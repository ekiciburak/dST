From RDST Require Import type.unscoped type.local.
Require Import String List Datatypes Lia Relations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.

(* Fixpoint compute_plus (e1 e2: local): option local :=
  match (e1, e2) with
    | (ltzero, ltzero)       => Some ltzero
    | (ltsucc k1, ltsucc k2) => let s := (compute_plus k1 k2) in
                                match s with
                                  | Some ss => Some (ltsucc (ltsucc ss))
                                  | _       => None
                                end
    | (ltsucc k1, ltzero)    => Some e1
    | (ltzero, ltsucc k2)    => Some e2
    | _                      => None
  end.

(* Eval compute in compute_plus (ltsend "p" "l" ltnat ltend) (ltnval 1). *)

Definition complus (e: local): local :=
  match e with
    | ltadd e1 e2 =>
    let fix next e1 e2 :=
      match (e1, e2) with
        | (ltzero, ltzero)       => ltzero
        | (ltsucc k1, ltsucc k2) => (ltsucc (ltsucc (next k1 k2)))
        | (ltsucc k1, ltzero)    => e1
        | (ltzero, ltsucc k2)    => e2
        | _                      => e
      end
    in next e1 e2
    | _           => e
  end. *)

(* Eval compute in complus (ltadd  (ltnval 1) (ltnval 1)). *)

Fixpoint betaP (s: local): local :=
  match s with
    | ltapp (ltlambda e1 e2) e3    => subst_local (e3 .: ltvar) e2
    | ltlambda e1 e2               => ltlambda (betaP e1) (betaP e2)
    | ltapp (ltpi e1 e2) e3        => subst_local (e3 .: ltvar) e2
    | ltpi e1 e2                   => ltpi (betaP e1) (betaP e2)
    | ltsig e1 e2                  => ltsig (betaP e1) (betaP e2)
    | ltite (ltbval true) e1 e2    => e1
    | ltite (ltbval false) e1 e2   => e2
(*     | ltadd e1 e2                 => complus s *)
    | _                            => s
  end.

Fixpoint retRecPath (l: label) (xs: list(label*local*local)): option local :=
  match xs with
    | nil             => None
    | (lbl,t,c) :: ys => if eqb l lbl then Some c else retRecPath l ys
  end.

Inductive lqueue (p: participant): Type := 
  | lnil : lqueue p
  | lcons: participant -> label -> local -> lqueue p -> lqueue p.

Arguments lnil {_}.
Arguments lcons {_} _ _ _.

Fixpoint lconq {p: participant} (m1 m2: lqueue p): lqueue p :=
  match m1 with
    | lnil           => m2
    | lcons q l c qu => lcons q l c (lconq qu m2)
  end.

Inductive gqueue: Type :=
  | gnil : gqueue
  | gcons: forall p, lqueue p -> gqueue -> gqueue.

Fixpoint genq (p: participant) (q: participant) (l: label) (t: local) (m: gqueue) : gqueue :=
  match m with
    | gnil           => gcons p (lcons q l t lnil) gnil
    | gcons p1 i1 m1 => if eqb p p1 then gcons p1 (lcons q l t i1) m1 else gcons p1 i1 (genq p q l t m1)
  end.

Definition isNil {p: participant} (l: lqueue p) :=
  match l with
    | lnil => true
    | _    => false
  end.

Fixpoint gdeq (p: participant) (k: participant) (m: gqueue): option (participant*label*local)*gqueue :=
  match m with
    | gnil         => (None,m)
    | gcons q i m1 => if eqb p q then 
                        let fix next k i :=
                          match i with
                           | lnil           => (None,i)
                           | lcons r l c i1 => if (eqb r k) then (Some (r,l,c), i1)
  (*                                              else if isNil i1 then (None, i1)  *)
                                               else ((fst (next k i1)), lcons r l c (snd (next k i1)))
                          end
                          in (let out := (next k i) in (fst out, gcons q (snd out) m1))
                      else 
                        let out := (gdeq p k m1) in (fst out, gcons q i (snd out))
  end.

Class process: Type :=
  mkproc
  {
    body : local;
    queue: gqueue
  }.

Fixpoint incn (u: local): local :=
  match u with
    | ltmu P t       => ltmu (incn P) t
    | ltlambda e1 e2 => ltlambda (incn e1) (incn e2)
    | ltapp e1 e2    => ltapp (incn e1) (incn e2)
    | ltsubtr e1 e2  => ltsubtr (incn e1) (incn e2)
    | ltadd e1 e2    => ltadd (incn e1) (incn e2)
    | ltmult e1 e2   => ltmult (incn e1) (incn e2)
    | ltgt e1 e2     => ltgt (incn e1) (incn e2)
    | ltvar 0        => ltvar 0
    | ltvar (S k)    => ltvar (S (S k))
    | ltite e1 e2 e3 => ltite (incn e1) (incn e2) (incn e3)
    | _              => u
  end.

Fixpoint betaL (u: local): local :=
  match u with
    | ltapp (ltlambda e1 e2) e3 => (subst_local (e3 .: ltvar) e2) 
(*     | ltapp (ltmu e1 e2) e3     => (subst_local (e3 .: ltvar) ((ltmu e1 e2)))  *)
    | ltapp (ltpi e1 e2) e3     => (subst_local (e3 .: ltvar) e2)
    | ltite (ltbval true) e1 e2 => e1
    | ltite (ltbval false) e1 e2=> e2 
(*     | ltadd e1 e2              => (complus (ltadd e1 e2)) *)
    | ltmu P t as f             => incn (subst_local (f .: ltvar) P)
    | ltlambda e1 e2            => ltlambda (betaL e1) (betaL e2)
    | ltadd e1 e2               => match (e1,e2) with
                                     | (ltnval n, ltnval m) => ltnval (n+m)
                                     | _                    => ltadd (betaL e1) (betaL e2) 
                                   end
    | ltmult e1 e2              => match (e1,e2) with
                                     | (ltnval n, ltnval m) => ltnval (n*m)
                                     | _                    => ltmult (betaL e1) (betaL e2) 
                                   end
    | ltsubtr e1 e2             =>  match (e1,e2) with
                                     | (ltnval n, ltnval m) => ltnval (n-m)
                                     | _                    => ltsubtr (betaL e1) (betaL e2) 
                                   end
    | ltgt e1 e2                => match (e1,e2) with
                                     | (ltnval n, ltnval m) => ltbval (Nat.ltb m n)
                                     | _                    => ltgt (betaL e1) (betaL e2) 
                                   end
    | ltite e1 e2 e3            => match e1 with
                                     | ltbval true  => e2
                                     | ltbval false => e3
                                     | _            => ltite (betaL e1) e2 e3 
                                   end
    | ltapp e1 e2              => ltapp (betaL e1) (betaL e2)
    | _                        => u
  end.

Definition beta (k: participant) (u: process): process :=
  match @body u with
   | ltsend p l e C             => mkproc C (genq k p l e (@queue u))
   | ltreceive p xs             => let m := gdeq p k (@queue u) in
                                    match m with
                                      | (Some (i1,i2,i3),m') => 
                                        let t := retRecPath i2 xs in
                                        match t with
                                          | Some t' => (mkproc (subst_local (i3 .: ltvar) t') m')
                                          | None    => u
                                        end
                                      | (None,_)             => u
                                    end
    | ltbranch p xs             => let m := gdeq p k (@queue u) in
                                    match m with
                                      | (Some (i1,i2,i3),m') => 
                                        let t := retRecPath i2 xs in
                                        match t with
                                          | Some t' => (mkproc (subst_local (i3 .: ltvar) t') m')
                                          | None    => u
                                        end
                                      | (None,_)             => u
                                    end
    | ltselect p l e C          => (mkproc C (genq k p l e (@queue u)))
(*     | ltmu (ltlambda e1 e2) t as f => (mkproc (betaL (@body u)) (@queue u)) *)
    | ltmu P t as f             => (mkproc (subst_local (f .: ltvar) P) (@queue u))
    | ltapp (ltlambda e1 e2) e3 => (mkproc (subst_local (e3 .: ltvar) e2) (@queue u))
    | ltapp (ltpi e1 e2) e3     => (mkproc (subst_local (e3 .: ltvar) e2) (@queue u))
    | ltapp e1 e2 as f          => (mkproc (betaL f) (@queue u))
    | ltlambda e1 e2 as f       => (mkproc (betaL f) (@queue u))
    | ltite (ltbval true) e1 e2 => (mkproc e1 (@queue u))
    | ltite (ltbval false) e1 e2=> (mkproc e2 (@queue u))
    | ltite e1 e2 e3 as f       => (mkproc (betaL f) (@queue u))
(*     | ltadd e1 e2              => (mkproc (complus (ltadd e1 e2)) (@queue u)) *)
    | ltadd e1 e2 as f          => (mkproc (betaL f) (@queue u))
    | ltmult e1 e2 as f         => (mkproc (betaL f) (@queue u))
    | ltgt e1 e2 as f           => (mkproc (betaL f) (@queue u))
    | ltsubtr e1 e2 as f        => (mkproc (betaL f) (@queue u))
    | _                         => u
  end.

Definition isVal (s: process): bool :=
  match (@body s) with
    | ltlambda e1 e2 => true
    | ltpi e1 e2     => true
    | ltstar         => true
(*     | ltsucc n       => true
    | ltzero         => true *)
    | _              => false
  end.

Fixpoint betan (n: nat) (p: participant) (s: process): process :=
  match n with
    | O   => s
    | S k => (* if isVal s then s else  *) betan k p (beta p s) 
  end.

Fixpoint betanList (n: nat) (p: participant) (l: list process): list process :=
  match l with
    | []    => []
    | x::xs => betan n p x :: betanList n p xs
  end.

Definition betanL (n: nat) (p: participant) (s: process): process :=
  let fix next n b :=
    match n with
      | O   => b
      | S k => next k (betaL b) 
    end
  in mkproc (next n (@body s)) (@queue s).

Fixpoint mkprocL (l: list local): list process :=
  match l with
    | []    => []
    | x::xs => mkproc x gnil :: mkprocL xs
  end.

Fixpoint mklocalL (l: list process): list local :=
  match l with
    | []    => []
    | x::xs => @body x :: mklocalL xs
  end.

Inductive session: Type :=
  | sind: participant -> process -> session
  | spar: session     -> session -> session.

Notation "p '<--' P | h" :=  (sind p (mkproc P h)) (at level 50, no associativity).
Notation "s1 '|||' s2"   :=  (spar s1 s2) (at level 50, no associativity): type_scope.

Class sessionA: Type :=
 mksession
 {
   und   : session;
   squeue: gqueue
 }.

Fixpoint agqueue (m1 m2: gqueue): gqueue :=
  match m1 with
    | gnil => m2
    | gcons p i m => gcons p i (agqueue m m2)
  end.

Inductive betaS: relation sessionA :=
  | r_send   : forall p q l p1 c lq gq M, let e1 := (beta p (mkproc (ltsend q l p1 c) lq)) in
                                          betaS (mksession ((p <-- (ltsend q l p1 c) | lq) ||| M) gq)
                                                (mksession ((p <-- (@body e1) | (@queue e1)) ||| M) (agqueue (@queue e1) gq))
  | r_receive: forall p k xs gq lq M, let m := gdeq k p gq in
                                      let e1 := (beta p (mkproc (ltreceive k xs) gq)) in
                                      betaS (mksession ((p <-- (ltreceive k xs) | lq) ||| M) gq)
                                            (mksession ((p <-- (@body e1) | lq) ||| M) (snd m))
  | r_rest   : forall p p1 lq gq M, let e := (beta p (mkproc p1 lq)) in
                                    betaS (mksession ((p <-- p1 | lq) ||| M) gq)
                                          (mksession ((p <-- (@body e) | lq) ||| M) gq).

Definition PAlice: local := 
  (ltsend "Bob" "l1" (ltnval 0) (ltreceive "Carol" [("l3",ltnat,ltend)])).

Definition PBob: local :=
   (ltreceive "Alice" [("l1",ltnat,(ltsend "Carol" "l2" (ltnval 1) ltend));
                       ("l4",ltnat,(ltsend "Carol" "l2" (ltnval 2) ltend))
                      ]).

Definition PCarol: local :=
 (ltreceive "Bob" [("l2",ltnat,(ltsend "Alice" "l3" (ltadd (ltvar 0) (ltnval 1)) ltend))]).


Definition MS: sessionA := mksession (("Alice" <-- PAlice | gnil) ||| ("Bob" <-- PBob | gnil) ||| ("Carol" <-- PCarol | gnil)) gnil.

Definition MS': sessionA := mksession (("Alice" <-- ltend | (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)) 
                                   ||| ("Bob"   <-- ltend | (gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil)) 
                                   ||| ("Carol" <-- ltend | (gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil) gnil)))
                                   (gcons "Carol" lnil (gcons "Bob" lnil (gcons "Alice" lnil gnil))).

Inductive pcong: relation local :=
  | pmuUnf: forall e p, pcong (ltmu e p) (subst_local ((ltmu e p) .: (ltvar)) p).

Inductive lqcong {p: participant}: relation (lqueue p) :=
  | qcons : forall q1 q2 l1 l2 v1 v2 h1 h2, q1 <> q2 -> 
                                            lqcong (lconq h1 (lconq (lcons q1 l1 v1 lnil) (lconq (lcons q2 l2 v2 lnil) h2)))
                                                   (lconq h1 (lconq (lcons q2 l2 v2 lnil) (lconq (lcons q1 l1 v1 lnil) h2))).

Inductive scongA: relation sessionA :=
  | srecA   : forall p P e hp h M, scongA (mksession ((p <-- (ltmu P e) | hp) ||| M) h) (mksession ((p <-- (subst_local ((ltmu P e) .: ltvar) P) | hp) ||| M) h)
  | sannA   : forall p M h, scongA (mksession ((p <--  ltend | gnil) ||| M) h) (mksession M h)
  | scommA  : forall M1 M2 h, scongA (mksession (M1 ||| M2) h) (mksession (M2 ||| M1) h)
  | sassocA : forall M1 M2 M3 h, scongA (mksession (M1 ||| M2 ||| M3) h) (mksession (M1 ||| (M2 ||| M3)) h)
(*   | sassoc2: forall M1 M2 M3, scong (M1 ||| M2 ||| M3) ((M1 ||| M2) ||| M3) *)
  | sassoc2A: forall M1 M2 M3 h, scongA (mksession (M1 ||| M2 ||| M3) h) (mksession (M1 ||| (M3 ||| M2)) h).

Inductive scong: relation session :=
  | sann   : forall p M, scong ((p <--  ltend | gnil) ||| M) M
  | scomm  : forall M1 M2, scong (M1 ||| M2) (M2 ||| M1)
  | sassoc : forall M1 M2 M3, scong (M1 ||| M2 ||| M3) (M1 ||| (M2 ||| M3))
(*   | sassoc2: forall M1 M2 M3, scong (M1 ||| M2 ||| M3) ((M1 ||| M2) ||| M3) *)
  | sassoc2: forall M1 M2 M3, scong (M1 ||| M2 ||| M3) (M1 ||| (M3 ||| M2)).
(*   | scongl : forall p P Q h1 h2 M, pcong P Q -> lqcong h1 h2 -> 
                                   scong ((p <-- (mkproc P h1)) ||| M) ((p <-- (mkproc Q h2)) ||| M). *)

Declare Instance Equivalence_beta : Equivalence betaS.
Declare Instance Equivalence_scong : Equivalence scong.
Declare Instance Equivalence_scongA : Equivalence scongA.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition betaS_multistep := multi betaS.

#[global] Declare Instance RW_scong2: Proper (scongA ==> scong) (@und).

#[global] Declare Instance RW_scong3: Proper (scongA ==> scongA ==> impl) betaS.
#[global] Declare Instance RW_scong4: Proper (scongA ==> scongA ==> impl) betaS_multistep.

Example redMS: betaS_multistep MS MS'.
Proof. intros.
       unfold betaS_multistep, MS, MS', PAlice.

       (* Eval compute in (beta "Alice" 
                                (mkproc (ltsend "Bob" "l1" (ltnval 0) (ltreceive "Carol" [("l3", ltnat, ltend)]))
                                gnil)). *)

       (* Eval compute in (beta "Bob" 
                              (mkproc (ltreceive "Alice" [("l1", ltnat, ltsend "Carol" "l2" (ltnval 1) ltend);
                                                          ("l4", ltnat, ltsend "Carol" "l2" (ltnval 2) ltend)])
                               gnil)). *)

       apply multi_step with
       (y :=  mksession ((("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | ( gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil))
                      ||| ("Bob" <-- PBob | gnil))
                      ||| ("Carol" <-- PCarol | gnil)) (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)).
       specialize(r_send "Alice" "Bob" "l1" 
                         (ltnval 0)
                         (ltreceive "Carol" [("l3", ltnat, ltend)])
                         gnil
                         gnil
                         (("Bob" <-- PBob | gnil) ||| ("Carol" <-- PCarol | gnil))
       ); intro HS.
       simpl in HS.
       setoid_rewrite sassocA.
       apply HS.

       setoid_rewrite sassocA.
       setoid_rewrite scommA.
       unfold PBob.

       (* Eval compute in  (beta "Bob"
                              (mkproc (ltreceive "Alice" [("l1", ltnat, ltsend "Carol" "l2" (ltnval 1) ltend);
                                                          ("l4", ltnat, ltsend "Carol" "l2" (ltnval 2) ltend)])
                              (gcons "Alice" (lcons "Bob" "l1" ltzero lnil) gnil))). *)

       apply multi_step with
       (y := mksession ((("Bob" <-- ltsend "Carol" "l2" (ltnval 1) ltend | gnil)
              ||| ("Carol" <-- PCarol | gnil))
              ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil))) (gcons "Alice" lnil gnil) ).

       specialize(r_receive "Bob" "Alice"
                            ([("l1", ltnat, ltsend "Carol" "l2" (ltnval 1) ltend);
                             ("l4", ltnat, ltsend "Carol" "l2" (ltnval 2) ltend)])
                            (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)
                            gnil
                            (("Carol" <-- PCarol | gnil) ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)))
       ); intros HR; simpl in HR.
       setoid_rewrite sassocA.
       apply HR.

       unfold PCarol.

       (* Eval compute in (beta "Bob"
                                (mkproc (ltsend "Carol" "l2" (ltnval 1) ltend) 
                                gnil)). *)

       apply multi_step with
       (y := mksession ((("Bob" <-- ltend | (gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil))
              ||| ("Carol" <-- ltreceive "Bob" [("l2", ltnat, ltsend "Alice" "l3" (ltadd (ltvar 0) (ltnval 1)) ltend)] | gnil))
              ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)) 
               (gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) (gcons "Alice" lnil gnil)) ).

       specialize(r_send "Bob" "Carol" "l2"
                         (ltnval 1)
                         ltend
                         gnil
                         (gcons "Alice" lnil gnil)
                         (("Carol" <-- ltreceive "Bob" [("l2", ltnat, ltsend "Alice" "l3" (ltadd (ltvar 0) (ltnval 1)) ltend)] | gnil)
                          ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil))
       ); intro HR; simpl in HR.
        setoid_rewrite sassocA.
        apply HR.

       setoid_rewrite sassocA.
       setoid_rewrite scommA.
       setoid_rewrite sassoc2A.


       (* Eval compute in (beta "Carol"
                                (mkproc (ltreceive "Bob" [("l2", ltnat, ltsend "Alice" "l3" (ltadd (ltvar 1) (ltnval 1)) ltend)]) 
                                (gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) (gcons "Alice" lnil gnil)))). *)

       apply multi_step with
       (y := mksession ((("Carol" <-- ltsend "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) ltend | gnil)
              ||| ("Bob" <-- ltend | gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil))
              ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)) 
               (gcons "Bob" lnil (gcons "Alice" lnil gnil)) ).
       specialize(r_receive "Carol" "Bob"
                            ([("l2", ltnat, ltsend "Alice" "l3" (ltadd (ltvar 0) (ltnval 1)) ltend)])
                            (gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) (gcons "Alice" lnil gnil))
                            gnil
       ); intro HR; simpl in HR.
       setoid_rewrite sassocA.
       apply HR.

       (*  Eval compute in (beta "Carol" 
                                 (mkproc (ltsend "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) ltend)  
                                 (gnil))). *)

       setoid_rewrite sassoc2A.

       apply multi_step with
       (y := mksession ((("Carol" <-- ltend | (gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil) gnil))
              ||| ("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil))
              ||| ("Bob" <-- ltend | gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil)) 
               (gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil) (gcons "Bob" lnil (gcons "Alice" lnil gnil))) ).

       specialize(r_send "Carol" "Alice" "l3"
                         (ltadd (ltnval 1) (ltnval 1))
                         ltend
                         gnil
                         (gcons "Bob" lnil (gcons "Alice" lnil gnil))
                         ((("Alice" <-- ltreceive "Carol" [("l3", ltnat, ltend)] | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)
                          ||| ("Bob" <-- ltend | gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil)))
       ); intro HS; simpl in HS.
       setoid_rewrite sassocA.
       apply HS.

       setoid_rewrite sassocA.
       setoid_rewrite scommA.
       setoid_rewrite sassoc2A.

       (* Eval compute in (beta "Alice" 
                                (mkproc (ltreceive "Carol" [("l3", ltnat, ltend)])
                                (gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil) (gcons "Bob" lnil (gcons "Alice" lnil gnil))))). *)

       apply multi_step with
       (y := mksession ((("Alice" <-- ltend | gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)
              ||| ("Carol" <-- ltend | gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil) gnil))
              ||| ("Bob" <-- ltend | gcons "Bob" (lcons "Carol" "l2" (ltnval 1) lnil) gnil)) 
               (gcons "Carol" lnil (gcons "Bob" lnil (gcons "Alice" lnil gnil))) ).
       specialize(r_receive "Alice" "Carol"
                            ([("l3", ltnat, ltend)])
                            (gcons "Carol" (lcons "Alice" "l3" (ltadd (ltnval 1) (ltnval 1)) lnil)
                              (gcons "Bob" lnil (gcons "Alice" lnil gnil)))
                            (gcons "Alice" (lcons "Bob" "l1" (ltnval 0) lnil) gnil)
       ); intro HR; simpl in HR.
       setoid_rewrite sassocA.
       apply HR.

       setoid_rewrite sassocA.
       setoid_rewrite scommA.
       setoid_rewrite sassoc2A at 2.
       setoid_rewrite sassocA.

       apply multi_refl.
Qed.

(* factorial example *)

Definition fact: local :=
  ltmu(
    ltlambda ltnat (ltite 
                    (ltgt (ltvar 1) (ltnval 1)) 
                    (ltmult (ltvar 1) (ltapp (ltvar 0) (ltsubtr (ltvar 1) (ltnval 1)))) 
                    (ltnval 1)
                   )
      ) (ltpi ltnat ltnat).

Definition factorial  (n: nat): local   := ltapp fact (ltnval n).
Definition pfactorial (n: nat): process := mkproc (factorial n) gnil.

Eval compute in (betan 34 "p" (pfactorial 7)).






