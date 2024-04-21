From DST Require Import sort.sort type.local processes.process.
Require Import String List Datatypes Lia.
Import ListNotations.
Local Open Scope string_scope.
From Paco Require Import paco.
From mathcomp Require Import seq.

Local Open Scope list_scope.

CoInductive st: Type :=
  | st_end    : st
  | st_receive: participant -> Type -> st -> st
  | st_send   : participant -> Type -> st -> st
  | st_brn    : participant -> list (label*st) -> st
  | st_sel    : participant -> list (label*st) -> st.

(* Arguments st_sel {_} _ _.
Arguments st_brn {_} _ _. *)
(* Arguments st_receive _ _ _.
Arguments st_send _ _ _. *)
(* Arguments st_end {_}.  *)

Definition st_id (s: st): st :=
  match s with
    | st_end           => st_end
    | st_receive p P c => st_receive p P c
    | st_send p P c    => st_send p P c
    | st_brn p l       => st_brn p l
    | st_sel p l       => st_sel p l
  end.

Lemma st_eq: forall s, s = st_id s.
Proof. intros s; destruct s; easy. Defined.

Inductive lt2st (R: local -> st -> Prop): local -> st -> Prop :=
  | lt2st_end: lt2st R lt_end st_end
  | lt2st_snd: forall (A: Type) p (s1: A) l t, 
               R l t ->
               lt2st R (@lt_send A p s1 l) (st_send p A t)
  | lt2st_rcv: forall (A: Type) p (s1: A) l t, 
               R l t ->
               lt2st R (@lt_receive A p s1 l) (st_receive p A t)
  | lt2st_brn: forall p l xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_brn p (zip l xs)) (st_brn p (zip l ys))
  | lt2st_sel: forall p l xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_sel p (zip l xs)) (st_sel p (zip l ys))
  | lt2st_mu : forall (A: Type) l t b,
               lt2st R (@unfold_local A b (lt_mu l)) t ->
               lt2st R (lt_mu l) t.

Definition lt2stC l t := paco2 (lt2st) bot2 l t.

Definition l1 (a: nat) := lt_mu (lt_send "p" a (lt_var 0)).

CoFixpoint s1 := st_send "p" nat s1.

Example l1s1: forall x, lt2stC (l1 x) s1.
Proof. pcofix CIH.
       intros x. pfold.
       unfold l1.
       setoid_rewrite(st_eq s1) at 1. simpl.
       specialize(@lt2st_mu 
                            (upaco2 lt2st r) fin
                            (@lt_send fin "p" x (lt_var  0))
                            (st_send "p" nat s1) 
                            (x + x)); intro HM.
       apply HM; clear HM.
       simpl.
       apply lt2st_snd.
       right.
       specialize(CIH (x+x)). unfold l1 in CIH.
       exact CIH.
Qed.

Lemma alln: forall (n: nat), n <> 0 -> { y: nat & y > 0 }.
Proof. intro n.
       exists n. lia.
Defined.

Definition lAlice (n: { y: nat & y > 0 }) (m: nat) :=
  lt_receive "Carol" n
  (lt_mu 
    (lt_send "Carol" (m+m)
      (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil)))
    )
  ).

CoFixpoint clAliceH: st :=
  st_send "Carol" nat (st_brn "Carol" (cons (pair "correct" st_end) (cons (pair "wrong" (clAliceH)) nil))).

Definition clAlice: st :=
  st_receive "Carol" ({ y: nat & y > 0 }) (clAliceH).

Example lclAlice: forall n m, lt2stC (lAlice n m) (clAlice).
Proof. intros (n, P) m.
       pfold. unfold clAlice, lAlice.
       apply lt2st_rcv.
       left. revert n P m. pcofix CIH.
       intros n P m. simpl.
       rewrite(st_eq (clAliceH)). simpl.
       pfold.
       specialize(lt2st_mu (upaco2 lt2st r) fin
                           (lt_send "Carol" (m+m) (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil))))
                           (st_send "Carol" fin (st_brn "Carol" (cons (pair "correct" st_end) (cons (pair "wrong" (clAliceH)) nil))))
                           (m+m)
       ); intro HM.
       apply HM; clear HM.
       simpl.
       apply lt2st_snd.
       left. pfold.
       specialize (lt2st_brn (upaco2 lt2st r) "Carol" 
                             (["correct"; "wrong"])
                             ([lt_end; (lt_mu (lt_send "Carol" (m+m)
                                              (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil)) )))])
                             ([st_end; (clAliceH)])
       ); intro HB. simpl in HB.
       apply HB; clear HB. easy.
       apply Forall_forall. intros (l,s).
       simpl.
       intro H. destruct H as [H | H].
       inversion H. subst. 
       left. pfold. constructor.
       destruct H as [H | H]. 
       inversion H. subst. right.
(*        assert(n+1 > 0) as Hsn.
       { lia. } *)
       specialize (CIH n P m). simpl in CIH.
       apply CIH.
       easy.
Qed.

Definition sigNT := { y: nat | if Nat.eqb y 0 then True else y > 0 }.

Definition lAlice1H (m: nat) :=
  (lt_mu 
    (lt_send "Carol" m
      (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil)))
    )
  ).

Definition lAlice1 (n: { y: nat | y > 0 }) (m: nat) := lt_receive "Carol" n (lAlice1H m).

CoFixpoint clAliceH1: st :=
  st_send "Carol" nat (st_brn "Carol" (cons (pair "correct" st_end) (cons (pair "wrong" (clAliceH1)) nil))). 

Definition clAlice1: st := st_receive "Carol" { y: nat | y > 0 } (clAliceH1).

Example lclAlice1: forall n m, lt2stC (lAlice1 n m) (clAlice1).
Proof. intros (n, P) m.
       pfold. unfold clAlice1, lAlice1. simpl.
       apply lt2st_rcv.
       unfold clAlice1, lAlice1H. simpl.
       left. revert n P m. pcofix CIH.
       intros n P m. simpl.
       pfold.
       rewrite(st_eq (clAliceH1)). simpl.
       specialize(lt2st_mu (upaco2 lt2st r) fin
                           (lt_send "Carol" m (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil))))
                           (st_send "Carol" fin (st_brn "Carol" (cons (pair "correct" st_end) (cons (pair "wrong" (clAliceH1)) nil))))
                           (m + m)
       ); intro HM.
       apply HM; clear HM.
       simpl.
       apply lt2st_snd.
       left. pfold.
       specialize (lt2st_brn (upaco2 lt2st r) "Carol" 
                             (["correct"; "wrong"])
                             ([lt_end; (lt_mu (lt_send "Carol" (m + m)
                                              (lt_brn "Carol" (cons (pair "correct" lt_end) (cons (pair "wrong" (lt_var 0)) nil)) )))])
                             ([st_end; (clAliceH1)])
       ); intro HB. simpl in HB.
       apply HB; clear HB. easy.
       apply Forall_forall. intros (l,s).
       simpl.
       intro H. destruct H as [H | H].
       inversion H. subst. 
       left. pfold. constructor.
       destruct H as [H | H]. 
       inversion H. subst. right.
       specialize (CIH n P (m+m)). simpl in CIH.
       apply CIH.
       easy.
Qed.

(*
Inductive subType: Type -> Type -> Prop :=
  | dep1: forall A B, subType A B -> subType ({y : A & (A + B)%type }) (forall (y: A), B). 
*)

