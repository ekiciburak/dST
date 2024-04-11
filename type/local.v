
From DST Require Import sort.unscoped sort.sort.
Require Import String List Datatypes Lia.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Notation participant := string (only parsing).
Notation label       := string (only parsing).

Inductive local : Type :=
  | lt_var : fin -> local
  | lt_sel : ( participant   ) -> ( list (prod (label  ) (local )) ) -> local
  | lt_brn : ( participant   ) -> ( list (prod (label  ) (local )) ) -> local
  | lt_receive : forall (A: Type), ( participant   ) -> A -> ( local  ) -> local
  | lt_send : forall (A: Type), ( participant   ) -> A -> ( local ) -> local
  | lt_mu : ( local  ) -> local
  | lt_end : local.

(* Arguments lt_var {_} _.
Arguments lt_sel {_} _ _.
Arguments lt_brn {_} _ _. *)
Arguments lt_receive {_} _ _ _.
Arguments lt_send {_} _ _ _.
(* Arguments lt_mu {_} _.
Arguments lt_end {_}. *)

Section local.

Lemma congr_lt_sel { s0 : participant   } { s1 : list (prod (label  ) (local )) } { t0 : participant   } 
{ t1 : list (prod (label  ) (local)) } (H1 : s0 = t0) (H2 : s1 = t1) : lt_sel s0 s1 = lt_sel t0 t1 .
Proof. congruence. Qed.

Lemma congr_lt_brn { s0 : participant   } { s1 : list (prod (label  ) (local )) } { t0 : participant   }
{ t1 : list (prod (label  ) (local)) } (H1 : s0 = t0) (H2 : s1 = t1) : lt_brn s0 s1 = lt_brn t0 t1 .
Proof. congruence. Qed.

Lemma congr_lt_receive {A: Type} { s0 : participant   } { s1 : A   } { s2 : local  } { t0 : participant   } { t1 : A   }
 { t2 : local } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : lt_receive s0 s1 s2 = lt_receive t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_lt_send  {A: Type} { s0 : participant   } { s1 : A   } { s2 : local } { t0 : participant   } { t1 : A   } { t2 : local  } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : lt_send s0 s1 s2 = lt_send t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_lt_mu {A: Type} { s1 : local } { t1 : local  }(H2 : s1 = t1) : lt_mu s1 = lt_mu t1 .
Proof. congruence. Qed.

Lemma congr_lt_end {A: Type}:  lt_end = lt_end .
Proof. congruence. Qed.

Definition upRen_local_local   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_local  (xilocal : ( fin ) -> fin) (s : local ) : local :=
    match s return local with
    | lt_var s  => lt_var (xilocal s) 
    | lt_sel s0 s1 => lt_sel ((fun x => x) s0) ((list_map (prod_map (fun x => x) (ren_local xilocal))) s1)
    | lt_brn s0 s1 => lt_brn ((fun x => x) s0) ((list_map (prod_map (fun x => x) (ren_local xilocal))) s1)
    | lt_receive s0 s1 s2 => lt_receive ((fun x => x) s0) ((fun x => x) s1) ((ren_local xilocal) s2)
    | lt_send s0 s1 s2 => lt_send ((fun x => x) s0) ((fun x => x) s1) ((ren_local xilocal) s2)
    | lt_mu s1 => lt_mu ((ren_local (upRen_local_local xilocal)) s1)
    | lt_end  => lt_end
    end.

Definition up_local_local (sigma : ( fin ) -> local) : ( fin ) -> local :=
  (scons) (lt_var var_zero ) ((funcomp) (ren_local (shift)) sigma).

Fixpoint subst_local (sigmalocal : ( fin ) -> local) (s : local) : local  :=
    match s return local with
    | lt_var s            => sigmalocal s
    | lt_sel s0 s1        => lt_sel s0 ((list_map (prod_map (fun x => x) (@subst_local sigmalocal))) s1)
    | lt_brn s0 s1        => lt_brn s0 ((list_map (prod_map (fun x => x) (@subst_local sigmalocal))) s1)
    | lt_receive s0 s1 s2 => lt_receive s0 s1 ((@subst_local sigmalocal) s2)
    | lt_send s0 s1 s2    => lt_send s0 s1 ((@subst_local sigmalocal) s2)
    | lt_mu  s1           => lt_mu  ((@subst_local (@up_local_local sigmalocal)) s1)
    | lt_end              => lt_end 
    end.

Fixpoint unfold_local {A: Type} (b: A) (l: local): local :=
  match l with
    | lt_mu l0            => @subst_local (lt_mu (unfold_local b l0) .: (lt_var)) l0
    | lt_send s0 s1 s2    => lt_send s0 b (unfold_local b s2)
    | lt_receive s0 s1 s2 => lt_receive s0 b (unfold_local b s2)
    | lt_brn s0 s1        => lt_brn s0 (list_map (prod_map (fun x => x) (@unfold_local A b)) s1)
    | lt_sel s0 s1        => lt_sel s0 (list_map (prod_map (fun x => x) (@unfold_local A b)) s1)
    | _                   => l
  end.
 
End local.

