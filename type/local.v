From RDST Require Import type.unscoped.
Require Import String List Datatypes Lia.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Notation participant := string (only parsing).
Notation label := string (only parsing).

Section local.
Inductive local  : Type :=
  | ltvar : ( fin ) -> local 
  | ltnval: fin -> local
  | ltbval: bool -> local
  | ltinact: local
  | ltend : local 
  | ltsend : ( participant   ) -> ( label   ) -> ( local   ) -> ( local   ) -> local 
  | ltreceive : ( participant   ) -> ( list (label*local*local) ) -> local 
(*   | ltselect : ( participant   ) -> ( list (label*local*local) ) -> local  *)
  | ltselect : ( participant   ) -> label -> local -> local -> local 
  | ltbranch : ( participant   ) -> ( list (label*local*local) ) -> local 
  | ltmu : ( local   ) -> ( local   ) -> local 
  | ltpi : ( local   ) -> ( local   ) -> local 
  | ltlambda : ( local   ) -> ( local   ) -> local 
  | ltapp: local -> local -> local
  | ltgt: local -> local -> local
  | ltsig : ( local   ) -> ( local   ) -> local 
  | ltite : ( local   ) -> ( local   ) -> ( local   ) -> local 
  | ltpair : ( local   ) -> ( local   ) -> local 
(*| ltzero : local 
  | ltsucc : ( local   ) -> local
  | ltplus: local -> local -> local 
  | ltfalse : local 
  | lttrue : local 
*)
  | ltnat : local 
  | ltadd : local -> local -> local
  | ltmult : local -> local -> local
  | ltsubtr : local -> local -> local
  | ltbool : local 
  | ltstar : local .

Lemma congr_ltend  : ltend  = ltend  .
Proof. congruence. Qed.

Lemma congr_ltinact  : ltinact  = ltinact.
Proof. congruence. Qed.


Lemma congr_ltsend  { s0 : participant   } { s1 : label   } { s2 : local   } { s3 : local   } { t0 : participant   } { t1 : label   } { t2 : local   } { t3 : local   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : ltsend  s0 s1 s2 s3 = ltsend  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ltreceive  { s0 : participant   } { s1 : list (prod (prod (label  ) (local  )) (local  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (local  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : ltreceive  s0 s1 = ltreceive  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltselect { s0 : participant   } { s1 : label   } { s2 : local   } { s3 : local   } { t0 : participant   } { t1 : label   } { t2 : local   } { t3 : local   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) :
  ltselect  s0 s1 s2 s3 = ltselect  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ltbranch  { s0 : participant   } { s1 : list (prod (prod (label  ) (local  )) (local  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (local  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : ltbranch  s0 s1 = ltbranch  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltmu  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltmu  s0 s1 = ltmu  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltpi  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltpi  s0 s1 = ltpi  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltlambda  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltlambda  s0 s1 = ltlambda  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltsig  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltsig  s0 s1 = ltsig  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltite  { s0 : local   } { s1 : local   } { s2 : local   } { t0 : local   } { t1 : local   } { t2 : local   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ltite  s0 s1 s2 = ltite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ltpair  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltpair  s0 s1 = ltpair  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltapp  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltapp  s0 s1 = ltapp  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltgt  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltgt  s0 s1 = ltgt  t0 t1 .
Proof. congruence. Qed.

(* Lemma congr_ltzero  : ltzero  = ltzero  .
Proof. congruence. Qed.

Lemma congr_ltsucc  { s0 : local   } { t0 : local   } (H1 : s0 = t0) : ltsucc  s0 = ltsucc  t0 .
Proof. congruence. Qed. *)

Lemma congr_ltnval  { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : ltnval s0 = ltnval t0 .
Proof. congruence. Qed.

Lemma congr_ltbval  { s0 : bool} { t0 : bool   } (H1 : s0 = t0) : ltbval s0 = ltbval t0 .
Proof. congruence. Qed.

Lemma congr_ltadd  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltadd  s0 s1 = ltadd  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltmult { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltmult  s0 s1 = ltmult  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ltsubtr  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltsubtr  s0 s1 = ltsubtr  t0 t1 .
Proof. congruence. Qed.

(* Lemma congr_ltplus  { s0 : local   } { s1 : local   } { t0 : local   } { t1 : local   } (H1 : s0 = t0) (H2 : s1 = t1) : ltplus  s0 s1 = ltplus  t0 t1 .
Proof. congruence. Qed. *)

(* Lemma congr_ltfalse  : ltfalse  = ltfalse  .
Proof. congruence. Qed.

Lemma congr_lttrue  : lttrue  = lttrue  .
Proof. congruence. Qed. *)

Lemma congr_ltnat  : ltnat  = ltnat  .
Proof. congruence. Qed.

Lemma congr_ltbool  : ltbool  = ltbool  .
Proof. congruence. Qed.

Lemma congr_ltstar  : ltstar  = ltstar  .
Proof. congruence. Qed.

Definition upRen_local_local   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_local   (xilocal : ( fin ) -> fin) (s : local ) : local  :=
    match s return local  with
    | ltvar  s => (ltvar ) (xilocal s)
    | ltend   => ltend 
    | ltinact   => ltinact 
    | ltsend  s0 s1 s2 s3 => ltsend  ((fun x => x) s0) ((fun x => x) s1) ((ren_local xilocal) s2) ((ren_local xilocal) s3)
    | ltreceive  s0 s1 => ltreceive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (ren_local (upRen_local_local xilocal)) ) (ren_local xilocal))) s1)
    | ltselect  s0 s1 s2 s3 => ltselect  ((fun x => x) s0) ((fun x => x) s1) ((ren_local xilocal) s2) ((ren_local xilocal) s3)
(*     | ltselect  s0 s1 => ltselect  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (ren_local xilocal)) (ren_local xilocal))) s1) *)
    | ltbranch  s0 s1 => ltbranch  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (ren_local (upRen_local_local xilocal)) ) (ren_local xilocal))) s1)
    | ltmu  s0 s1 => ltmu  ((ren_local (upRen_local_local xilocal)) s0) ((ren_local xilocal) s1)
    | ltpi  s0 s1 => ltpi  ((ren_local (upRen_local_local xilocal)) s0) ((ren_local xilocal) s1)
    | ltlambda  s0 s1 => ltlambda  ((ren_local (upRen_local_local xilocal)) s0) ((ren_local xilocal) s1)
    | ltsig  s0 s1 => ltsig  ((ren_local (upRen_local_local xilocal)) s0) ((ren_local xilocal) s1)
    | ltite  s0 s1 s2 => ltite  ((ren_local xilocal) s0) ((ren_local xilocal) s1) ((ren_local xilocal) s2)
    | ltapp  s0 s1 => ltapp  ((ren_local xilocal) s0) ((ren_local xilocal) s1)
    | ltgt  s0 s1 => ltgt ((ren_local xilocal) s0) ((ren_local xilocal) s1)
    | ltpair  s0 s1 => ltpair  ((ren_local xilocal) s0) ((ren_local xilocal) s1)
(*     | ltzero   => ltzero 
    | ltsucc  s0 => ltsucc  ((ren_local xilocal) s0)
    | ltplus  s0 s1 => ltplus  ((ren_local xilocal) s0) ((ren_local xilocal) s1) *)
    | ltadd  s0 s1 => ltadd  ((ren_local xilocal) s0) ((ren_local xilocal) s1)
    | ltmult  s0 s1 => ltmult  ((ren_local xilocal) s0) ((ren_local xilocal) s1)
    | ltsubtr  s0 s1 => ltsubtr  ((ren_local xilocal) s0) ((ren_local xilocal) s1)
(*     | ltfalse   => ltfalse 
    | lttrue   => lttrue  *)
    | ltnat   => ltnat 
    | ltbool   => ltbool 
    | ltstar   => ltstar 
    | ltnval n => ltnval n
    | ltbval b => ltbval b
    end.

Definition up_local_local   (sigma : ( fin ) -> local ) : ( fin ) -> local  :=
  (scons) ((ltvar ) (var_zero)) ((funcomp) (ren_local (shift)) sigma).

Fixpoint subst_local (sigmalocal : ( fin ) -> local ) (s : local ) : local  :=
    match s return local  with
    | ltvar  s => sigmalocal s
    | ltend   => ltend
    | ltinact   => ltinact 
    | ltsend  s0 s1 s2 s3 => ltsend  ((fun x => x) s0) ((fun x => x) s1) ((subst_local sigmalocal) s2) ((subst_local sigmalocal) s3)
    | ltreceive  s0 s1 => ltreceive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (subst_local (up_local_local sigmalocal))) (subst_local sigmalocal))) s1)
(*     | ltselect  s0 s1 => ltselect  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (subst_local sigmalocal)) (subst_local sigmalocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => ltselect  ((fun x => x) s0) ((fun x => x) s1) ((subst_local sigmalocal) s2) ((subst_local sigmalocal) s3)
    | ltbranch  s0 s1 => ltbranch  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (subst_local (up_local_local sigmalocal))) (subst_local sigmalocal))) s1)
    | ltmu  s0 s1 => ltmu  ((subst_local (up_local_local sigmalocal)) s0) ((subst_local sigmalocal) s1)
    | ltpi  s0 s1 => ltpi  ((subst_local (up_local_local sigmalocal)) s0) ((subst_local sigmalocal) s1)
    | ltlambda  s0 s1 => ltlambda  ((subst_local (up_local_local sigmalocal)) s0) ((subst_local sigmalocal) s1)
    | ltsig  s0 s1 => ltsig  ((subst_local (up_local_local sigmalocal)) s0) ((subst_local sigmalocal) s1)
    | ltite  s0 s1 s2 => ltite  ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1) ((subst_local sigmalocal) s2)
    | ltapp  s0 s1 => ltapp ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
    | ltgt  s0 s1 => ltgt ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
    | ltpair  s0 s1 => ltpair  ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
(*     | ltzero   => ltzero 
    | ltsucc  s0 => ltsucc  ((subst_local sigmalocal) s0)
    | ltplus  s0 s1 => ltplus ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1) *)
    | ltadd  s0 s1 => ltadd ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
    | ltmult  s0 s1 => ltmult ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
    | ltsubtr  s0 s1 => ltsubtr ((subst_local sigmalocal) s0) ((subst_local sigmalocal) s1)
(*     | ltfalse   => ltfalse 
    | lttrue   => lttrue  *)
    | ltnat   => ltnat 
    | ltbool   => ltbool 
    | ltstar   => ltstar 
    | ltnval n => ltnval n
    | ltbval b => ltbval b
    end.

Definition upId_local_local  (sigma : ( fin ) -> local ) (Eq : forall x, sigma x = (ltvar ) x) : forall x, (up_local_local sigma) x = (ltvar ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_local  (sigmalocal : ( fin ) -> local ) (Eqlocal : forall x, sigmalocal x = (ltvar ) x) (s : local ) : subst_local sigmalocal s = s :=
    match s return subst_local sigmalocal s = s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend 
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((idSubst_local sigmalocal Eqlocal) s2) ((idSubst_local sigmalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal))) (idSubst_local sigmalocal Eqlocal))) s1)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((idSubst_local sigmalocal Eqlocal) s2) ((idSubst_local sigmalocal Eqlocal) s3)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (idSubst_local sigmalocal Eqlocal)) (idSubst_local sigmalocal Eqlocal))) s1) *)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal))) (idSubst_local sigmalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1) ((idSubst_local sigmalocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((idSubst_local sigmalocal Eqlocal) s0)
    | ltplus  s0 s1 => congr_ltplus ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1) *)
    | ltadd s0 s1 => congr_ltadd ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltmult s0 s1 => congr_ltmult ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
    | ltsubtr s0 s1 => congr_ltsubtr ((idSubst_local sigmalocal Eqlocal) s0) ((idSubst_local sigmalocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition upExtRen_local_local   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_local_local xi) x = (upRen_local_local zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_local   (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (Eqlocal : forall x, xilocal x = zetalocal x) (s : local ) : ren_local xilocal s = ren_local zetalocal s :=
    match s return ren_local xilocal s = ren_local zetalocal s with
    | ltvar  s => (ap) (ltvar ) (Eqlocal s)
    | ltend   => congr_ltend 
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((extRen_local xilocal zetalocal Eqlocal) s2) ((extRen_local xilocal zetalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) ) (extRen_local xilocal zetalocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (extRen_local xilocal zetalocal Eqlocal)) (extRen_local xilocal zetalocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((extRen_local xilocal zetalocal Eqlocal) s2) ((extRen_local xilocal zetalocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) ) (extRen_local xilocal zetalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1) ((extRen_local xilocal zetalocal Eqlocal) s2)
    | ltapp s0 s1 => congr_ltapp ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltgt s0 s1 => congr_ltgt ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((extRen_local xilocal zetalocal Eqlocal) s0)
    | ltplus s0 s1 => congr_ltplus ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1) *)
    | ltadd s0 s1 => congr_ltadd ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltmult s0 s1 => congr_ltmult ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
    | ltsubtr s0 s1 => congr_ltsubtr ((extRen_local xilocal zetalocal Eqlocal) s0) ((extRen_local xilocal zetalocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition upExt_local_local   (sigma : ( fin ) -> local ) (tau : ( fin ) -> local ) (Eq : forall x, sigma x = tau x) : forall x, (up_local_local sigma) x = (up_local_local tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_local   (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (Eqlocal : forall x, sigmalocal x = taulocal x) (s : local ) : subst_local sigmalocal s = subst_local taulocal s :=
    match s return subst_local sigmalocal s = subst_local taulocal s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((ext_local sigmalocal taulocal Eqlocal) s2) ((ext_local sigmalocal taulocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x)(ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) ) (ext_local sigmalocal taulocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (ext_local sigmalocal taulocal Eqlocal)) (ext_local sigmalocal taulocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((ext_local sigmalocal taulocal Eqlocal) s2) ((ext_local sigmalocal taulocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) ) (ext_local sigmalocal taulocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1) ((ext_local sigmalocal taulocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((ext_local sigmalocal taulocal Eqlocal) s0)
    | ltplus  s0 s1 => congr_ltplus ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1) *)
    | ltadd  s0 s1 => congr_ltadd ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltmult  s0 s1 => congr_ltmult ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
    | ltsubtr s0 s1 => congr_ltsubtr ((ext_local sigmalocal taulocal Eqlocal) s0) ((ext_local sigmalocal taulocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition up_ren_ren_local_local    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_local_local tau) (upRen_local_local xi)) x = (upRen_local_local theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (rholocal : ( fin ) -> fin) (Eqlocal : forall x, ((funcomp) zetalocal xilocal) x = rholocal x) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s :=
    match s return ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s with
    | ltvar  s => (ap) (ltvar ) (Eqlocal s)
    | ltend   => congr_ltend 
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s2) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal))) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenRen_local xilocal zetalocal rholocal Eqlocal)) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s2) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal))) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0)
    | ltplus  s0 s1 => congr_ltplus ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1) *)
    | ltadd  s0 s1 => congr_ltadd ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltmult  s0 s1 => congr_ltmult ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
    | ltsubtr  s0 s1 => congr_ltsubtr ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s0) ((compRenRen_local xilocal zetalocal rholocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition up_ren_subst_local_local    (xi : ( fin ) -> fin) (tau : ( fin ) -> local ) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_local_local tau) (upRen_local_local xi)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) taulocal xilocal) x = thetalocal x) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s2) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal))) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenSubst_local xilocal taulocal thetalocal Eqlocal)) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s2) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal))) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0)
    | ltplus  s0 s1 => congr_ltplus ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1) *)
    | ltadd  s0 s1 => congr_ltadd ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltmult  s0 s1 => congr_ltmult ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
    | ltsubtr  s0 s1 => congr_ltsubtr ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s0) ((compRenSubst_local xilocal taulocal thetalocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition up_subst_ren_local_local    (sigma : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) (ren_local zetalocal) sigma) x = theta x) : forall x, ((funcomp) (ren_local (upRen_local_local zetalocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_local (shift) (upRen_local_local zetalocal) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_local zetalocal (shift) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_local (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (ren_local zetalocal) sigmalocal) x = thetalocal x) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s2) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal))) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal)) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s2) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal))) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) 
    | ltgt  s0 s1 => congr_ltgt ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) 
(*     | ltplus  s0 s1 => congr_ltplus ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)  *)
    | ltadd  s0 s1 => congr_ltadd ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) 
    | ltmult  s0 s1 => congr_ltmult ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) 
    | ltsubtr s0 s1 => congr_ltsubtr ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1) 
    | ltpair  s0 s1 => congr_ltpair ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal) s0) *)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition up_subst_subst_local_local    (sigma : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (theta : ( fin ) -> local ) (Eq : forall x, ((funcomp) (subst_local taulocal) sigma) x = theta x) : forall x, ((funcomp) (subst_local (up_local_local taulocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_local (shift) (up_local_local taulocal) ((funcomp) (up_local_local taulocal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_local taulocal (shift) ((funcomp) (ren_local (shift)) taulocal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_local (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (thetalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (subst_local taulocal) sigmalocal) x = thetalocal x) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s2) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal))) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal)) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s2) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal))) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0)
    | ltplus  s0 s1 => congr_ltplus ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1) *)
    | ltadd  s0 s1 => congr_ltadd ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltmult  s0 s1 => congr_ltmult ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
    | ltsubtr  s0 s1 => congr_ltsubtr ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s0) ((compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal) s1)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Definition rinstInst_up_local_local   (xi : ( fin ) -> fin) (sigma : ( fin ) -> local ) (Eq : forall x, ((funcomp) (ltvar ) xi) x = sigma x) : forall x, ((funcomp) (ltvar ) (upRen_local_local xi)) x = (up_local_local sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_local (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_local   (xilocal : ( fin ) -> fin) (sigmalocal : ( fin ) -> local ) (Eqlocal : forall x, ((funcomp) (ltvar ) xilocal) x = sigmalocal x) (s : local ) : ren_local xilocal s = subst_local sigmalocal s :=
    match s return ren_local xilocal s = subst_local sigmalocal s with
    | ltvar  s => Eqlocal s
    | ltend   => congr_ltend
    | ltinact   => congr_ltinact
    | ltsend  s0 s1 s2 s3 => congr_ltsend ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((rinst_inst_local xilocal sigmalocal Eqlocal) s2) ((rinst_inst_local xilocal sigmalocal Eqlocal) s3)
    | ltreceive  s0 s1 => congr_ltreceive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal))) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
(*     | ltselect  s0 s1 => congr_ltselect ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (rinst_inst_local xilocal sigmalocal Eqlocal)) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1) *)
    | ltselect  s0 s1 s2 s3 => congr_ltselect ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((rinst_inst_local xilocal sigmalocal Eqlocal) s2) ((rinst_inst_local xilocal sigmalocal Eqlocal) s3)
    | ltbranch  s0 s1 => congr_ltbranch ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal))) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
    | ltmu  s0 s1 => congr_ltmu ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltpi  s0 s1 => congr_ltpi ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltlambda  s0 s1 => congr_ltlambda ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltsig  s0 s1 => congr_ltsig ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltite  s0 s1 s2 => congr_ltite ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1) ((rinst_inst_local xilocal sigmalocal Eqlocal) s2)
    | ltapp  s0 s1 => congr_ltapp ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltgt  s0 s1 => congr_ltgt ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
(*     | ltplus  s0 s1 => congr_ltplus ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1) *)
    | ltadd  s0 s1 => congr_ltadd ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltmult  s0 s1 => congr_ltmult ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltsubtr  s0 s1 => congr_ltsubtr ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
    | ltpair  s0 s1 => congr_ltpair ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) ((rinst_inst_local xilocal sigmalocal Eqlocal) s1)
(*     | ltzero   => congr_ltzero 
    | ltsucc  s0 => congr_ltsucc ((rinst_inst_local xilocal sigmalocal Eqlocal) s0) *)
(*     | ltfalse   => congr_ltfalse 
    | lttrue   => congr_lttrue  *)
    | ltnat   => congr_ltnat 
    | ltbool   => congr_ltbool 
    | ltstar   => congr_ltstar 
    | ltnval n => congr_ltnval eq_refl
    | ltbval b => congr_ltbval eq_refl
    end.

Lemma rinstInst_local   (xilocal : ( fin ) -> fin) : ren_local xilocal = subst_local ((funcomp) (ltvar ) xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_local xilocal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_local  : subst_local (ltvar ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_local (ltvar ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_local  : @ren_local   (id) = id .
Proof. exact ((eq_trans) (rinstInst_local ((id) (_))) instId_local). Qed.

Lemma varL_local   (sigmalocal : ( fin ) -> local ) : (funcomp) (subst_local sigmalocal) (ltvar ) = sigmalocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_local   (xilocal : ( fin ) -> fin) : (funcomp) (ren_local xilocal) (ltvar ) = (funcomp) (ltvar ) xilocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) s .
Proof. exact (compSubstSubst_local sigmalocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_local    (sigmalocal : ( fin ) -> local ) (taulocal : ( fin ) -> local ) : (funcomp) (subst_local taulocal) (subst_local sigmalocal) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_local sigmalocal taulocal n)). Qed.

Lemma compRen_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) s .
Proof. exact (compSubstRen_local sigmalocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_local    (sigmalocal : ( fin ) -> local ) (zetalocal : ( fin ) -> fin) : (funcomp) (ren_local zetalocal) (subst_local sigmalocal) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_local sigmalocal zetalocal n)). Qed.

Lemma renComp_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local ((funcomp) taulocal xilocal) s .
Proof. exact (compRenSubst_local xilocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_local    (xilocal : ( fin ) -> fin) (taulocal : ( fin ) -> local ) : (funcomp) (subst_local taulocal) (ren_local xilocal) = subst_local ((funcomp) taulocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_local xilocal taulocal n)). Qed.

Lemma renRen_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local ((funcomp) zetalocal xilocal) s .
Proof. exact (compRenRen_local xilocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_local    (xilocal : ( fin ) -> fin) (zetalocal : ( fin ) -> fin) : (funcomp) (ren_local zetalocal) (ren_local xilocal) = ren_local ((funcomp) zetalocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_local xilocal zetalocal n)). Qed.

End local.


Global Instance Subst_local   : Subst1 (( fin ) -> local ) (local ) (local ) := @subst_local   .

Global Instance Ren_local   : Ren1 (( fin ) -> fin) (local ) (local ) := @ren_local   .

Global Instance VarInstance_local  : Var (fin) (local ) := @ltvar  .

Notation "x '__local'" := (ltvar x) (at level 5, format "x __local") : subst_scope.

Notation "x '__local'" := (@ids (_) (_) VarInstance_local x) (at level 5, only printing, format "x __local") : subst_scope.

Notation "'var'" := (ltvar) (only printing, at level 1) : subst_scope.

Class Up_local X Y := up_local : ( X ) -> Y.

Notation "↑__local" := (up_local) (only printing) : subst_scope.

Notation "↑__local" := (up_local_local) (only printing) : subst_scope.

Global Instance Up_local_local   : Up_local (_) (_) := @up_local_local   .

Notation "s |- sigmalocal -|" := (subst_local sigmalocal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "||- sigmalocal -||" := (subst_local sigmalocal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xilocal ⟩" := (ren_local xilocal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xilocal ⟩" := (ren_local xilocal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_local| progress rewrite ?compComp_local| progress rewrite ?compComp'_local| progress rewrite ?rinstId_local| progress rewrite ?compRen_local| progress rewrite ?compRen'_local| progress rewrite ?renComp_local| progress rewrite ?renComp'_local| progress rewrite ?renRen_local| progress rewrite ?renRen'_local| progress rewrite ?varL_local| progress rewrite ?varLRen_local| progress (unfold up_ren, upRen_local_local, up_local_local)| progress (cbn [subst_local ren_local])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_local in *| progress rewrite ?compComp_local in *| progress rewrite ?compComp'_local in *| progress rewrite ?rinstId_local in *| progress rewrite ?compRen_local in *| progress rewrite ?compRen'_local in *| progress rewrite ?renComp_local in *| progress rewrite ?renComp'_local in *| progress rewrite ?renRen_local in *| progress rewrite ?renRen'_local in *| progress rewrite ?varL_local in *| progress rewrite ?varLRen_local in *| progress (unfold up_ren, upRen_local_local, up_local_local in *)| progress (cbn [subst_local ren_local] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_local).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_local).
