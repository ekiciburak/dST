From DST Require Import sort.unscoped sort.sort sort.beta sort.sortcheck.
Require Import ZArith String List.

Notation participant := string (only parsing).
Notation label       := string (only parsing).

Section process.
(* Inductive process  : Type :=
  | ps_var : fin -> process 
  | ps_end : process 
  | ps_send : ( participant   ) -> ( label   ) -> ( sort   ) -> ( process   ) -> process 
  | ps_receive : ( participant   ) -> ( list (prod (prod (label  ) (sort  )) (process  )) ) -> process 
  | ps_ite : ( sort   ) -> ( process   ) -> ( process   ) -> process 
  | ps_mu : ( process   ) -> sort -> process .

Lemma congr_ps_end  : ps_end  = ps_end  .
Proof. congruence. Qed.

Lemma congr_ps_send  { s0 : participant   } { s1 : label   } { s2 : sort   } { s3 : process   } { t0 : participant   } { t1 : label   } { t2 : sort   } { t3 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : ps_send  s0 s1 s2 s3 = ps_send  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ps_receive  { s0 : participant   } { s1 : list (prod (prod (label  ) (sort  )) (process  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (sort  )) (process  )) } (H1 : s0 = t0) (H2 : s1 = t1) : ps_receive  s0 s1 = ps_receive  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ps_ite  { s0 : sort   } { s1 : process   } { s2 : process   } { t0 : sort   } { t1 : process   } { t2 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ps_ite  s0 s1 s2 = ps_ite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ps_mu  { s0 : process   } { t0 : process } (H1 : s0 = t0) : ps_mu  s0 = ps_mu  t0 .
Proof. congruence. Qed.

Definition upRen_process_process   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_process (xisort : fin -> fin) (xiprocess : fin -> fin) (s : process ) : process  :=
    match s return process  with
    | ps_var p => (ps_var) (xiprocess p) 
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ((ren_sort (xisort)) s2) ((ren_process xisort (xiprocess)) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (ren_sort xisort)) (ren_process xisort xiprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((ren_sort xisort) s0) ((ren_process xiprocess) xisort s1) ((ren_process xiprocess) xisort s2)
    | ps_mu  s0 e => ps_mu  ((ren_process xisort (upRen_process_process xiprocess)) s0) ((ren_sort (xisort)) e) 
    end.

Definition up_process_process (sigma : ( fin ) -> process ) : ( fin ) -> process  :=
  (scons) ((ps_var) (var_zero) ) ((funcomp) (ren_process (unscoped.shift) (unscoped.shift)) (sigma)).

Fixpoint subst_process (sigmasort : fin -> sort)  (sigmaprocess : ( fin ) -> process ) (s : process ) : process  :=
    match s return process  with
    | ps_var s => (sigmaprocess s)
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ( ((subst_sort sigmasort) s2)) ((subst_process sigmasort sigmaprocess) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_process sigmasort sigmaprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((subst_process sigmasort sigmaprocess) s1) ((subst_process sigmasort sigmaprocess) s2)
    | ps_mu s0 e => ps_mu  ((subst_process sigmasort (up_process_process (sigmaprocess ))) s0) ( ((subst_sort sigmasort) e))
    end. *)

Inductive process  : Type :=
  | ps_var : fin -> process 
  | ps_end : process 
  | ps_send : ( participant   ) -> ( label   ) -> ( sort   ) -> ( process   ) -> process 
  | ps_receive : ( participant   ) -> ( list (prod (prod (label  ) (sort)) (process  )) ) -> process 
  | ps_ite : ( sort   ) -> ( process   ) -> ( process   ) -> process 
  | ps_mu : ( process   ) -> sort -> process .

Lemma congr_ps_end  : ps_end  = ps_end  .
Proof. congruence. Qed.

Lemma congr_ps_send  { s0 : participant   } { s1 : label   } { s2 : sort   } { s3 : process   } { t0 : participant   } { t1 : label   } { t2 : sort   } { t3 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : ps_send  s0 s1 s2 s3 = ps_send  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ps_receive  { s0 : participant   } { s1 : list (prod (prod (label  ) (sort  )) (process  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (sort  )) (process  )) } (H1 : s0 = t0) (H2 : s1 = t1) : ps_receive  s0 s1 = ps_receive  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ps_ite  { s0 : sort   } { s1 : process   } { s2 : process   } { t0 : sort   } { t1 : process   } { t2 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ps_ite  s0 s1 s2 = ps_ite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ps_mu  { s0 : process   } { t0 : process } (H1 : s0 = t0) : ps_mu  s0 = ps_mu  t0 .
Proof. congruence. Qed.

Definition upRen_process_process   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_process (xiprocess : fin -> fin) (s : process ) : process  :=
    match s return process  with
    | ps_var p => (ps_var) (xiprocess p) 
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((ren_process (xiprocess)) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_process xiprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((ren_process xiprocess) s1) ((ren_process xiprocess) s2)
    | ps_mu  s0 e => ps_mu  ((ren_process (upRen_process_process xiprocess)) s0) e
    end.

Definition up_process_process (sigma : ( fin ) -> process ) : ( fin ) -> process  :=
  (scons) ((ps_var) (var_zero) ) ((funcomp) (ren_process (unscoped.shift)) (sigma)).
  
Fixpoint subst_process (sigmasort : ( fin ) -> sort)  (sigmaprocess : ( fin ) -> process ) (s : process ) : process  :=
    match s return process  with
    | ps_var s => (sigmaprocess s)
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ( beta ((subst_sort ( (sigmasort ))) s2)) ((subst_process sigmasort sigmaprocess) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (subst_sort (up_sort_sort (sigmasort )))) (subst_process sigmasort sigmaprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((subst_process sigmasort sigmaprocess) s1) ((subst_process sigmasort sigmaprocess) s2)
    | ps_mu s0 e => ps_mu  ((subst_process sigmasort (up_process_process (sigmaprocess ))) s0) e (* (subst_sort ((sigmasort )) e) *)
    end.

(* Fixpoint ren_process (xisort: fin -> fin) (xiprocess : fin -> fin) (s : process ) : process  :=
    match s return process  with
    | ps_var p => (ps_var) (xiprocess p) 
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ((ren_sort (xisort)) s2) ((ren_process xisort (xiprocess)) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_process xisort xiprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((ren_process xiprocess) xisort s1) ((ren_process xisort xiprocess) s2)
    | ps_mu  s0 e => ps_mu  ((ren_process xisort (upRen_process_process xiprocess)) s0) e
    end.

Definition up_process_process (sigma : ( fin ) -> process ) : ( fin ) -> process  :=
  (scons) ((ps_var) (var_zero) ) ((funcomp) (ren_process (unscoped.shift) (unscoped.shift)) (sigma)).

Fixpoint subst_process (sigmasort : ( fin ) -> sort)  (sigmaprocess : ( fin ) -> process ) (s : process ) : process  :=
    match s return process  with
    | ps_var s => (sigmaprocess s)
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ( ((fun x => x) (* (subst_sort (up_sort_sort (sigmasort ))) *) s2)) ((subst_process sigmasort sigmaprocess) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x) (* (subst_sort (up_sort_sort (sigmasort ))) *)) (subst_process sigmasort sigmaprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((subst_process sigmasort sigmaprocess) s1) ((subst_process sigmasort sigmaprocess) s2)
    | ps_mu s0 e => ps_mu  ((subst_process sigmasort (up_process_process (sigmaprocess ))) s0) e
    end. *)

End process.

