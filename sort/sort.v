From DST Require Import sort.unscoped.
Require Import ZArith.

Section sort.

Inductive sort  : Type :=
  | svar   : fin -> sort 
  | sint   : sort
  | sbool  : sort
  | sci    : Z    -> sort 
  | scb    : bool -> sort 
  | spi    : sort -> sort -> sort -> sort
  | slambda: sort -> sort -> sort -> sort
  | ssig   : sort -> sort -> sort -> sort
  | splus  : sort -> sort -> sort
  | sminus : sort -> sort -> sort
  | sgt    : sort -> sort -> sort
  | seq    : sort -> sort -> sort
  | sapp   : sort -> sort -> sort
  | sstar  : sort
  | site   : sort -> sort -> sort -> sort
  | spair  : sort -> sort -> sort -> sort
  | sexst  : sort -> sort -> sort
  | sneg   : sort -> sort
  | sand   : sort -> sort -> sort
  | sor    : sort -> sort -> sort.

Lemma congr_sint  : sint  = sint  .
Proof. congruence. Qed.

Lemma congr_sbool  : sbool  = sbool  .
Proof. congruence. Qed.

Lemma congr_sci  { s0 : Z   } { t0 : Z   } (H1 : s0 = t0) : sci  s0 = sci  t0 .
Proof. congruence. Qed.

Lemma congr_scb  { s0 : bool   } { t0 : bool   } (H1 : s0 = t0) : scb  s0 = scb  t0 .
Proof. congruence. Qed.

Lemma congr_spi  { s0 : sort   } { s1 : sort   } { s2 : sort   } { t0 : sort   } { t1 : sort   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : spi  s0 s1 s2 = spi  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_slambda  { s0 : sort   } { s1 : sort   } { s2 : sort   } { t0 : sort   } { t1 : sort   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : slambda  s0 s1 s2 = slambda  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ssig  { s0 : sort   } { s1 : sort   } { s2 : sort   } { t0 : sort   } { t1 : sort   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ssig  s0 s1 s2 = ssig  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_splus  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : splus  s0 s1 = splus  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sminus  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sminus  s0 s1 = sminus  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sgt  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sgt  s0 s1 = sgt  t0 t1 .
Proof. congruence. Qed.

Lemma congr_seq  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : seq  s0 s1 = seq  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sapp  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sapp  s0 s1 = sapp  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sstar  : sstar  = sstar  .
Proof. congruence. Qed.

Lemma congr_site  { s0 : sort   } { s1 : sort   } { s2 : sort   } { t0 : sort   } { t1 : sort   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : site  s0 s1 s2 = site  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_spair  { s0 : sort   } { s1 : sort   } { s2 : sort   } { t0 : sort   } { t1 : sort   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : spair  s0 s1 s2 = spair  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_sexst  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sexst  s0 s1 = sexst  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sneg  { s0 : sort   } { t0 : sort   } (H1 : s0 = t0) : sneg  s0 = sneg  t0 .
Proof. congruence. Qed.

Lemma congr_sand  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sand  s0 s1 = sand  t0 t1 .
Proof. congruence. Qed.

Lemma congr_sor  { s0 : sort   } { s1 : sort   } { t0 : sort   } { t1 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) : sor  s0 s1 = sor  t0 t1 .
Proof. congruence. Qed.

Definition upRen_sort_sort   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_sort   (xisort : ( fin ) -> fin) (s : sort ) : sort  :=
    match s return sort  with
    | svar  s => (svar ) (xisort s)
    | sint   => sint 
    | sbool   => sbool 
    | sci  s0 => sci  ((fun x => x) s0)
    | scb  s0 => scb  ((fun x => x) s0)
    | spi  s0 s1 s2 => spi  ((ren_sort (upRen_sort_sort xisort)) s0) ((ren_sort xisort) s1) ((ren_sort xisort) s2)
    | slambda  s0 s1 s2 => slambda  ((ren_sort (upRen_sort_sort xisort)) s0) ((ren_sort xisort) s1) ((ren_sort xisort) s2)
    | ssig  s0 s1 s2 => ssig  ((ren_sort (upRen_sort_sort xisort)) s0) ((ren_sort xisort) s1) ((ren_sort xisort) s2)
    | splus  s0 s1 => splus  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sminus  s0 s1 => sminus  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sgt  s0 s1 => sgt  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | seq  s0 s1 => seq  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sapp  s0 s1 => sapp  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sstar   => sstar 
    | site  s0 s1 s2 => site  ((ren_sort xisort) s0) ((ren_sort xisort) s1) ((ren_sort xisort) s2)
    | spair  s0 s1 s2 => spair  ((ren_sort (upRen_sort_sort xisort)) s0) ((ren_sort xisort) s1) ((ren_sort xisort) s2)
    | sexst  s0 s1 => sexst  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sneg  s0 => sneg  ((ren_sort xisort) s0)
    | sand  s0 s1 => sand  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    | sor  s0 s1 => sor  ((ren_sort xisort) s0) ((ren_sort xisort) s1)
    end.

Definition up_sort_sort   (sigma : ( fin ) -> sort ) : ( fin ) -> sort  :=
  (scons) ((svar ) (var_zero)) ((funcomp) (ren_sort (unscoped.shift)) sigma).

Fixpoint subst_sort   (sigmasort : ( fin ) -> sort ) (s : sort ) : sort  :=
    match s return sort  with
    | svar  s => sigmasort s
    | sint   => sint 
    | sbool   => sbool 
    | sci  s0 => sci  ((fun x => x) s0)
    | scb  s0 => scb  ((fun x => x) s0)
    | spi  s0 s1 s2 => spi  ((subst_sort (up_sort_sort sigmasort)) s0) ((subst_sort sigmasort) s1) ((subst_sort sigmasort) s2)
    | slambda  s0 s1 s2 => slambda  ((subst_sort (up_sort_sort sigmasort)) s0) ((subst_sort sigmasort) s1) ((subst_sort sigmasort) s2)
    | ssig  s0 s1 s2 => ssig  ((subst_sort (up_sort_sort sigmasort)) s0) ((subst_sort sigmasort) s1) ((subst_sort sigmasort) s2)
    | splus  s0 s1 => splus  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sminus  s0 s1 => sminus  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sgt  s0 s1 => sgt  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | seq  s0 s1 => seq  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sapp  s0 s1 => sapp  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sstar   => sstar 
    | site  s0 s1 s2 => site  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1) ((subst_sort sigmasort) s2)
    | spair  s0 s1 s2 => spair  ((subst_sort (up_sort_sort sigmasort)) s0) ((subst_sort sigmasort) s1) ((subst_sort sigmasort) s2)
    | sexst  s0 s1 => sexst  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sneg  s0 => sneg  ((subst_sort sigmasort) s0)
    | sand  s0 s1 => sand  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    | sor  s0 s1 => sor  ((subst_sort sigmasort) s0) ((subst_sort sigmasort) s1)
    end.

Definition upId_sort_sort  (sigma : ( fin ) -> sort ) (Eq : forall x, sigma x = (svar ) x) : forall x, (up_sort_sort sigma) x = (svar ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_sort (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_sort  (sigmasort : ( fin ) -> sort ) (Eqsort : forall x, sigmasort x = (svar ) x) (s : sort ) : subst_sort sigmasort s = s :=
    match s return subst_sort sigmasort s = s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((idSubst_sort (up_sort_sort sigmasort) (upId_sort_sort (_) Eqsort)) s0) ((idSubst_sort sigmasort Eqsort) s1) ((idSubst_sort sigmasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((idSubst_sort (up_sort_sort sigmasort) (upId_sort_sort (_) Eqsort)) s0) ((idSubst_sort sigmasort Eqsort) s1) ((idSubst_sort sigmasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((idSubst_sort (up_sort_sort sigmasort) (upId_sort_sort (_) Eqsort)) s0) ((idSubst_sort sigmasort Eqsort) s1) ((idSubst_sort sigmasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1) ((idSubst_sort sigmasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((idSubst_sort (up_sort_sort sigmasort) (upId_sort_sort (_) Eqsort)) s0) ((idSubst_sort sigmasort Eqsort) s1) ((idSubst_sort sigmasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((idSubst_sort sigmasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((idSubst_sort sigmasort Eqsort) s0) ((idSubst_sort sigmasort Eqsort) s1)
    end.

Definition upExtRen_sort_sort   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_sort_sort xi) x = (upRen_sort_sort zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (unscoped.shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_sort   (xisort : ( fin ) -> fin) (zetasort : ( fin ) -> fin) (Eqsort : forall x, xisort x = zetasort x) (s : sort ) : ren_sort xisort s = ren_sort zetasort s :=
    match s return ren_sort xisort s = ren_sort zetasort s with
    | svar  s => (ap) (svar ) (Eqsort s)
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((extRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upExtRen_sort_sort (_) (_) Eqsort)) s0) ((extRen_sort xisort zetasort Eqsort) s1) ((extRen_sort xisort zetasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((extRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upExtRen_sort_sort (_) (_) Eqsort)) s0) ((extRen_sort xisort zetasort Eqsort) s1) ((extRen_sort xisort zetasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((extRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upExtRen_sort_sort (_) (_) Eqsort)) s0) ((extRen_sort xisort zetasort Eqsort) s1) ((extRen_sort xisort zetasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1) ((extRen_sort xisort zetasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((extRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upExtRen_sort_sort (_) (_) Eqsort)) s0) ((extRen_sort xisort zetasort Eqsort) s1) ((extRen_sort xisort zetasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((extRen_sort xisort zetasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((extRen_sort xisort zetasort Eqsort) s0) ((extRen_sort xisort zetasort Eqsort) s1)
    end.

Definition upExt_sort_sort   (sigma : ( fin ) -> sort ) (tau : ( fin ) -> sort ) (Eq : forall x, sigma x = tau x) : forall x, (up_sort_sort sigma) x = (up_sort_sort tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_sort (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_sort   (sigmasort : ( fin ) -> sort ) (tausort : ( fin ) -> sort ) (Eqsort : forall x, sigmasort x = tausort x) (s : sort ) : subst_sort sigmasort s = subst_sort tausort s :=
    match s return subst_sort sigmasort s = subst_sort tausort s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((ext_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (upExt_sort_sort (_) (_) Eqsort)) s0) ((ext_sort sigmasort tausort Eqsort) s1) ((ext_sort sigmasort tausort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((ext_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (upExt_sort_sort (_) (_) Eqsort)) s0) ((ext_sort sigmasort tausort Eqsort) s1) ((ext_sort sigmasort tausort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((ext_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (upExt_sort_sort (_) (_) Eqsort)) s0) ((ext_sort sigmasort tausort Eqsort) s1) ((ext_sort sigmasort tausort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1) ((ext_sort sigmasort tausort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((ext_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (upExt_sort_sort (_) (_) Eqsort)) s0) ((ext_sort sigmasort tausort Eqsort) s1) ((ext_sort sigmasort tausort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sneg  s0 => congr_sneg ((ext_sort sigmasort tausort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((ext_sort sigmasort tausort Eqsort) s0) ((ext_sort sigmasort tausort Eqsort) s1)
    end.

Definition up_ren_ren_sort_sort    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_sort_sort tau) (upRen_sort_sort xi)) x = (upRen_sort_sort theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_sort    (xisort : ( fin ) -> fin) (zetasort : ( fin ) -> fin) (rhosort : ( fin ) -> fin) (Eqsort : forall x, ((funcomp) zetasort xisort) x = rhosort x) (s : sort ) : ren_sort zetasort (ren_sort xisort s) = ren_sort rhosort s :=
    match s return ren_sort zetasort (ren_sort xisort s) = ren_sort rhosort s with
    | svar  s => (ap) (svar ) (Eqsort s)
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((compRenRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upRen_sort_sort rhosort) (up_ren_ren (_) (_) (_) Eqsort)) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1) ((compRenRen_sort xisort zetasort rhosort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((compRenRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upRen_sort_sort rhosort) (up_ren_ren (_) (_) (_) Eqsort)) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1) ((compRenRen_sort xisort zetasort rhosort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((compRenRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upRen_sort_sort rhosort) (up_ren_ren (_) (_) (_) Eqsort)) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1) ((compRenRen_sort xisort zetasort rhosort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1) ((compRenRen_sort xisort zetasort rhosort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((compRenRen_sort (upRen_sort_sort xisort) (upRen_sort_sort zetasort) (upRen_sort_sort rhosort) (up_ren_ren (_) (_) (_) Eqsort)) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1) ((compRenRen_sort xisort zetasort rhosort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sneg  s0 => congr_sneg ((compRenRen_sort xisort zetasort rhosort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((compRenRen_sort xisort zetasort rhosort Eqsort) s0) ((compRenRen_sort xisort zetasort rhosort Eqsort) s1)
    end.

Definition up_ren_subst_sort_sort    (xi : ( fin ) -> fin) (tau : ( fin ) -> sort ) (theta : ( fin ) -> sort ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_sort_sort tau) (upRen_sort_sort xi)) x = (up_sort_sort theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_sort (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_sort    (xisort : ( fin ) -> fin) (tausort : ( fin ) -> sort ) (thetasort : ( fin ) -> sort ) (Eqsort : forall x, ((funcomp) tausort xisort) x = thetasort x) (s : sort ) : subst_sort tausort (ren_sort xisort s) = subst_sort thetasort s :=
    match s return subst_sort tausort (ren_sort xisort s) = subst_sort thetasort s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((compRenSubst_sort (upRen_sort_sort xisort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_ren_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1) ((compRenSubst_sort xisort tausort thetasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((compRenSubst_sort (upRen_sort_sort xisort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_ren_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1) ((compRenSubst_sort xisort tausort thetasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((compRenSubst_sort (upRen_sort_sort xisort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_ren_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1) ((compRenSubst_sort xisort tausort thetasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1) ((compRenSubst_sort xisort tausort thetasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((compRenSubst_sort (upRen_sort_sort xisort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_ren_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1) ((compRenSubst_sort xisort tausort thetasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((compRenSubst_sort xisort tausort thetasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((compRenSubst_sort xisort tausort thetasort Eqsort) s0) ((compRenSubst_sort xisort tausort thetasort Eqsort) s1)
    end.

Definition up_subst_ren_sort_sort    (sigma : ( fin ) -> sort ) (zetasort : ( fin ) -> fin) (theta : ( fin ) -> sort ) (Eq : forall x, ((funcomp) (ren_sort zetasort) sigma) x = theta x) : forall x, ((funcomp) (ren_sort (upRen_sort_sort zetasort)) (up_sort_sort sigma)) x = (up_sort_sort theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_sort (unscoped.shift) (upRen_sort_sort zetasort) ((funcomp) (unscoped.shift) zetasort) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_sort zetasort (unscoped.shift) ((funcomp) (unscoped.shift) zetasort) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_sort (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_sort    (sigmasort : ( fin ) -> sort ) (zetasort : ( fin ) -> fin) (thetasort : ( fin ) -> sort ) (Eqsort : forall x, ((funcomp) (ren_sort zetasort) sigmasort) x = thetasort x) (s : sort ) : ren_sort zetasort (subst_sort sigmasort s) = subst_sort thetasort s :=
    match s return ren_sort zetasort (subst_sort sigmasort s) = subst_sort thetasort s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((compSubstRen_sort (up_sort_sort sigmasort) (upRen_sort_sort zetasort) (up_sort_sort thetasort) (up_subst_ren_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((compSubstRen_sort (up_sort_sort sigmasort) (upRen_sort_sort zetasort) (up_sort_sort thetasort) (up_subst_ren_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((compSubstRen_sort (up_sort_sort sigmasort) (upRen_sort_sort zetasort) (up_sort_sort thetasort) (up_subst_ren_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((compSubstRen_sort (up_sort_sort sigmasort) (upRen_sort_sort zetasort) (up_sort_sort thetasort) (up_subst_ren_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s0) ((compSubstRen_sort sigmasort zetasort thetasort Eqsort) s1)
    end.

Definition up_subst_subst_sort_sort    (sigma : ( fin ) -> sort ) (tausort : ( fin ) -> sort ) (theta : ( fin ) -> sort ) (Eq : forall x, ((funcomp) (subst_sort tausort) sigma) x = theta x) : forall x, ((funcomp) (subst_sort (up_sort_sort tausort)) (up_sort_sort sigma)) x = (up_sort_sort theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_sort (unscoped.shift) (up_sort_sort tausort) ((funcomp) (up_sort_sort tausort) (unscoped.shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_sort tausort (unscoped.shift) ((funcomp) (ren_sort (unscoped.shift)) tausort) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_sort (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_sort    (sigmasort : ( fin ) -> sort ) (tausort : ( fin ) -> sort ) (thetasort : ( fin ) -> sort ) (Eqsort : forall x, ((funcomp) (subst_sort tausort) sigmasort) x = thetasort x) (s : sort ) : subst_sort tausort (subst_sort sigmasort s) = subst_sort thetasort s :=
    match s return subst_sort tausort (subst_sort sigmasort s) = subst_sort thetasort s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((compSubstSubst_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_subst_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((compSubstSubst_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_subst_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((compSubstSubst_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_subst_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((compSubstSubst_sort (up_sort_sort sigmasort) (up_sort_sort tausort) (up_sort_sort thetasort) (up_subst_subst_sort_sort (_) (_) (_) Eqsort)) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s0) ((compSubstSubst_sort sigmasort tausort thetasort Eqsort) s1)
    end.

Definition rinstInst_up_sort_sort   (xi : ( fin ) -> fin) (sigma : ( fin ) -> sort ) (Eq : forall x, ((funcomp) (svar ) xi) x = sigma x) : forall x, ((funcomp) (svar ) (upRen_sort_sort xi)) x = (up_sort_sort sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_sort (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_sort   (xisort : ( fin ) -> fin) (sigmasort : ( fin ) -> sort ) (Eqsort : forall x, ((funcomp) (svar ) xisort) x = sigmasort x) (s : sort ) : ren_sort xisort s = subst_sort sigmasort s :=
    match s return ren_sort xisort s = subst_sort sigmasort s with
    | svar  s => Eqsort s
    | sint   => congr_sint 
    | sbool   => congr_sbool 
    | sci  s0 => congr_sci ((fun x => (eq_refl) x) s0)
    | scb  s0 => congr_scb ((fun x => (eq_refl) x) s0)
    | spi  s0 s1 s2 => congr_spi ((rinst_inst_sort (upRen_sort_sort xisort) (up_sort_sort sigmasort) (rinstInst_up_sort_sort (_) (_) Eqsort)) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1) ((rinst_inst_sort xisort sigmasort Eqsort) s2)
    | slambda  s0 s1 s2 => congr_slambda ((rinst_inst_sort (upRen_sort_sort xisort) (up_sort_sort sigmasort) (rinstInst_up_sort_sort (_) (_) Eqsort)) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1) ((rinst_inst_sort xisort sigmasort Eqsort) s2)
    | ssig  s0 s1 s2 => congr_ssig ((rinst_inst_sort (upRen_sort_sort xisort) (up_sort_sort sigmasort) (rinstInst_up_sort_sort (_) (_) Eqsort)) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1) ((rinst_inst_sort xisort sigmasort Eqsort) s2)
    | splus  s0 s1 => congr_splus ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sminus  s0 s1 => congr_sminus ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sgt  s0 s1 => congr_sgt ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | seq  s0 s1 => congr_seq ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sapp  s0 s1 => congr_sapp ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sstar   => congr_sstar 
    | site  s0 s1 s2 => congr_site ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1) ((rinst_inst_sort xisort sigmasort Eqsort) s2)
    | spair  s0 s1 s2 => congr_spair ((rinst_inst_sort (upRen_sort_sort xisort) (up_sort_sort sigmasort) (rinstInst_up_sort_sort (_) (_) Eqsort)) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1) ((rinst_inst_sort xisort sigmasort Eqsort) s2)
    | sexst  s0 s1 => congr_sexst ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sneg  s0 => congr_sneg ((rinst_inst_sort xisort sigmasort Eqsort) s0)
    | sand  s0 s1 => congr_sand ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    | sor  s0 s1 => congr_sor ((rinst_inst_sort xisort sigmasort Eqsort) s0) ((rinst_inst_sort xisort sigmasort Eqsort) s1)
    end.

Lemma rinstInst_sort   (xisort : ( fin ) -> fin) : ren_sort xisort = subst_sort ((funcomp) (svar ) xisort) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_sort xisort (_) (fun n => eq_refl) x)). Qed.

Lemma instId_sort  : subst_sort (svar ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_sort (svar ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_sort  : @ren_sort   (id) = id .
Proof. exact ((eq_trans) (rinstInst_sort ((id) (_))) instId_sort). Qed.

Lemma varL_sort   (sigmasort : ( fin ) -> sort ) : (funcomp) (subst_sort sigmasort) (svar ) = sigmasort .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_sort   (xisort : ( fin ) -> fin) : (funcomp) (ren_sort xisort) (svar ) = (funcomp) (svar ) xisort .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_sort    (sigmasort : ( fin ) -> sort ) (tausort : ( fin ) -> sort ) (s : sort ) : subst_sort tausort (subst_sort sigmasort s) = subst_sort ((funcomp) (subst_sort tausort) sigmasort) s .
Proof. exact (compSubstSubst_sort sigmasort tausort (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_sort    (sigmasort : ( fin ) -> sort ) (tausort : ( fin ) -> sort ) : (funcomp) (subst_sort tausort) (subst_sort sigmasort) = subst_sort ((funcomp) (subst_sort tausort) sigmasort) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_sort sigmasort tausort n)). Qed.

Lemma compRen_sort    (sigmasort : ( fin ) -> sort ) (zetasort : ( fin ) -> fin) (s : sort ) : ren_sort zetasort (subst_sort sigmasort s) = subst_sort ((funcomp) (ren_sort zetasort) sigmasort) s .
Proof. exact (compSubstRen_sort sigmasort zetasort (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_sort    (sigmasort : ( fin ) -> sort ) (zetasort : ( fin ) -> fin) : (funcomp) (ren_sort zetasort) (subst_sort sigmasort) = subst_sort ((funcomp) (ren_sort zetasort) sigmasort) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_sort sigmasort zetasort n)). Qed.

Lemma renComp_sort    (xisort : ( fin ) -> fin) (tausort : ( fin ) -> sort ) (s : sort ) : subst_sort tausort (ren_sort xisort s) = subst_sort ((funcomp) tausort xisort) s .
Proof. exact (compRenSubst_sort xisort tausort (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_sort    (xisort : ( fin ) -> fin) (tausort : ( fin ) -> sort ) : (funcomp) (subst_sort tausort) (ren_sort xisort) = subst_sort ((funcomp) tausort xisort) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_sort xisort tausort n)). Qed.

Lemma renRen_sort    (xisort : ( fin ) -> fin) (zetasort : ( fin ) -> fin) (s : sort ) : ren_sort zetasort (ren_sort xisort s) = ren_sort ((funcomp) zetasort xisort) s .
Proof. exact (compRenRen_sort xisort zetasort (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_sort    (xisort : ( fin ) -> fin) (zetasort : ( fin ) -> fin) : (funcomp) (ren_sort zetasort) (ren_sort xisort) = ren_sort ((funcomp) zetasort xisort) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_sort xisort zetasort n)). Qed.

End sort.









































Global Instance Subst_sort   : Subst1 (( fin ) -> sort ) (sort ) (sort ) := @subst_sort   .

Global Instance Ren_sort   : Ren1 (( fin ) -> fin) (sort ) (sort ) := @ren_sort   .

Global Instance VarInstance_sort  : Var (fin) (sort ) := @svar  .

Notation "x '__sort'" := (svar x) (at level 5, format "x __sort") : subst_scope.

Notation "x '__sort'" := (@ids (_) (_) VarInstance_sort x) (at level 5, only printing, format "x __sort") : subst_scope.

Notation "'var'" := (svar) (only printing, at level 1) : subst_scope.

Class Up_sort X Y := up_sort : ( X ) -> Y.

Notation "↑__sort" := (up_sort) (only printing) : subst_scope.

Notation "↑__sort" := (up_sort_sort) (only printing) : subst_scope.

Global Instance Up_sort_sort   : Up_sort (_) (_) := @up_sort_sort   .

Notation "s [ sigmasort ]" := (subst_sort sigmasort s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmasort ]" := (subst_sort sigmasort) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xisort ⟩" := (ren_sort xisort s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xisort ⟩" := (ren_sort xisort) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_sort,  Ren_sort,  VarInstance_sort.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_sort,  Ren_sort,  VarInstance_sort in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_sort| progress rewrite ?compComp_sort| progress rewrite ?compComp'_sort| progress rewrite ?rinstId_sort| progress rewrite ?compRen_sort| progress rewrite ?compRen'_sort| progress rewrite ?renComp_sort| progress rewrite ?renComp'_sort| progress rewrite ?renRen_sort| progress rewrite ?renRen'_sort| progress rewrite ?varL_sort| progress rewrite ?varLRen_sort| progress (unfold up_ren, upRen_sort_sort, up_sort_sort)| progress (cbn [subst_sort ren_sort])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_sort in *| progress rewrite ?compComp_sort in *| progress rewrite ?compComp'_sort in *| progress rewrite ?rinstId_sort in *| progress rewrite ?compRen_sort in *| progress rewrite ?compRen'_sort in *| progress rewrite ?renComp_sort in *| progress rewrite ?renComp'_sort in *| progress rewrite ?renRen_sort in *| progress rewrite ?renRen'_sort in *| progress rewrite ?varL_sort in *| progress rewrite ?varLRen_sort in *| progress (unfold up_ren, upRen_sort_sort, up_sort_sort in *)| progress (cbn [subst_sort ren_sort] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_sort).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_sort).
