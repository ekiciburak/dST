From DST Require Import sort.axioms sort.unscoped sort.sort sort.beta.
(* From mathcomp Require Import all_ssreflect. *)
(* From Paco Require Import paco. *)
(* Require Import ST.src.stream. *)
Require Import String List Datatypes ZArith.
(* Local Open Scope string_scope. *)
Import ListNotations.

Fixpoint lookup (c:  (list (nat*sort))) (m: nat): option sort :=
  match c with
    | (pair n s1) :: xs => if Nat.eqb n m then Some s1 else lookup xs m
    |  nil              => None
  end.

Inductive sortCheck: list (fin*sort) -> fin -> sort -> sort -> Prop :=
  | sc_lambda: forall c x p e t' n m, sortCheck c m p sstar ->
                                      let t := betan n p in
                                      (* ctx ext *)
                                      sortCheck (cons (pair m t) c) (S m) e t' ->
                                      sortCheck c m (slambda x p e) (spi x t t') 
  | sc_app   : forall c e e' x t t' n m, sortCheck c m e (spi x t t') ->
                                         sortCheck c m e' t ->
                                         let tt := subst_sort (e' .: svar) t' in
                                         let t'' := betan n tt in
                                         sortCheck c m (sapp e e') t''
  | sc_pi    : forall c x p p' n m, sortCheck c m p sstar ->
                                    let t := betan n p in
                                    (* ctx ext *)
                                    sortCheck (cons (pair m t) c) (S m) p' sstar ->
                                    sortCheck c m (spi x p p') sstar
  | sc_pair  : forall c x p e t' n m, sortCheck c m p sstar ->
                                      let t := betan n p in
                                      (* ctx ext *)
                                      sortCheck (cons (pair m t) c) (S m) e t' ->
                                      sortCheck c m (spair x p e) (ssig x t t') 
  | sc_exst : forall c e e' x t t' n m, sortCheck c m e (ssig x t t') ->
                                        sortCheck c m e' t ->
                                        let tt := subst_sort (e' .: svar) t' in
                                        let t'' := betan n tt in
                                        sortCheck c m (sexst e' e) t''
  | sc_sig   : forall c x p p' n m, sortCheck c m p sstar ->
                                    let t := betan n p in
                                    (* ctx ext *)
                                    sortCheck (cons (pair m t) c) (S m) p' sstar ->
                                    sortCheck c m (ssig x p p') sstar
  | sc_star  : forall c m, sortCheck c m sstar sstar
  | sc_var   : forall c s t' m, Some t' = lookup c s ->
                                sortCheck c m (svar s) t' 
  | sc_cint  : forall c n m, sortCheck c m (sci n) sint
  | sc_cbool : forall c n m, sortCheck c m (scb n) sbool
  | sc_gt    : forall c e1 e2 m, sortCheck c m e1 sint ->
                                 sortCheck c m e2 sint ->
                                 sortCheck c m (sgt e1 e2) sbool
  | sc_int   : forall c m, sortCheck c m sint sstar
  | sc_bool  : forall c m, sortCheck c m sbool sstar
  | sc_ite   : forall c e1 e2 e3 t m, sortCheck c m e1 sbool ->
                                      sortCheck c m e2 t ->
                                      sortCheck c m e3 t ->
                                      sortCheck c m (site e1 e2 e3) t
  | sc_eq    : forall c e1 e2 t m, sortCheck c m e1 t ->
                                   sortCheck c m e2 t ->
                                   sortCheck c m (sort.seq e1 e2) sbool
  | sc_plus  : forall c e1 e2 m, sortCheck c m e1 sint ->
                                 sortCheck c m e2 sint ->
                                 sortCheck c m (splus e1 e2) sint
  | sc_minus : forall c e1 e2 m, sortCheck c m e1 sint ->
                                 sortCheck c m e2 sint ->
                                 sortCheck c m (sminus e1 e2) sint
  | sc_neg   : forall c e1 m, sortCheck c m e1 sbool -> 
                              sortCheck c m (sneg e1) sbool
  | sc_and   : forall c e1 e2 m, sortCheck c m e1 sbool ->
                                 sortCheck c m e2 sbool ->
                                 sortCheck c m (sand e1 e2) sbool
  | sc_or    : forall c e1 e2 m, sortCheck c m e1 sbool ->
                                 sortCheck c m e2 sbool ->
                                 sortCheck c m (sor e1 e2) sbool.

Example ex1: sortCheck nil 0 (sapp (slambda (svar 0) sint (sapp (slambda (svar 0) sint (sgt (svar 1) (svar 0))) 
                                                          (sci 110))) 
                                   (sci 220))
             sbool.
Proof. simpl.
       specialize (sc_app nil
                          (slambda (svar 0) sint (sapp (slambda (svar 0) sint (sgt (svar 1) (svar 0))) (sci 110)))
                          (sci 220)
                          (svar 0) sint sbool 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            (svar 0) sint (sapp (slambda (svar 0) sint (sgt (svar 1) (svar 0))) (sci 110))
                            sbool
                            1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.

       specialize (sc_app (cons (pair 0 sint) nil) 
                          (slambda (svar 0) sint (sgt (svar 1) (svar 0)))
                          (sci 110)
                          (svar 0) sint sbool 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.

       specialize(sc_lambda (cons (pair 0 sint) nil) 
                            (svar 0) sint (sgt (svar 1) (svar 0))
                            sbool
                            1 1
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.
       apply sc_gt.
       apply sc_var. simpl. easy.
       apply sc_var. simpl. easy.
       apply sc_cint.
       apply sc_cint.
Qed.

Example ex2: sortCheck nil 0
             (sexst (sci 220) (sexst (sci 110) (spair (svar 0) sint (spair (svar 0) sint (sgt (svar 1) (svar 0)))))) 
             sbool.
Proof. specialize(sc_exst nil
                          (sexst (sci 110) (spair (svar 0) sint (spair (svar 0) sint (sgt (svar 1) (svar 0)))))
                          (sci 220) (svar 0) sint sbool 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_exst nil
                          (spair (svar 0) sint (spair (svar 0) sint (sgt (svar 1) (svar 0))))
                          (sci 110) (svar 0) sint (ssig (svar 0) sint sbool) 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_pair nil
                         (svar 0) sint 
                         (spair (svar 0) sint (sgt (svar 1) (svar 0)))
                         (ssig (svar 0) sint sbool) 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       apply sc_int.
       specialize(sc_pair (cons (pair 0 sint) nil) 
                          (svar 0) sint 
                          (sgt (svar 1) (svar 0))
                          sbool 1 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       apply sc_int.
       apply sc_gt.
       apply sc_var. simpl. easy.
       apply sc_var. simpl. easy.
       apply sc_cint.
       apply sc_cint.
Qed.

Example ex3: sortCheck nil 0
              (sapp (slambda (svar 0) sint (splus (svar 0) (sci 50))) 
                    (sapp (slambda (svar 0) sint (sminus (svar 0) (sci 18)))  
                          (sci 12)
                  )
            ) sint.
Proof. specialize (sc_app nil
                          (slambda (svar 0) sint (splus (svar 0) (sci 50)))
                          (sapp (slambda (svar 0) sint (sminus (svar 0) (sci 18))) (sci 12))
                          (svar 0) sint sint 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            (svar 0) sint
                            (splus (svar 0) (sci 50))
                            sint 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.
       apply sc_plus.
       apply sc_var. simpl. easy.
       apply sc_cint.
       specialize (sc_app nil
                          (slambda (svar 0) sint (sminus (svar 0) (sci 18)))
                          (sci 12)
                          (svar 0) sint sint 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            (svar 0) sint
                            (sminus (svar 0) (sci 18))
                            sint 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.
       apply sc_minus.
       apply sc_var. simpl. easy.
       apply sc_cint.
       apply sc_cint.
Qed.

Example ex4: sortCheck nil 0
              (sapp (slambda (svar 0) (spi (svar 0) sint sint) (svar 0)) (slambda (svar 0) sint (splus (svar 0) (sci 5))))
              (spi (svar 0) sint sint).
Proof. specialize (sc_app nil
                          (slambda (svar 0) (spi (svar 0) sint sint) (svar 0))
                          (slambda (svar 0) sint (splus (svar 0) (sci 5)))
                          (svar 0) (spi (svar 0) sint sint) 
                          (spi (svar 0) sint sint) 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            (svar 0) (spi (svar 0) sint sint)
                            (svar 0) (spi (svar 0) sint sint) 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_pi with (n := 0).
       apply sc_int.
       simpl. apply sc_int.
       apply sc_var. simpl. easy.

       specialize(sc_lambda nil
                            (svar 0) sint
                             (splus (svar 0) (sci 5)) sint 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.
       apply sc_plus.
       apply sc_var. simpl. easy.
       apply sc_cint.
Qed.

(* Eval compute in betan 1
(sapp (slambda (svar 0) (spi (svar 0) sint sint) (svar 0)) (slambda (svar 0) sint (splus (svar 0) (sci 5)))).

Eval compute in betan 3
            (sapp (slambda (svar 0) sint (splus (svar 0) (sci 50))) 
                  (sapp (slambda (svar 0) sint (sminus (svar 0) (sci 18)))  
                        (sci 20)
                  )
            ).
 *)





















