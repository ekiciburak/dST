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
  | sc_lambda: forall c p e t' n m, sortCheck c m p sstar ->
                                      let t := betan n p in
                                      (* ctx ext *)
                                      sortCheck (cons (pair m t) c) (S m) e t' ->
                                      sortCheck c m (slambda p e) (spi t t') 
  | sc_app   : forall c e e' t t' n m, sortCheck c m e (spi t t') ->
                                         sortCheck c m e' t ->
                                         let tt := subst_sort (e' .: svar) t' in
                                         let t'' := betan n tt in
                                         sortCheck c m (sapp e e') t''
  | sc_pi    : forall c p p' n m, sortCheck c m p sstar ->
                                    let t := betan n p in
                                    (* ctx ext *)
                                    sortCheck (cons (pair m t) c) (S m) p' sstar ->
                                    sortCheck c m (spi p p') sstar
  | sc_pair  : forall c e1 p e2 t' n m, sortCheck c m e1 p ->
                                          let t := betan n p in
                                          (* ctx ext *)
                                          sortCheck (cons (pair m t) c) (S m) e2 t' ->
                                          sortCheck c m (spair e1 e2) (ssig t t')
  | sc_sig   : forall c p p' n m, sortCheck c m p sstar ->
                                    let t := betan n p in
                                    (* ctx ext *)
                                    sortCheck (cons (pair m t) c) (S m) p' sstar ->
                                    sortCheck c m (ssig p p') sstar
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
                                 sortCheck c m (sor e1 e2) sbool
  | sc_proj1 : forall c e t t' m, sortCheck c m e (ssig t t') ->
                                  sortCheck c m (sproj1 e) t
  | sc_proj2 : forall c e t1 t2 n m, sortCheck c m e (ssig t1 t2) ->
                                     let tt  := subst_sort ((sproj1 e) .: svar) t2 in
                                     let tt' := betan n tt in
                                     sortCheck c m (sproj2 e) tt'
  | sc_mu    : forall c t e t' m, sortCheck (cons (pair m t) c) (S m) e t' ->
                                  sortCheck c m (smu e) (spi t t').

(* Eval compute in 
(betan 3
(sapp (slambda sint (sapp (slambda sint (sgt (svar 1) (svar 0))) 
                          (sci 110))) 
      (sci 220))). *)


Example ex1: sortCheck nil 0 (sapp (slambda sint (sapp (slambda sint (sgt (svar 1) (svar 0))) 
                                                       (sci 110))) 
                             (sci 220))
             sbool.
Proof. simpl.
       specialize (sc_app nil
                          (slambda sint (sapp (slambda sint (sgt (svar 1) (svar 0))) (sci 110)))
                          (sci 220)
                          sint sbool 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            sint (sapp (slambda sint (sgt (svar 1) (svar 0))) (sci 110))
                            sbool
                            1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.

       specialize (sc_app (cons (pair 0 sint) nil) 
                          (slambda sint (sgt (svar 1) (svar 0)))
                          (sci 110)
                           sint sbool 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.

       specialize(sc_lambda (cons (pair 0 sint) nil) 
                            sint (sgt (svar 1) (svar 0))
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

Example ex2: sortCheck (cons (pair 5 sint) (cons (pair 6 sint) nil)) 0
             (spair (svar 5) (spair (svar 6) (sgt (svar 6) (svar 5))))
             (ssig sint (ssig sint sbool)).
Proof. specialize(sc_pair (cons (pair 5 sint) (cons (pair 6 sint) nil))
                          (svar 5) sint 
                          (spair (svar 6) (sgt (svar 6) (svar 5)))
                          (ssig sint sbool) 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       apply sc_var. simpl. easy.
       specialize(sc_pair (cons (pair 0 sint) (cons (pair 5 sint) (cons (pair 6 sint) nil)))
                         (svar 6) sint 
                         (sgt (svar 6) (svar 5))
                         sbool 1 1
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       apply sc_var. simpl. easy.
       apply sc_gt.
       apply sc_var. simpl. easy.
       apply sc_var. simpl. easy.
Qed.

Example ex3: sortCheck nil 0
              (sapp (slambda sint (splus (svar 0) (sci 50))) 
                    (sapp (slambda sint (sminus (svar 0) (sci 18)))  
                          (sci 12)
                  )
            ) sint.
Proof. specialize (sc_app nil
                          (slambda sint (splus (svar 0) (sci 50)))
                          (sapp (slambda sint (sminus (svar 0) (sci 18))) (sci 12))
                          sint sint 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            sint
                            (splus (svar 0) (sci 50))
                            sint 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_int.
       apply sc_plus.
       apply sc_var. simpl. easy.
       apply sc_cint.
       specialize (sc_app nil
                          (slambda sint (sminus (svar 0) (sci 18)))
                          (sci 12)
                          sint sint 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            sint
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
              (sapp (slambda (spi sint sint) (svar 0)) (slambda sint (splus (svar 0) (sci 5))))
              (spi sint sint).
Proof. specialize (sc_app nil
                          (slambda (spi sint sint) (svar 0))
                          (slambda sint (splus (svar 0) (sci 5)))
                          (spi sint sint) 
                          (spi sint sint) 1 0
       ); intro HS. simpl in HS.
       apply HS; clear HS.
       specialize(sc_lambda nil
                            (spi sint sint)
                            (svar 0) (spi sint sint) 1 0
       ); intro HL. simpl in HL.
       apply HL; clear HL.
       apply sc_pi with (n := 0).
       apply sc_int.
       simpl. apply sc_int.
       apply sc_var. simpl. easy.

       specialize(sc_lambda nil
                            sint
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





















