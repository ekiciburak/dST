From RDST Require Import type.unscoped type.local type.beta.
Require Import String List Datatypes Lia Relations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.
From mathcomp Require Import ssreflect.seq.

Fixpoint lookup (c: (list (nat*local))) (m: nat): option local :=
  match c with
    | (pair n s1) :: xs => if Nat.eqb n m then Some s1 else lookup xs m
    |  nil              => None
  end.

Print process.

Inductive propcont: local -> Prop :=
  | pc_inact: propcont ltinact
  | pc_send : forall p l s c, propcont c -> propcont (ltsend p l s c)
  | pc_recv : forall p C, List.Forall (fun u => propcont u) (map snd C) -> 
                          propcont (ltreceive p C).

(* incomplete set of rules *)
Inductive typeCheck: list (fin*local) -> fin -> local -> local -> Prop :=
  | tc_inact : forall m c, typeCheck c m (ltinact) (ltend)
  | tc_var  : forall m c s t, Some t = lookup c s ->
                              typeCheck c m (ltvar s) t
  | tc_lambda: forall c p k e t' n m, typeCheck c m p ltstar ->
                                      let t := betan n k (mkproc p gnil) in
                                      (* ctx ext *)
                                      typeCheck ((m, (@body t)) :: c) (S m) e t' ->
                                      typeCheck c m (ltlambda p e) (ltpi (@body t) t')
  | tc_mu    : forall m c p t, typeCheck ((m, t) :: c) (S m) p t ->
                               typeCheck c m (ltmu t p) t
  | tc_app   : forall c k e e' t t' n m, typeCheck c m e (ltpi t t') ->
                                         typeCheck c m e' t ->
                                         let tt := subst_local (e' .: ltvar) t' in
                                         let t'' := betan n k (mkproc tt gnil) in
                                         typeCheck c m (ltapp e e') (@body t'')
  | tc_pi    : forall c k p p' (t: local) n m, typeCheck c m p ltstar ->
                                               let t := betan n k (mkproc p gnil) in
                                               (* ctx ext *)
                                               typeCheck ((m, (@body t)) :: c) (S m) p' ltstar ->
                                               typeCheck c m (ltpi p p') ltstar
  | tc_send  : forall m c p l e P S T, propcont P ->
                                       typeCheck c m e S ->
                                       typeCheck c m P T ->
                                       typeCheck c m (ltsend p l e P) (ltselect p l S T)
  | tc_recv  : forall m c p L (ST P T: list local),
                      List.Forall (fun u => propcont u) P -> 
                      length L = length ST ->
                      length ST = length P ->
                      length P = length T ->
                      (* ctx ext *)
                      List.Forall (fun u => typeCheck ((m, (fst u)) :: c) (S m) (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                      typeCheck c m (ltreceive p (zip (zip L ST) P)) (ltbranch p (zip (zip L ST) T)).