From DST Require Import sort.unscoped sort.sort.
Require Import ZArith.

Definition isVal (s: sort): bool :=
  match s with
    | slambda e1 e2 e3 => true
    | spi e1 e2 e3     => true
    | spair e1 e2 e3   => true
    | ssig e1 e2 e3     => true
    | sstar            => true
    | sci n            => true
    | scb b            => true
    | sint             => true
    | sbool            => true 
    | _                => false
  end.

Fixpoint beta (s: sort): sort :=
  match s with
    | sapp (slambda y e1 e2) e3    => subst_sort (e3 .: svar) e2
    | slambda y e1 e2              => slambda y (beta e1) (beta e2)
    | sapp (spi y e1 e2) e3        => subst_sort (e3 .: svar) e2
    | spi y e1 e2                  => spi y (beta e1) (beta e2)
    | ssig y e1 e2                 => ssig y (beta e1) (beta e2)
    | sexst e3 (spair y e1 e2)     => subst_sort (e3 .: svar) e2
    | sexst e1 e2                  => sexst (beta e1) e2
    | sapp e1 e2                   => sapp (beta e1) e2
    | splus e1 e2                  => let be1 := beta e1 in
                                      let be2 := beta e2 in 
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => sci (n+m)
                                            | _     => splus be1 be2
                                          end 
                                        | _     => splus be1 e2
                                      end
    | sminus e1 e2                 => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => sci (n-m)
                                            | _     => sminus be1 e2
                                          end 
                                        | _     => sminus be1 be2
                                      end
    | sgt e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => scb (Z.gtb n m)
                                            | _     => sgt be1 be2
                                          end 
                                        | _     => sgt be1 be2
                                      end
    | seq e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => scb (Z.eqb n m)
                                            | _     => seq be1 be2
                                          end 
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (Bool.eqb n m)
                                            | _     => seq be1 be2
                                          end 
                                        | _     => seq be1 be2
                                      end
    | site (scb true) e2 e3        => e2
    | site (scb false) e2 e3       => e3
    | site e1 e2 e3                => site (beta e1) e2 e3 
    | sneg e1                      => let be1 := beta e1 in
                                      match be1 with
                                        | scb b => scb (negb b)
                                        | _     => sneg be1
                                      end
    | sand e1 e2                   => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (andb n m)
                                            | _     => sand be1 be2
                                          end
                                        | _     => sand be1 be2
                                      end
    | sor e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (orb n m)
                                            | _     => sor be1 be2
                                          end
                                        | _     => sor be1 be2
                                      end
    | _                            => s
  end.

Fixpoint betan (n: nat) (s: sort): sort :=
  match n with
    | O   => s
    | S k => if isVal s then s else betan k (beta s) 
  end.


Fixpoint replaceSort (s e: sort): sort :=
  match s with
    | slambda x e1 e2 => (subst_sort (e .: svar) e2)
    | spi x e1 e2     => (subst_sort (e .: svar) e2)
    | spair x e1 e2   => (subst_sort (e .: svar) e2)
    | ssig x e1 e2    => (subst_sort (e .: svar) e2)
    | sapp e1 e2      => sapp (replaceSort e1 e) (replaceSort e2 e)
    | sexst e1 e2     => sexst (replaceSort e1 e) (replaceSort e2 e)
    | splus e1 e2     => splus (replaceSort e1 e) (replaceSort e2 e)
    | sminus e1 e2    => sminus (replaceSort e1 e) (replaceSort e2 e)
    | sgt e1 e2       => sgt (replaceSort e1 e) (replaceSort e2 e)
    | seq e1 e2       => seq (replaceSort e1 e) (replaceSort e2 e)
    | site e1 e2 e3   => site (replaceSort e1 e) (replaceSort e2 e) (replaceSort e3 e)
    | sneg e1         => sneg (replaceSort e1 e)
    | sand e1 e2      => sand (replaceSort e1 e) (replaceSort e2 e)
    | sor e1 e2       => sor (replaceSort e1 e) (replaceSort e2 e)
    | svar n          => (* if isVal e then e else s *) e
    | _               => s
  end.


(* Eval compute in replaceSort (slambda (svar 0) sint (slambda (svar 0) sint (splus (svar 1) (svar 0)))) (sci 22).

Eval compute in (replaceSort (splus (svar 0) (slambda (svar 0) sint (splus (svar 0) (sci 20)))) (sminus (svar 0) (sci 1))).
Eval compute in (replaceSort (slambda (svar 0) (sint) (sminus (svar 0) (sci 5))) (splus (svar 0) (sci 5))). *)


 *)
