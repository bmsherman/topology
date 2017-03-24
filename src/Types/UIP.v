Require Import 
  Prob.StdLib
  Eqdep_dec.

Set Universe Polymorphism.

Lemma UIP_eq_dep_eq {A} :
  EqdepFacts.UIP_ A -> EqdepFacts.Eq_dep_eq A.
Proof.
intros H. apply EqdepFacts.eq_rect_eq__eq_dep_eq.
apply EqdepFacts.Streicher_K__eq_rect_eq.
apply EqdepFacts.UIP_refl__Streicher_K.
apply EqdepFacts.UIP__UIP_refl. assumption.
Qed.

Lemma UIP_inj_dep_pair {A} :
  EqdepFacts.UIP_ A -> EqdepFacts.Inj_dep_pair A.
Proof.
intros H. apply EqdepFacts.eq_dep_eq__inj_pair2.
apply UIP_eq_dep_eq. assumption.
Qed.

Ltac UIP_clean := match goal with
  | [ H : existT _ _ ?x = existT _ _ ?x |- _ ] => clear H
  | [ H : existT _ _ ?x = existT _ _ ?y |- _ ] => 
     apply UIP_inj_dep_pair in H; [| solve[auto] ]; subst
  end.

Ltac UIP_inv H := inv H; repeat UIP_clean.