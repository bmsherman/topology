Require Export Coq.Sets.Ensembles.
Require Import Morphisms.

Arguments Intersection {U} _ _ _.
Arguments Inhabited {U} _.
Arguments In {U} _ _.
Arguments Same_set {U} _ _.
Arguments Included {U} _ _.
Arguments Union {U} _ _ _.

Infix "⊆" := Included (at level 60) : Ensemble_scope.
Infix "∩" := Intersection (at level 50) : Ensemble_scope.
Infix "∪" := Union (at level 55) : Ensemble_scope.
Infix "===" := Same_set (at level 70) : Ensemble_scope.

Delimit Scope Ensemble_scope with Ensemble.
Local Open Scope Ensemble.

Inductive union {S T} (U : Ensemble S) (f : S -> Ensemble T) : Ensemble T :=
  union_intro : forall a b, In U a -> f a b -> In (union U f) b.

Theorem Union_union : forall A B (a b : Ensemble A) (f : A -> Ensemble B),
  union a f ∪ union b f === union (a ∪ b) f.
Proof.
intros. constructor; unfold Included; intros.
- destruct H; destruct H; econstructor; 
  (eassumption || (econstructor (eassumption))).
- destruct H. destruct H; [ left | right]; econstructor; eauto.
Qed.

Theorem Intersection_Included_l : forall A (U V : Ensemble A),
  U ∩ V ⊆ U.
Proof.
intros. unfold Included. intros. destruct H. assumption.
Qed.

Theorem Intersection_Included_r : forall A (U V : Ensemble A),
  U ∩ V ⊆ V.
Proof.
intros. unfold Included. intros. destruct H. assumption.
Qed.

Theorem Union_Included_l : forall A (U V : Ensemble A),
  U ⊆ U ∪ V.
Proof.
intros. unfold Included. intros. constructor 1; eassumption. 
Qed.

Theorem Union_Included_r : forall A (U V : Ensemble A),
  V ⊆ U ∪ V.
Proof.
intros. unfold Included. intros. constructor 2; eassumption. 
Qed.

Instance Intersection_Proper_le : forall U,
  Proper (Included ==> Included ==> Included) (@Intersection U).
Proof.
intros. unfold Proper, respectful.
intros. constructor. 
- destruct H1. apply H. assumption. 
- destruct H1. apply H0. assumption.
Qed.

Instance Intersection_Proper : forall U,
  Proper (Same_set ==> Same_set ==> Same_set) (@Intersection U).
Proof.
intros. unfold Proper, respectful.
intros. destruct H, H0. constructor;
apply Intersection_Proper_le; assumption.
Qed.

Instance Union_Proper_le : forall U,
  Proper (Included ==> Included ==> Included) (@Union U).
Proof.
intros. unfold Proper, respectful.
intros. unfold Included; intros. 
destruct H1.
- constructor 1. apply H. assumption.
- constructor 2. apply H0. assumption.
Qed.

Instance Included_Reflexive : forall U, Reflexive (@Included U).
Proof.
intros. unfold Reflexive. intros.
unfold Included. intros. assumption.
Qed.

Instance Included_Transitive : forall U, Transitive (@Included U).
Proof.
intros. unfold Transitive. unfold Included. intros.
eauto.
Qed.

Instance Included_subrelation : forall U, subrelation (@Same_set U) (@Included U).
Proof.
intros. unfold subrelation, predicate_implication, pointwise_lifting,
  Basics.impl. intros. destruct H. assumption.
Qed.

Instance Included_Proper : forall U, Proper (@Same_set U ==> @Same_set U ==> iff)
  (@Included U).
Proof.
intros. unfold Proper, respectful.
intros. destruct H, H0. split; intros;
repeat (etransitivity; try eassumption).
Qed.

Theorem Same_set_iff : forall A (U V : Ensemble A),
  (forall x, U x <-> V x) -> U === V.
Proof.
intros. split; unfold Included, In; intros.
- apply H; assumption. 
- apply H; assumption.
Qed.

Instance Same_set_Equivalence : forall U, Equivalence (@Same_set U).
Proof. intros. unfold Same_set. constructor.
- unfold Reflexive. intros; split; reflexivity.
- unfold Symmetric. intros; tauto.
- unfold Transitive. intros. destruct H, H0. 
  split; etransitivity; eassumption.
Qed.
