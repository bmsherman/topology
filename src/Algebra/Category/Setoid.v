Require Import 
  CMorphisms
  Algebra.Category
  Types.Setoid.

Set Universe Polymorphism.

Local Open Scope setoid.

(** The universe of level i types lives in
    Type i', where i < i'. *)
Definition SetoidC@{A P A'} : Category@{A' A P}.
Proof. 
unshelve eapply (
  Build_Category@{A' A P} Setoid@{A P} function@{A P})
  ; simpl; auto.
- intros A. exact id.
- intros A B C. exact compose.
- simpl. intros. auto.
- simpl. intros. apply sf_proper. assumption.
- simpl. intros. apply sf_proper. assumption.
- simpl. intros. apply h. apply g. apply f. assumption.
Defined.

Definition Pi {A} (B : A -> Type) := forall a, B a.


Definition Product {Ix} (F : Ix -> SetoidC)
  : SetoidC.
Proof.
unshelve econstructor.
- exact (Pi F).
- exact (fun x y => forall ix, x ix == y ix).
- constructor; unfold Reflexive, Symmetric, Transitive;
    simpl; intros.
  + reflexivity.
  + symmetry. auto.
  + etransitivity; eauto.
Defined.

Definition Has_Products {Ix : Type} (F : Ix -> SetoidC)
  : Is_Product F (Product F).
Proof.
unshelve econstructor.
- simpl. intros. unshelve econstructor.
  + auto.
  + simpl. auto.
- simpl. intros. unshelve econstructor.
  + unshelve econstructor.
    * intros. simpl. unfold Pi. intros ix.
      apply projX. assumption.
    * simpl. intros. apply sf_proper. assumption.
  + simpl. intros. apply sf_proper. assumption.
  + simpl. intros. symmetry. apply X0. symmetry. assumption.
Defined.

Require Import 
  Category.Type
  Category.Functor.

Local Open Scope cat.

Definition Type_Setoid : TypeC ==> SetoidC.
Proof.
unshelve econstructor.
- exact Leib.Leibniz.
- simpl. intros. unshelve econstructor.
  + simpl. intros. apply Leib.Leibniz_func. assumption. 
  + simpl. intros. subst. auto.
- simpl. auto.
- simpl. intros. subst. auto.
Defined.

Lemma Type_Setoid_Faithful : Faithful Type_Setoid.
Proof.
unfold Faithful. simpl. auto.
Qed.

Lemma Type_Setoid_Full : Full Type_Setoid.
Proof.
unfold Full. simpl. intros.
exists f. intros. f_equal. assumption.
Qed.

Require Import Algebra.SetsC.

Set Printing Universes.

Definition Powerset@{A P AP AP'} (A : Setoid@{A P}) : Setoid@{AP' AP}.
Proof.
unshelve econstructor.
exact (Subset@{A P} A).
- exact (Same_set@{A P AP}).
- typeclasses eauto.
Defined.