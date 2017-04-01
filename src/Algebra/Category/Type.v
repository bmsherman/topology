Require Import 
  Algebra.Category
  Types.Setoid.

Set Universe Polymorphism.

Definition function@{A P} (A B : Type@{A}) : Setoid@{A P}.
Proof.
unshelve eapply (
  {| sty := A -> B
   ; seq := fun f g => forall x, f x = g x
  |}).
constructor; auto.
unfold CRelationClasses.Transitive.
intros. transitivity (y x0); auto. 
Defined.

(** The universe of level i types lives in
    Type i', where i < i'. *)
Definition TypeC@{i P i'} : Category@{i' i' P}.
Proof. 
unshelve eapply (
  Build_Category@{i' i' P} Type@{i} function@{i' P})
  ; simpl; auto.
simpl. intros. transitivity (g' (f x)); auto.
f_equal. apply H0.
Defined.

Definition Pi {A} (B : A -> Type) := forall a, B a.

Definition Has_Products {Ix : Type} (F : Ix -> TypeC)
  : Is_Product F (Pi F).
Proof.
unshelve econstructor.
- simpl. intros. apply X.
- simpl. intros. 
  exists (fun x ix => projX ix x). reflexivity.
  simpl.  intros.
  (* Looks like we need functional extensionality... *)
Abort.