(* Cartesian closed categories *)

Set Universe Polymorphism.
Set Asymmetric Patterns.

Require Import Prob.Spec.Category.
Import Category.

Local Open Scope obj.
Local Open Scope morph.

Module CCC.
Section CCC.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Require Import Morphisms.
Class CCCOps : Type :=
  { Func : U -> U -> U
  ; eval : forall {A B}, Func A B * A ~~> B
  ; abstract : forall {Γ A B}, Γ * A ~~> B -> Γ ~~> Func A B
  }.

Context {cccops : CCCOps}.

Class CCCProps : Prop :=
  { abstract_Proper :> forall Γ A B, Proper (eq ==> eq) (@abstract _ Γ A B)
  ; eval_abstract : forall {Γ A B} (e : Γ * A ~~> B), 
     eval ∘ (abstract e ⊗ id (A := A)) == e
  ; abstract_eval : forall {Γ A B } (f : Γ ~~> Func A B), 
     abstract (eval ∘ f ⊗ id (A := A)) == f
  ; abstract_ext : forall {Γ Γ' A B} (e : Γ * A ~~> B)
     (f : Γ' ~~> Γ),
     abstract e ∘ f == abstract (e ∘ (f ⊗ id))
  }.

End CCC.

Infix "==>" := Func (at level 55, right associativity) : obj_scope.

Arguments CCCOps U {_} : clear implicits.
Arguments CCCProps U {_ _ _} : clear implicits.

Section Defns.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}
  {cmcprops : CMC_Props U}
  {cccops : CCCOps U} {cccprops : CCCProps U}.

Lemma abstract_eta : forall {Γ A B} (f f' : Γ * A ~~> B),
      abstract f == abstract f' -> f == f'.
Proof.
intros. rewrite <- eval_abstract.
rewrite H. rewrite eval_abstract. reflexivity.
Qed.

Definition postcompose {A A' B} (f : A' ~~> A)
  : A ==> B ~~> A' ==> B
  := abstract (eval ∘ (id ⊗ f)).

Definition precompose {A B B'} (f : B ~~> B')
  : A ==> B ~~> A ==> B'
  := abstract (f ∘ eval).

Definition uncurry {A B C} :
  A ==> B ==> C ~~> A * B ==> C.
Proof.
apply abstract.
  eapply compose. Focus 2. apply prod_assoc_left.
  eapply compose. Focus 2.
  apply (eval ⊗ id). apply eval.
Defined.

Definition curry {A B C} :
  A * B ==> C ~~> A ==> B ==> C.
Proof.
apply abstract. apply abstract.
eapply compose. Focus 2. apply prod_assoc_right.
apply eval.
Defined.

Definition Const A := unit ~~> A.

Require Import Types.Setoid.
Require Import Morphisms.

Require Import Spec.Functor.
Definition multR_F (C : U) : Functor U U.
Proof.
unshelve econstructor.
- exact (fun x => x * C).
- simpl. intros. exact (X ⊗ id).
- simpl. prove_map_Proper.
- simpl. intros. apply parallel_id.
- simpl. intros. rewrite parallel_compose.
  rewrite compose_id_left. reflexivity.
Defined.

Axiom undefined : forall A, A.
Definition exp_F (C : U) : Functor U U.
Proof.
unshelve econstructor.
- exact (fun x => C ==> x).
- simpl. intros. eapply precompose. assumption.
- unfold precompose. prove_map_Proper.
- unfold precompose. intros. 
  rewrite compose_id_left.
  rewrite <- (compose_id_right eval).
  rewrite <- parallel_id. apply abstract_eval.
- simpl. intros. unfold precompose.
  rewrite abstract_ext. apply abstract_Proper.
  rewrite <- !compose_assoc.
  rewrite eval_abstract. reflexivity.
Defined.

Lemma eval_abstract_Iso {Γ A B} :
  (Hom_Setoid Γ (A ==> B) ≅ Hom_Setoid (Γ * A) B)%setoid.
Proof.
simple refine (Build_Iso _ _ _ _ _ _ _ _); simpl.
- intros. refine (eval ∘ (X ⊗ id)).
- apply abstract.
- prove_map_Proper. 
- prove_map_Proper.
- simpl. intros. rewrite eval_abstract. reflexivity.
- intros. simpl. rewrite abstract_eval. reflexivity.
Defined.

Lemma exp_adjoint (C : U) : (multR_F C -| exp_F C)%functor.
Proof.
unshelve econstructor.
- intros. apply eval_abstract_Iso.
- simpl. intros. unfold precompose.
  rewrite <- (compose_assoc f).
  rewrite abstract_ext. apply abstract_Proper.
  rewrite <- !compose_assoc.
  apply compose_Proper. reflexivity.
  rewrite abstract_ext. rewrite eval_abstract.
  reflexivity.
Defined.

Lemma internalize_Iso {A B} : 
  (Hom_Setoid unit (A ==> B) ≅ Hom_Setoid A B)%setoid.
Proof.
eapply Iso_Trans. apply eval_abstract_Iso.
apply Hom_Setoid_Iso. apply Iso_add_unit_left.
apply Category.Iso_Refl.
Defined.

Lemma Curry_Iso_weak {A B C} Γ :
  (Hom_Setoid Γ (A ==> B ==> C) ≅
   Hom_Setoid Γ (A * B ==> C))%setoid.
Proof.
pose proof (compose_Adjunction (exp_adjoint A) (exp_adjoint B)) as X.
eapply Iso_Trans. apply (Adj_Hom_Iso _ _ X).
simpl.
eapply Iso_Trans. Focus 2.
apply (Iso_Sym eval_abstract_Iso).
eapply Hom_Setoid_Iso. apply (Category.Iso_Sym Iso_Prod_Assoc).
apply Category.Iso_Refl.
Defined.

Definition Adjoint_Iso {F G : Functor U U}
  : (F -| G)%functor
  -> forall A B, A ==> G B ≅ F A ==> B.
Proof.
intros. unshelve (eapply Category.Build_Iso).
Abort.


Lemma lift_weak_Iso {A B}
  (equiv : forall Γ, (Hom_Setoid Γ A ≅ Hom_Setoid Γ B)%setoid)
  : to (equiv A) id ∘ from (equiv B) id == id 
  -> from (equiv B) id ∘ to (equiv A) id == id
  -> A ≅ B.
Proof.
intros. unshelve (eapply Category.Build_Iso).
apply (to (equiv A)). apply id.
apply (from (equiv B)). apply id.
assumption. assumption.
Defined.

Lemma Curry_Iso {A B C} : A ==> B ==> C ≅ A * B ==> C.
Proof.
unshelve (eapply lift_weak_Iso).
intros. apply Curry_Iso_weak.
simpl. rewrite !parallel_id.
rewrite !compose_id_left, !compose_id_right.
rewrite abstract_ext.
rewrite <- (abstract_eval id).
 apply abstract_Proper.
rewrite <- !compose_assoc.
apply undefined.
simpl. apply undefined.
Defined.

End Defns.

End CCC.