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

Axiom undefined : forall A, A.



Lemma Curry_Iso {A B C} : A ==> B ==> C ≅ A * B ==> C.
Proof.
refine (
  {| to := uncurry
   ; from := curry
  |}).
-  apply undefined.
- apply undefined.
Defined.

End Defns.

End CCC.