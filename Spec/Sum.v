Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Sum.
Section Sum.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Class SumTys : Type :=
  { False : U
  ; sum : U -> U -> U }.

Infix "+" := sum : obj_scope.

Context `{sts : SumTys}.

(** Does sum_elim need to have the context Γ? It seems
    like it may *)
Class SumOps : Type :=
  { False_elim : forall {A}, False ~~> A
  ; inl : forall {A B}, A ~~> A + B
  ; inr : forall {A B}, B ~~> A + B
  ; sum_elim : forall {Γ A B C}, Γ * A ~~> C -> Γ * B ~~> C 
     -> Γ * (A + B) ~~> C
  }.

Context `{SumOps}.

Class SumProps : Type :=
  { False_elim_unique : forall {A} (x y : False ~~> A), x == y
  ; sum_elim_inl : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inl) == f
  ; sum_elim_inr : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inr) == g
  }.

End Sum.

Infix "+" := sum : obj_scope.

End Sum.