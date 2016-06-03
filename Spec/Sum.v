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

Context `{SumTys}.

Class SumOps : Type :=
  { False_elim : forall {A}, False ~~> A
  ; inl : forall {A B}, A ~~> A + B
  ; inr : forall {A B}, B ~~> A + B
  ; sum_elim : forall {A B C}, A ~~> C -> B ~~> C -> A + B ~~> C
  }.

Context `{SumOps}.

Class SumProps : Type :=
  { False_elim_unique : forall {A} (x y : False ~~> A), x == y
  ; sum_elim_inl : forall {A B C} (f : A ~~> C) (g : B ~~> C),
      sum_elim f g ∘ inl == f
  ; sum_elim_inr : forall {A B C} (f : A ~~> C) (g : B ~~> C),
      sum_elim f g ∘ inr == g
  }.

End Sum.

Infix "+" := sum : obj_scope.

End Sum.