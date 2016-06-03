Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Discrete.
Section Defn.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Variable D : Type -> U.

Class DiscreteOps : Type :=
  { func : forall {A B}, (A -> B) -> D A ~~> D B }.

Context `{DiscreteOps}.

Class DiscreteProps : Type :=
  { func_id : forall {A}, func (fun x : A => x) == id
  ; func_compose : forall {A B C} (f : A -> B) (g : B -> C),
     func g ∘ func f == func (fun x => g (f x))
  ; unit_discrete : unit ≅ D True
  ; prod_discrete : forall {A B}, D A * D B ≅ D (A * B)
  ; diagonal_discrete : forall {A}, 
      diagonal == from prod_discrete ∘ func (fun x : A => (x, x))
  ; parallel_discrete : forall {A B X Y} (f : A -> X) (g : B -> Y),
     func f ⊗ func g  == 
     from prod_discrete
     ∘ func (fun p : A * B => let (a, b) := p in (f a, g b))
     ∘ to prod_discrete
  }.

End Defn.
End Discrete.