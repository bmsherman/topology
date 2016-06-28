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

Class CCCOps : Type :=
  { Func : U -> U -> U
  ; eval : forall {A B}, Func A B * A ~~> B
  ; abstract : forall {Γ A B}, Γ * A ~~> B -> Γ ~~> Func A B
  }.

Context {cccops : CCCOps}.

Class CCCProps : Prop :=
  { eval_abstract : forall {Γ A B} (e : Γ * A ~~> B), 
     eval ∘ (abstract e ⊗ id) == e
  }.

End CCC.

Infix "==>" := Func (at level 55, right associativity) : obj_scope.

End CCC.