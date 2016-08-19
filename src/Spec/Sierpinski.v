Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Sierp.
Section Sierpinski.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Context {Σ : U}.

Class ΣOps : Type :=
  { true : unit ~~> Σ
  ; false : unit ~~> Σ
  ; and : Σ * Σ ~~> Σ
  ; or : Σ * Σ ~~> Σ
(*  ; join : forall {X : Type} X ~> Σ ~~> Σ               *)
  }.

Infix "&&" := (ap2 and) : morph_scope.
Infix "||" := (ap2 or) : morph_scope.

Context `{ΣOps}.

Class ΣProps : Type :=
  { apart : ~ (true == false)
  ; not_false_then_true : forall (y : unit ~~> Σ), ~ (y == false) -> y == true            
  ; and_comm : forall {Γ} (x y : Γ ~~> Σ), (x && y) == (y && x)
  ; or_comm : forall {Γ} (x y : Γ ~~> Σ), (x || y) == (y || x)
  ; and_true : forall {Γ} (x : Γ ~~> Σ), (ap0 true && x) == x
  ; and_false : forall {Γ} (x : Γ ~~> Σ), (ap0 false && x) == ap0 false
  ; or_true : forall {Γ} (x : Γ ~~> Σ), (ap0 true || x) == ap0 true
  ; or_false : forall {Γ} (x : Γ ~~> Σ), (ap0 false || x) == x
  }.

End Sierpinski.

End Sierp.