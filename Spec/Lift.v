(** Definition of "lifted" spaces, which are spaces with a "bottom"
    (think non-termination) element adjoined. *)

Require Import Spec.Category Spec.Stream Spec.Sum.

Import Category.
Import Stream.
Import Sum.
Local Open Scope obj.
Local Open Scope morph.

Module Lift.
Section Lift.

Context `{SOps : StreamOps}.
Context {cmc : CMC U}.
Context `{sumOps : SumOps (U := U) (ccat := ccat)}.
Context {Lift : U -> U}.

Class LiftOps : Type :=
  { strict : forall {A}, A ~~> Lift A
  ; gen_recursion : forall {A}, Stream (unit + A) ~~> Lift A
  }.

Context `{LiftOps}.

Definition sum_elim' {A B C : U} (l : A ~~> C) (r : B ~~> C) 
  : (A + B) ~~> C
  := sum_elim (l ∘ snd) (r ∘ snd) ∘ add_unit_left.

Class LiftProps : Prop :=
  { strict_mono : forall {A}, Mono (strict (A := A))
  ; gen_recursion_tl : forall {A},
    gen_recursion (A := A) == sum_elim fst (strict ∘ snd) 
                              ∘ ((gen_recursion ∘ tl (StreamOps := SOps))  ⊗ hd (StreamOps := SOps)) ∘ diagonal
  } .

End Lift.


End Lift.