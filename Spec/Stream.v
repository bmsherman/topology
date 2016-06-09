Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Stream.
Section Stream.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Context {Stream : U -> U}.

Class StreamOps : Type :=
  { stream : forall {Γ X A}, Γ ~~> X -> X ~~> A * X -> Γ ~~> Stream A
  ; hd : forall {A}, Stream A ~~> A
  ; tl : forall {A}, Stream A ~~> Stream A
  }.

Context `{StreamOps}.

Class StreamProps : Prop :=
  { stream_hd : forall {Γ X A} (x : Γ ~~> X) (f : X ~~> A * X),
    hd ∘ stream x f == fst ∘ f ∘ x
  ; stream_tl : forall {Γ X A} (x : Γ ~~> X) (f : X ~~> A * X),
    tl ∘ stream x f == stream (snd ∘ f ∘ x) f
  }.

End Stream.

End Stream.