Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Stream.
Section Stream.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Variable Stream : U -> U.

Class StreamOps : Type :=
  { stream : forall {Γ A}, Γ ~~> A -> A ~~> A -> Γ ~~> Stream A
  ; hd : forall {A}, Stream A ~~> A
  ; tl : forall {A}, Stream A ~~> Stream A
  }.

Context `{StreamOps}.

Class StreamProps : Prop :=
  { stream_hd : forall {Γ A} (x : Γ ~~> A) (f : A ~~> A),
    hd ∘ stream x f == x
  ; stream_tl : forall {Γ A} (x : Γ ~~> A) (f : A ~~> A),
    tl ∘ stream x f == stream (f ∘ x) f
  } .

End Stream.

End Stream.