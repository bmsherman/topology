Require Import 
  Algebra.OrderC
  Algebra.FrameC
  Algebra.SetsC
  CMorphisms
  CRelationClasses
  Prob.StdLib
  FormTopC.FormTop
  FormTopC.Bundled.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope FT.

Set Printing Universes.

Definition OnePO : PreOrder :=
  {| PO_car := unit
  ; le := fun _ _ => unit
  |}.

Definition OneI := fun _ : OnePO => Empty_set.

Definition OneC (s : OnePO) (ix : OneI s) : Open OnePO :=
  Empty_set_rect _ ix.

Definition OnePS : PreISpace.t :=
  {| PreISpace.S := OnePO
   ; PreISpace.Ix := OneI
   ; PreISpace.C := OneC
  |}.
