Require Import 
  Algebra.FrameC
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  FormTopC.Locale
  FormTopC.FormTop
  FormTopC.InfoBase
  FormTopC.FormalSpace
  CMorphisms
  Prob.StdLib
  FormTopC.Spaces.One.

Set Universe Polymorphism.

Local Open Scope FT.

Require Import FormalSpace.


Local Open Scope Subset.

Require Import FormTopC.Cont.


Existing Instances Frame Frame.type
  FOps LOps.
Local Open Scope loc.

Section Approx.

Context {A : t}.

Definition framePt (pt : One ~~> A)
  : Frame.point (FOps A) :=
  Frame.cmap_compose
  One_type_cmap (@toCmap One A _ (mp_ok (LA := One) (LB := A) pt)).

Inductive liesIn {pt : One ~~> A} {U : Subset (S A)}
  := MkliesIn : forall u : S A, U u -> mp pt u tt -> liesIn.
Arguments liesIn : clear implicits.

Infix "⊧" := liesIn (at level 40).

Lemma liesIn_finv (pt : One ~~> A)
  U : iffT (pt ⊧ U) (Frame.finv (framePt pt) U).
Proof.
split; intros H. 
- destruct H. simpl.
  unfold Cont.Cont.frame. exists u; assumption.
- destruct H. econstructor; eauto.
Qed.

Definition evalPt (U : Subset (S A))
  {Ix} (V : Ix -> Subset (S A))
  (pt : One ~~> A)
  : pt ⊧ U
  -> L.le U (Frame.sup V)
  -> {i : Ix & pt ⊧ V i }.
Proof.
intros X X0. 
pose proof (Frame.point_cov (framePt pt) (U := U) (V := V)) as X1.
pose proof (liesIn_finv pt U) as X2.
destruct X2 as [lf fl].
specialize (X1 X0 (lf X)).
destruct X1.
exists x. apply liesIn_finv. assumption.
Qed.

End Approx.

Inductive Approx {A : t} {I : Type} :=
  MkApprox : forall (U : Subset (S A)) (V : I -> Subset (S A))
      , L.le U (Frame.sup V) -> Approx.

Arguments Approx : clear implicits.

Infix "⇓" := Approx (at level 40).