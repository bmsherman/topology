Require Import 
  Algebra.FrameC
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.Locale
  FormTopC.Bundled
  FormTopC.FormTop
  FormTopC.InfoBase
  CMorphisms.

Coercion FormalSpace.fromIGT : IGT >-> FormalSpace.t.
Local Open Scope FT.

Require Import FormalSpace.

Lemma split_One :
  forall a U, a <|[One] U -> U I.
Proof.
intros. induction X.
- destruct a. assumption.
- assumption.
- destruct i.
Qed.

Local Open Scope Subset.

Lemma One_Sat_le :
  forall U V, Sat One U ⊆ Sat One V -> U ⊆ V.
Proof.
  intros. apply Included_impl; intros.
  destruct x. eapply split_One. apply X.
  eapply FormTop.refl. eassumption.
Qed.

Lemma One_Sat_eq :
  forall U V, Sat One U === Sat One V -> U === V.
Proof.
intros. apply Same_set_Included in X.
destruct X.
apply Included_Same_set; apply One_Sat_le;
  assumption.
Qed.

Require Import Algebra.SetsC
  Prob.StdLib.
    

Definition One_cont : Frame.morph (OA := FOps One)
  (OB := Frame.type_ops) (f := fun U => U I).
Proof.
  unshelve eapply Frame.morph_easy.
- eapply Frame.
- eapply Frame.type.
- unfold Proper, respectful. intros.
  apply One_Sat_eq in X. simpl. apply Same_set_iff. assumption.
- simpl. unfold iffT; auto.
- simpl. split; intros.
  + destruct X. destruct d, d0. destruct l, l0, a, a0.
    auto.
  + destruct X. split; exists I; (assumption || reflexivity).
- simpl. intros. split; intros.
  + destruct X. exists i. assumption.
  + destruct X. exists x. assumption.
Qed.

Definition One_type_cmap :
  Frame.cmap (OA := Frame.type_ops) (OB := FOps One)
  :=
  {| Frame.cont := One_cont |}.

Require Import FormTopC.Cont.


Existing Instances Frame Frame.type
  FOps LOps.
Local Open Scope loc.

Section Approx.

Context {A : IGT}.

Definition framePt (pt : One ~~> A)
  : Frame.point (FOps A) :=
  Frame.cmap_compose
  One_type_cmap (@toCmap One A _ (mp_ok (LA := One) (LB := A) pt)).

Inductive liesIn {pt : One ~~> A} {U : Subset (S A)}
  := MkliesIn : forall u : S A, U u -> mp pt u I -> liesIn.
Arguments liesIn : clear implicits.

Infix "⊧" := liesIn (at level 40).

Lemma liesIn_finv (pt : One ~~> A)
  U : iffT (pt ⊧ U) (Frame.finv (framePt pt) U).
Proof.
split; intros. 
- destruct X. simpl.
  unfold Cont.Cont.frame. exists u; assumption.
- destruct X. econstructor; eauto.
Qed.

Definition evalPt (U : Subset (S A))
  {Ix} (V : Ix -> Subset (S A))
  (pt : One ~~> A)
  : pt ⊧ U
  -> L.le U (Frame.sup V)
  -> {i : Ix & pt ⊧ V i }.
Proof.
intros. 
pose proof (Frame.point_cov (framePt pt) (U := U) (V := V)).
pose proof (liesIn_finv pt U).
destruct X2 as [lf fl].
specialize (X1 X0 (lf X)).
destruct X1.
exists x. apply liesIn_finv. assumption.
Qed.

End Approx.

Inductive Approx {A : IGT} {I : Type} :=
  MkApprox : forall (U : Subset (S A)) (V : I -> Subset (S A))
      , L.le U (Frame.sup V) -> Approx.

Arguments Approx : clear implicits.

Infix "⇓" := Approx (at level 40).