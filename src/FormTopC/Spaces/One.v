Require Import 
  Algebra.OrderC
  Algebra.FrameC
  Algebra.SetsC
  CMorphisms
  CRelationClasses
  Prob.StdLib
  FormTopC.FormTop
  FormTopC.Locale
  FormTopC.FormalSpace.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope FT.

Definition OnePO : PreOrder :=
  {| PO_car := unit
  ; le := fun _ _ => unit
  |}.

Lemma OnePO_PO : PreO.t (le OnePO).
Proof.
firstorder.
Qed.

Definition OneI := fun _ : OnePO => Empty_set.

Definition OneC (s : OnePO) (ix : OneI s) : Subset OnePO :=
  Empty_set_rect _ ix.

Definition OnePS : PreISpace.t :=
  {| PreISpace.S := OnePO
   ; PreISpace.Ix := OneI
   ; PreISpace.C := OneC
  |}.

Definition OnePos (_ : unit) : Type := unit.

Lemma OnePos_Pos : FormTop.gtPos OnePS.
Proof.
apply gall_Pos. intros.
destruct i.
Qed.

Definition One : IGt :=
  {| IGS := OnePS
   ; IGPO := OnePO_PO
   ; IGpos := OnePos_Pos
  |}.

Lemma split_One :
  forall a U, a <|[One] U -> U tt.
Proof.
intros a U H. induction H.
- destruct a. assumption.
- assumption.
- destruct i.
Qed.


Local Open Scope Subset.

Lemma One_Sat_le :
  forall U V, Sat One U ⊆ Sat One V -> U ⊆ V.
Proof.
  intros U V H. apply Included_impl; intros.
  destruct x. eapply split_One. apply H.
  eapply FormTop.refl. eassumption.
Qed.

Lemma One_Sat_eq :
  forall U V, Sat One U === Sat One V -> U === V.
Proof.
intros U V H. apply Same_set_Included in H.
destruct H.
apply Included_Same_set; apply One_Sat_le;
  assumption.
Qed.

Definition One_cont : Frame.morph (FOps One)
  Frame.type_ops (fun U => U tt).
Proof.
  unshelve eapply Frame.morph_easy.
- eapply Frame.
- eapply Frame.type.
- unfold Proper, respectful. intros.
  apply One_Sat_eq in X. simpl. apply Same_set_iff. assumption.
- simpl. unfold iffT; auto.
- simpl. split; intros X.
  + destruct X. destruct d, d0. destruct l, l0, a, a0.
    auto.
  + destruct X. split; exists tt; (assumption || reflexivity).
- simpl. intros. split; intros X.
  + destruct X. exists i. assumption.
  + destruct X. exists x. assumption.
Qed.

Definition One_type_cmap :
  Frame.cmap Frame.type_ops (FOps One)
  :=
  {| Frame.cont := One_cont |}.

Section PointMap.

Context {A : FormalSpace.t}.


End PointMap.