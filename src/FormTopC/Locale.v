Require Import 
  FormTopC.FormTop
  Algebra.SetsC
  Algebra.OrderC
  Algebra.FrameC
  FormTopC.FormalSpace
  CMorphisms.

Local Open Scope Subset.

Existing Instances FormalSpace.Cov_Proper 
  FormalSpace.Cov_Proper2 
  FormalSpace.Cov_Proper3
  FormalSpace.FT
  FormalSpace.PreO.

Import FormTop.

Section ToFrame.
Variable (A : FormalSpace.t).

Definition T := Subset (S A).

Definition Sat (U : T) : T := fun s => s <|[A] U.

Definition leA (U V : T) : Type := Sat U ⊆ Sat V.

Definition eqA (U V : T) : Type := Sat U === Sat V.

Definition minA (U V : T) : T :=
  downset (le A) U ∩ downset (le A) V.

Inductive supA I (f : I -> T) : T := 
  MksupA : forall i s, f i s -> In (supA I f) s.

Definition LOps : Lattice.Ops T :=
  {| Lattice.le := leA
  ;  Lattice.eq := eqA
  ;  Lattice.max := Union
  ;  Lattice.min := minA
  |}.

Instance LOps' : Lattice.Ops T := LOps.

Definition FOps : @Frame.Ops T := 
  {| Frame.LOps := LOps
   ; Frame.top := fun _ => True
   ; Frame.sup := supA
  |}.

Instance FOps' : @Frame.Ops T := FOps.

Theorem FramePreO : @PreO.t T leA.
Proof.
constructor; unfold leA; intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Theorem FramePO : @PO.t T leA eqA.
Proof.
constructor; unfold eqA; intros.
- apply FramePreO.
- unfold leA. unfold Proper, respectful. 
  intros. rewrite X, X0. reflexivity.
- unfold leA in *. split; intros.
  apply X. assumption. apply X0. assumption.
Qed.

Theorem Sat_Intersection : forall U V,
  Sat (U ∩ V) ⊆ Sat U ∩ Sat V.
Proof.
intros. constructor; unfold Sat, In in *.
  rewrite <- (Intersection_Included_l _ U V); eassumption.
  rewrite <- (Intersection_Included_r _ U V); eassumption.
Qed.

Theorem Sat_Union : forall U V,
  Sat U ∪ Sat V ⊆ Sat (U ∪ V).
Proof.
intros. unfold Included, pointwise_rel, arrow; intros a H. 
destruct H; unfold In, Sat in *. 
rewrite <- Union_Included_l. assumption. 
rewrite <- Union_Included_r. assumption. 
Qed.

Theorem Sat_mono : forall U, U ⊆ Sat U.
Proof.
intros. unfold Included, pointwise_rel, arrow, Sat. 
intros. apply refl. assumption.
Qed.

Theorem Sat_mono2 : forall U V, U ⊆ V -> Sat U ⊆ Sat V.
Proof.
intros U V H. unfold Included, pointwise_rel, arrow, Sat. 
intros a X. rewrite <- H. assumption.
Qed.

Theorem Cov_Sat : forall a U, iffT (a <|[A] U) (a <|[A] Sat U).
Proof.
intros. split; intros. rewrite <- Sat_mono. assumption.
etrans. assumption.
Qed.

Theorem Sat_downset : forall U, Sat U === Sat (downset (le A) U).
Proof.
intros. split.
- apply Sat_mono2. unfold Included, In, downset.
  intros. econstructor. eassumption. reflexivity.
- unfold Included, Sat, In, downset.
  intros H. etrans. destruct H. 
  rewrite l. apply refl. assumption.
Qed.

Existing Instances Union_Proper_le_flip Union_Proper_eq.

Theorem FrameLatt : Lattice.t T LOps.
Proof.
constructor; intros.
- apply FramePO.
- simpl. unfold Proper, respectful, eqA. intros x y H x0 y0 H0.
  split; unfold Included, In, Sat; intros.
  + apply Cov_Sat. rewrite <- Sat_Union.
    rewrite <- H, <- H0.
    rewrite <- !Sat_mono. assumption.
  + apply Cov_Sat. rewrite <- Sat_Union. 
    rewrite H, H0. rewrite <- !Sat_mono. assumption. 
- constructor.
  + simpl. unfold leA. apply Sat_mono2. 
    apply Union_Included_l.
  + simpl. unfold leA. apply Sat_mono2.
    apply Union_Included_r.
  + simpl. unfold leA. intros.
    unfold Sat, Included, pointwise_rel, arrow. 
    intros a H. etrans. rewrite Cov_Sat. destruct H.
    * rewrite <- X, <- Cov_Sat. apply refl. assumption.
    * rewrite <- X0, <- Cov_Sat. apply refl. assumption.
- simpl. unfold Proper, respectful, eqA, minA.
  intros x y H x0 y0 H0.
  apply Included_Same_set.
  + rewrite Sat_Intersection. 
    (* universes broke rewriting
rewrite <- Sat_downset.
    rewrite H, H0. unfold Included, pointwise_rel, arrow; 
    intros a H1.
    destruct H1. unfold Sat, In in *.
    join s s0. assumption.
    *) admit.
  + rewrite Sat_Intersection. 
    (* universes broke rewriting
    rewrite <- !Sat_downset.
    rewrite <- H, <- H0. unfold Included, pointwise_rel, arrow; 
    intros a H1.
    destruct H1. unfold Sat, In in *.
    join s s0; assumption. *)
    admit.
- simpl. constructor; unfold leA, minA; intros.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H.
    etrans. destruct H as (H0 & H1). destruct H0.
    rewrite l0. apply refl. assumption.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H.
    etrans. destruct H as (H0 & H1). destruct H1. 
    rewrite l0. apply refl. assumption.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H. 
    etrans. apply le_right. rewrite Cov_Sat, <- X, <- Cov_Sat.
    apply refl. assumption.
    rewrite Cov_Sat, <- X0, <- Cov_Sat. apply refl.  assumption.
Admitted.

Theorem Frame : @Frame.t T FOps.
Proof.
constructor; intros.
- apply FrameLatt.
- simpl. unfold PreO.top, leA.
  intros. apply Sat_mono2. unfold Included, In, pointwise_rel, arrow. 
  auto.
- simpl. unfold eqA, pointwise_relation. 
  unfold Proper, respectful. intros.
  split; unfold Included, Sat; intros.
  + etrans. destruct X0.
    apply (trans (U := y i)).
    rewrite Cov_Sat, <- (X i), <- Cov_Sat. 
    apply refl. assumption. specialize (X i).
    intros. apply refl. econstructor. eassumption. 
  + etrans. destruct X0.
    apply (trans (U := x i)).
    rewrite Cov_Sat, (X i), <- Cov_Sat.
    apply refl. assumption. intros.
    apply refl. econstructor; eassumption.
- simpl. constructor; unfold leA; intros.
  + apply Sat_mono2. unfold Included, pointwise_rel, arrow; intros. 
    econstructor; eassumption. 
  + unfold Included, Sat, pointwise_rel, arrow; intros.
    etrans. destruct X0. 
    rewrite Cov_Sat, <- (X i), <- Cov_Sat.
    apply refl. assumption.
- simpl. unfold minA, eqA.
  split; apply Sat_mono2.
  + unfold Included, pointwise_rel, arrow. 
    intros a0 H. destruct H as (H & H0).
    destruct H0. destruct i.
    repeat (econstructor; try eassumption).
  + unfold Included, pointwise_rel, arrow. 
    intros a0 H. destruct H. destruct i0.
    constructor. assumption. destruct d0. 
    repeat (econstructor; try eassumption).
Qed. 

End ToFrame.

Section FrameMorphism.

Context {A B : FormalSpace.t}.

Variable F_ : Contmap A B.
Hypothesis cont : Contprf A B F_.

Local Instance POFS : @PO.t (T A) (leA A) (eqA A).
Proof.
eapply FramePO.
Qed.

Local Instance POFT : @PO.t (T B) (leA B) (eqA B).
Proof.
eapply FramePO.
Qed.

Require Import FormTopC.Cont.

Theorem monotone : PreO.morph (leA B) (leA A)
   (Cont.frame F_).
Proof.
unfold PreO.morph. intros. unfold Cont.frame.
simpl. unfold leA, Sat.
unfold Included, pointwise_rel, arrow.
intros a' H. FormTop.trans H.
destruct H as [t' at' Fa't'].
apply (Cont.cov cont _ Fa't'). apply X. unfold Sat.
apply FormTop.refl. assumption.
Qed.


Require Import CMorphisms.

Theorem Sat_Proper : forall A,
  Proper (Same_set ==> Same_set) (Sat A).
Proof.
intros. unfold Proper, respectful. intros. unfold Sat.
apply Same_set_iff. intros. apply FormTop.subset_equiv.
assumption.
Qed.

Existing Instances FormTop.Cov_Proper union_Proper.

(** This shouldn't be necessary. It should essentially
    follow from union_Proper. *)
Local Instance union_Proper_flip : 
  forall A B, Proper ((@Included A) --> eq ==> flip (@Included B)) union.
Proof.
intros. unfold Proper, respectful; intros. subst. 
apply union_Proper. assumption. reflexivity.
Qed.

Theorem toLattice : 
   L.morph (LOps B) (LOps A) (Cont.frame F_).
Proof.
constructor.
  + constructor.
     * apply monotone.
     * repeat intro. split; apply monotone; simpl in X;
       rewrite X; apply PreO.le_refl.
  + intros. unfold Cont.frame. simpl. unfold eqA.
    eapply Sat_Proper; try eassumption.
    symmetry. apply Union_union.
  + intros. unfold Cont.frame. simpl. apply PO.le_antisym;
    unfold leA, Sat, Included, pointwise_rel, arrow; intros.
    * FormTop.trans X. unfold minA in X.
      destruct X. destruct i. destruct d, d0.
      unfold minA.
      apply FormTop.le_right;
      apply (Cont.cov cont _ f).
      apply FormTop.le_left with a2. assumption.
      apply FormTop.refl. assumption.
      apply FormTop.le_left with a3. assumption.
      apply FormTop.refl. assumption.
    * FormTop.trans X. unfold minA in *.
      destruct X. destruct d, d0. destruct i, i0.
      rewrite <- FormTop.down_downset; try eassumption.
      apply (Cont.local (CovT := Cov B) (leS := le A)). eassumption. 
      eapply Cont.le_left with a1; eassumption.
      eapply Cont.le_left with a2; eassumption.
Qed.

Theorem toFrame : Frame.morph 
  (OA := (FOps B)) (OB := (FOps A)) (f := (Cont.frame F_)).
Proof.
constructor.
- apply toLattice.
- unfold Cont.frame. simpl. intros.
  unfold eqA. eapply Sat_Proper; try eassumption.
  intros; split; unfold Included, In; intros.
  + destruct X. destruct i. repeat econstructor; eauto.
  + destruct X. destruct u. repeat econstructor; eauto. 
- unfold Cont.frame. simpl. unfold eqA, Sat.
  intros. split; unfold Included, In; intros.
  + apply FormTop.refl. unfold In. auto.
  + pose proof (Cont.here cont a).
    FormTop.ejoin. FormTop.etrans.
    destruct X1.  destruct d, d0.
    destruct i0. clear i i0. clear l.
    rewrite l0. apply FormTop.refl.
    repeat (econstructor; try eassumption).
Qed.

Definition toCmap : Frame.cmap (OA := FOps A)
  (OB := FOps B) :=
  {| Frame.finv := Cont.frame F_
   ; Frame.cont := toFrame |}.

End FrameMorphism.