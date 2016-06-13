
Add Rec LoadPath "/Users/Sherman/Documents/Projects/corn/" as CoRN.
Require Import FormTopC.FormTop Algebra.FrameC Algebra.SetsC.
Require Import CoRN.metric2.Metric
  CoRN.model.structures.Qpossec
  Coq.QArith.QArith_base
  CMorphisms.

Set Asymmetric Patterns.
Set Universe Polymorphism.

Module Metric.
Section Metric.

Hypothesis MS : MetricSpace.

Definition M : Type := msp_is_setoid MS.

Definition Ball : Type := (M * Qpos)%type.

Definition lt_ball (Bx By : Ball) : Type :=
  let (x, delta) := Bx in let (y, eps) := By in
  { d : Qpos | ball d x y /\ (d + delta < eps)%Qpos }.

Definition le_ball (Bx By : Ball) : Type :=
  let (x, delta) := Bx in let (y, eps) := By in
  { d : Q | gball d x y /\ d + delta <= eps }.


Instance PreO : PreO.t le_ball.
Proof.
constructor; intros.
- destruct x. unfold le_ball. intros.
  exists 0. simpl. unfold gball. simpl. split.
  reflexivity. ring_simplify. apply Qle_refl. 
- destruct x, y, z. unfold le_ball in *.
  destruct H as (d & mm0 & dq0).
  destruct H0 as (d' & d01 & dq01).
  exists (d + d'). split. 
  eapply gball_triangle; eassumption.
  setoid_replace (d + d' + q) with ((d + q) + d') by ring.
  eapply Qle_trans. apply Qplus_le_compat. eassumption.
  apply Qle_refl. rewrite Qplus_comm. assumption.
Qed.

Definition Ix (_ : Ball) : Type := option Qpossec.Qpos.

Definition C (b : Ball) (i : Ix b) : Subset Ball := 
  match i with
  | None         => fun b' => lt_ball b' b
  | Some epsilon => fun b' => (le_ball b' b
          * (snd b' = epsilon)%Q)%type
  end.

Existing Instance PreO.PreOrder_I.

Local Instance PreOrder_le_ball : Transitive le_ball := 
  PreOrder_Transitive.

Require Import Coq.QArith.Qminmax.

Lemma gball_pos : forall (m : MetricSpace) (e : Qpos) (x y : m),
  ball e x y <-> gball e x y.
Proof.
intros. pose proof (gball_pos (m := m) (proj2_sig e)).
split; intros.
- apply H. apply ball_weak_le with e. simpl. apply Qle_refl.
assumption.
- eapply ball_weak_le. 2: apply <- H.
  simpl. apply Qle_refl. assumption.
Qed.

Require Coq.Classes.CRelationClasses.
Lemma lt_le_trans : forall a b c, 
   lt_ball a b -> le_ball b c -> lt_ball a c.
Proof.
intros. destruct a, b, c. 
unfold lt_ball, le_ball in *. 
destruct H as (d & dmm0 & dqq0).
destruct H0 as (d' & d'm01 & dq01).
Admitted.


Lemma lt_le_weak : forall a b,
  lt_ball a b -> le_ball a b.
Proof.
unfold lt_ball, le_ball.
intros. destruct a, b.
destruct H as (d & b & l).
exists d. split.
apply gball_pos. assumption.
apply Qlt_le_weak. assumption.
Qed.

Theorem loc : @FormTop.localized _ le_ball Ix C.
Proof.
unfold FormTop.localized. intros.
destruct i; simpl.
- exists (Some q). simpl. intros. destruct s. 
  destruct H0. subst. simpl in *.
  exists (m, q0). split. split. 
  eapply transitivity; eassumption. reflexivity.
  split. assumption. apply reflexivity.
- exists None. simpl. intros. 
  exists s. split. eapply lt_le_trans; eassumption.
  split. apply lt_le_weak. assumption. reflexivity.
Qed.

Definition Cov := FormTop.GCov le_ball C.

End Metric.

Section Map.
Require Import FormTopC.Cont CMorphisms.
Require Import CoRN.metric2.UniformContinuity.

Context {X Y : Metric.MetricSpace}.
Delimit Scope uc_scope with uc.
Variable f : (X --> Y)%uc.

Local Open Scope Subset.

Lemma true_union S T (F : S -> Subset T) (t : T) : 
  { x : S & F x t} ->
  union (fun _ => True) F t.
Proof.
intros H. destruct H. econstructor; unfold In; eauto.
Qed.

Lemma true_union' S T (F : S -> Subset T) : 
  (fun t => { x : S & F x t}) ⊆
  union (fun _ => True) F.
Proof.
unfold Included, In, pointwise_rel, arrow.
apply true_union.
Qed.

Definition lift : Cont.map (Ball X) (Ball Y) :=
  fun By Bx => 
  forall x : X, ball (snd Bx) (fst Bx) x -> ball (snd By) (fst By) (f x).

Definition Qpos1 : Qpos.
apply (@mkQpos 1). reflexivity.
Defined.


Definition Qpossmaller (q : QposInf) : Qpos := match q with
  | Qpos2QposInf q' => q'
  | QposInfinity => Qpos1
  end.

Definition Qpossmaller_prf : forall (q : QposInf),
  QposInf_le (Qpossmaller q) q.
Proof.
intros. unfold QposInf_le, Qpossmaller. destruct q; auto.
apply Qle_refl.
Qed.

Existing Instances PreO PreO.PreOrder_I.

Theorem Cont : Cont.t (le_ball X) (le_ball Y)
 (Cov X) (Cov Y) lift.
Proof.
pose proof (uc_prf f) as UC.
constructor; intros.
- unfold Cov.
  pose (q := Qpossmaller (mu f (snd a))).
  apply FormTop.ginfinity with (Some q).
  simpl. intros. destruct H. subst.
  apply FormTop.grefl.
  apply true_union.
  destruct u as (m, q).
  specialize (UC (snd a) m).
  exists (f m, snd a). unfold lift. simpl. 
  intros.
  apply UC. eapply ball_ex_weak_le.
  apply Qpossmaller_prf. simpl in *.
  subst. assumption.
- unfold lift in *. intros.
  apply X0. apply H. assumption.
- destruct a, b, c. 
  pose (eps := QposMinMax.Qpos_min q0 q1).
  pose (delt := Qpossmaller (mu f eps)).
  apply FormTop.ginfinity with (Some delt).
  simpl. intros. destruct u. destruct H. simpl in *. subst.
  apply FormTop.grefl.
  constructor 1 with (f m2, eps).
  + split. unfold lift in X0. simpl in X0.
    unfold le_ball. simpl. unfold le_ball in H. 
    simpl in H.
    assert (q0 + eps = q0)%Qpos as eqprf by admit.
    rewrite <- eqprf.
    intros. eapply ball_triangle. apply X0. apply H.
    apply ball_refl. assumption.
    admit.
  + unfold lift. simpl. intros. 
    apply UC. eapply ball_ex_weak_le. apply Qpossmaller_prf.
    assumption.
- induction X1.
  + apply FormTop.grefl. constructor 1 with a0; auto.
  + apply IHX1. unfold lift.
    intros. apply l. apply X0. assumption.
  + destruct i; simpl in *.
    * apply X1 with (fst a0, q). admit. admit.
    * admit.
Admitted.
End Map.
End Metric.
