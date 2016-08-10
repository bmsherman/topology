Require Import FormTopC.FormTop Algebra.FrameC
  Algebra.SetsC
  CoRN.metric2.Metric
  FormTopC.Metric.

Require Import Types.Setoid.

Definition Setoid_RSetoid (X : Setoid) : RSetoid :=
  {| st_car := sty X
   ; st_eq := seq X
   ; st_isSetoid := seq_Equivalence X |}.

(* One-point metric space *)
Definition MOne : MetricSpace.
Proof.
unshelve econstructor.
- exact (Setoid_RSetoid unit_Setoid).
- exact (fun _ _ _ => True).
- simpl. intros. split; intros; auto.
- simpl. constructor.
  + unfold Reflexive. auto.
  + unfold Symmetric. auto.
  + auto.
  + auto.
  + simpl. auto.
Defined.

Import Metric.
Require Import FormTopC.Cont.

Require Import QposMinMax.

Existing Instances PreO PreO.PreOrder_I.

Lemma tt_cont : IGCont.pt le_ball C (fun _ : Ball MOne => True).
Proof.
constructor.
- exists (tt, Qpos1). unfold In. auto.
- intros. destruct b, c. destruct m, m0.
  exists (tt, Qpos_min q q0). split. 
  split; apply le_ball_center.
  apply Qpos_min_lb_l. apply Qpos_min_lb_r.
  auto.
- auto.
- intros. destruct i. destruct x. 
  destruct a, x. destruct H. destruct m, m0.
  simpl.
  destruct i; simpl.
  + exists (tt, Qpos_min q q1). split. auto.
    exists (tt, q1). split. reflexivity.
    split; apply le_ball_center. apply Qpos_min_lb_l.
    apply Qpos_min_lb_r.
  + destruct (Qpos_smaller q).
    exists (tt, x). split. auto. 
    exists (tt, x). split. apply lt_ball_center.
    apply le_ball_radius in y. simpl in y.
    eapply Qlt_le_trans; eassumption.
    split. apply le_ball_center. apply Qlt_le_weak.
    assumption. reflexivity.
Qed.

Section Yoneda.
Context {X : MetricSpace}.

Lemma from_One_lip
  (f : MOne -> X) (k : Qpos) : Lipschitz f k.
Proof.
unfold Lipschitz.
simpl. intros. destruct x, x'.
apply ball_refl.
Qed.

(** Applying this map to the unique point in the
    one-point space will give us the point which is
    the embedding of
    [x: X] into its metric completion.
*)
Definition from_One_cont (x : X) :
  IGCont.t le_ball (FormTop.GCovL le_ball CUL)
  le_ball (FormTop.CL le_ball CUL) 
  (lift (fun _ : MOne => x) Qpos1).
Proof.
apply Cont. apply from_One_lip.
Qed.

End Yoneda.

(** Now let's get to the real numbers. *)

Require Import CoRN.model.metric2.Qmetric
  CoRN.metric2.ProductMetric.

Let MQ : MetricSpace := Q_as_MetricSpace.

Definition binop (f : MQ -> MQ -> MQ) (p : ProductMS MQ MQ) : MQ :=
  let (x, y) := p in f x y.

Lemma Qle_eq {x y : Q} : x == y -> x <= y.
Proof.
intros xeqy. rewrite xeqy. reflexivity.
Qed.

Lemma plus_Lip : Lipschitz (binop Qplus) (Qpos1 + Qpos1).
Proof.
unfold Lipschitz. intros. 
destruct x, x', H.
unfold binop.
eapply ball_weak_le.
Focus 2.  eapply Qball_plus; eassumption.
simpl. apply Qle_eq. ring.
Qed.

Require Import QArith.Qminmax COrdAbs.
Require Import Qordfield.

Local Open Scope Q.

(* This lemma is taken from 
  [QboundBelow_uc_prf] here:
  https://github.com/robbertkrebbers/corn/blob/8b864e218dd1a682746c25c4b56e225f120be957/reals/fast/CRGroupOps.v#L396
*)
Lemma Qball_between :
 forall e a b0 b1, Qball e b0 b1 -> b0 <= a <= b1 -> Qball e a b1.
Proof.
  intros e a b0 b1 H [H1 H2].
  unfold Qball in *.
  unfold AbsSmall in *.
  split.
   apply Qle_trans with (b0-b1).
    tauto.
   apply (minus_resp_leEq _ b0).
   assumption.
  apply Qle_trans with 0.
   apply (shift_minus_leEq _ a).
   stepr b1.
    assumption.
   simpl; ring.
  apply Qpos_nonneg.
Qed.


Lemma max_Lip : Lipschitz (binop Qmax) Qpos1.
Proof.
unfold Lipschitz. intros.
destruct x, x', H. unfold binop. simpl.
simpl in *.
simpl in H5, H6.