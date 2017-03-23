Require Import 
  FormTopC.FormTop
  FormTopC.Cont
  Algebra.OrderC
  Numbers.QPosFacts
  CoRN.metric2.Metric
  FormTopC.Metric
  QposMinMax
  QArith.Qminmax
  COrdAbs
  Qordfield
  CoRN.model.metric2.Qmetric
  CoRN.metric2.ProductMetric
  Algebra.SetsC.

Definition unit_RSetoid : RSetoid.
Proof.
refine (
  {| st_car := unit
   ; st_eq := fun _ _ => True |}); firstorder.
Defined. 

(* One-point metric space *)
Definition MOne : MetricSpace.
Proof.
unshelve econstructor.
- exact (unit_RSetoid).
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

Existing Instances PreO PreO.PreOrder_I.

Lemma tt_cont : IGCont.pt Metric (fun _ : Ball MOne => True).
Proof.
constructor.
- exists (tt, Qpos1). unfold In. auto.
- intros. destruct b, c. destruct m, m0.
  exists (tt, Qpos_min q q0). split.
  split; le_down; apply le_ball_center.
  apply Qpos_min_lb_l. apply Qpos_min_lb_r.
  auto.
- auto.
- intros a c ix l H. destruct ix. 
  destruct a, c. destruct H. destruct m, m0.
  simpl.
  + exists (tt, Qpos_min q0 q). split. auto.
    split. le_down. apply le_ball_center. apply Qpos_min_lb_l.
    exists (tt, q). reflexivity.
    apply le_ball_center. apply Qpos_min_lb_r.
  + simpl in *. destruct a, c, H.
    destruct m, m0.
    destruct (Qpos_smaller q).
    exists (tt, x). split. auto.
    split. le_down.
    apply le_ball_center. apply Qlt_le_weak. assumption.
    exists (tt, x). unfold In. apply lt_ball_center.
    apply (@le_ball_radius MOne (tt, q) (tt, q0)) in l. 
    simpl in l.
    eapply Qlt_le_trans; eassumption. reflexivity.
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
  IGCont.t (toPreSpace Metric) Metric 
  (lift (fun _ : MOne => x) Qpos1).
Proof.
apply Cont. apply from_One_lip.
Qed.

End Yoneda.

(** Now let's get to the real numbers. *)

Definition MQ : MetricSpace := Q_as_MetricSpace.

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
eapply ball_weak_le. eapply Qle_eq. simpl. ring_simplify.
reflexivity.
apply Q.max_case_strong.
intros. rewrite <- H1.  assumption.
apply Q.max_case_strong. intros. rewrite <- H1.
auto. auto. intros.
eapply Qball_between.
admit. admit.
apply Q.max_case_strong. intros. rewrite <- H1. auto.
intros. 
admit. 
auto.
Admitted.

Lemma min_Lip : Lipschitz (binop Qmin) Qpos1.
Admitted.