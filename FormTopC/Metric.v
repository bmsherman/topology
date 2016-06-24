Require Import FormTopC.FormTop Algebra.FrameC Algebra.SetsC.

Set Asymmetric Patterns.
Set Universe Polymorphism.

Add Rec LoadPath "/Users/Sherman/Documents/Projects/corn/" as CoRN.
Require Import CoRN.metric2.Metric
  CoRN.model.structures.Qpossec
  Coq.QArith.QArith_base
  CMorphisms.
Require Import CoRN.model.structures.QposInf.

(** Positive upper-real numbers *)

Module PosUR.

(** I get a Coq error with using the typeclasses
    if I leave le as returning Prop *)
Definition le (x y : QposInf) : Type := QposInf_le x y.

Local Infix "<=" := le.

Definition lt (x y : QposInf) : Type :=
  ((x <= y) * ((y <= x) -> False))%type.

Local Infix "<" := lt.

Definition Ix (x : QposInf) : Type := unit.

Definition C (q : QposInf) (_ : Ix q) : Subset QposInf
  := fun q' => lt q' q.

Instance PO : PreO.t le.
Proof.
constructor; unfold le; intros.
- destruct x; simpl. apply Qle_refl. constructor.
- destruct x, y, z; simpl in *; try (constructor || contradiction).
 eapply Qle_trans; eassumption.
Qed.

Existing Instance PreO.PreOrder_I.

Lemma lt_le_trans (x y z : QposInf) : x < y -> y <= z -> x < z.
Proof.
unfold lt in *. 
intros P Q. destruct P as (P1 & P2). split.
etransitivity; eassumption.
intros.  apply P2. etransitivity; eassumption.
Qed.

Lemma lt_le_weak (x y : QposInf) : x < y -> x <= y.
Proof.
intros H. destruct H. assumption.
Qed. 

Definition loc : FormTop.localized le C.
Proof.
unfold FormTop.localized.
intros. exists tt. unfold C. intros.
exists s. split. eapply lt_le_trans; eassumption.
split. apply lt_le_weak. assumption. 
reflexivity.
Qed.

Definition fromQpos (x : Qpos) (y : QposInf) := x < y.

Require Import FormTopC.Cont.

Definition Pt := IGCont.pt le C.

Definition Qpos_two : Qpos := Qpos_one + Qpos_one.

Definition Qpos_one_half : Qpos := Qpos_one / Qpos_two.

Definition Qpos_smaller (x : Qpos) : { y : Qpos & y < x }.
Proof.
exists (Qpos_mult Qpos_one_half x).
unfold lt. split. unfold le.
simpl. setoid_replace (x : Q) with (Qmult 1%Q (x : Q)) at 2 by ring.
apply Qmult_le_compat_r.
ring_simplify. apply Qle_shift_inv_r. reflexivity.
unfold Qle, Z.le. simpl. unfold not. intros. inversion H.
apply Qlt_le_weak. apply Qpos_prf.
intros.
admit. (* I am lazy *)
Admitted.

Definition QposInf_smaller (x : QposInf) : { y : Qpos & y < x }.
Proof.
destruct x.
- apply Qpos_smaller.
- exists Qpos_one. unfold lt. simpl. auto.
Qed.

Lemma Qpos_plus_lt (x y : Qpos) : x < x + y.
Proof.
unfold lt. split.
- unfold le. simpl.
  setoid_replace (x : Q) with (x + 0)%Q at 1.
  apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak.
  apply Qpos_prf. ring.
- unfold le. simpl. 
  setoid_replace (x : Q) with (x + 0)%Q at 2 by ring.
  intros. apply Q.Qplus_le_r in H.
  eapply Qlt_not_le. 2:eassumption. apply Qpos_prf.
Qed.

Lemma QposInf_between (x y : QposInf) : x < y ->
  { z : QposInf & ((x < z) * (z < y))%type }.
Admitted.

Definition Qpos_pt (x : Qpos) : Pt (fromQpos x).
Proof.
constructor; intros.
- exists (x + 1)%Qpos. unfold In, fromQpos.
  apply Qpos_plus_lt.
- exists (QposInf_min b c). constructor.
  constructor. apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  unfold fromQpos in *.
  admit.
- unfold fromQpos in *. eapply lt_le_trans; eassumption.
- destruct i. unfold fromQpos in *. unfold C.
  destruct (QposInf_between x a X).
  destruct p. exists x0. split; assumption.
Abort.

Definition URzero (x : QposInf) : Type := unit.

Definition URzero_pt : Pt URzero.
Proof.
constructor; intros.
- exists 1%Qpos. constructor.
- exists (QposInf_min b c). constructor.
  constructor.  apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  constructor.
- constructor.
- destruct i. destruct (QposInf_smaller a).
  exists x. split. constructor. assumption.
Qed.

Inductive URinfty : QposInf -> Type :=
  MkURinfty : URinfty QposInfinity.

Definition URinfty_pt : Pt URinfty.
Proof.
constructor; intros.
- exists QposInfinity. constructor.
- exists (QposInf_min b c). constructor.
  constructor.  apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  destruct X, X0. simpl. constructor.
- destruct X. destruct b; simpl in *. contradiction. 
  econstructor.
- destruct i. exists QposInfinity. split. constructor.
  unfold C.
  (* I need to change my definition of lt or of C so that
     this doesn't happen. *)
Abort. 


End PosUR.

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
  apply X0. admit. (* apply H. assumption. *)
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
