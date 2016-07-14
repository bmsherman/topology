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

Definition Qpos_two : Qpos := Qpos_one + Qpos_one.

Definition Qpos_one_half : Qpos := Qpos_one / Qpos_two.

Lemma one_half_sum_one : Qpos_one_half + Qpos_one_half == 1.
Proof.
reflexivity.
Qed.

Lemma one_half_sum : forall e,
  (Qpos_one_half * e)%Qpos + (Qpos_one_half * e)%Qpos == e.
Proof.
intros. simpl. rewrite <- Qmult_plus_distr_l.
rewrite one_half_sum_one. apply Qmult_1_l.
Qed.

Definition Qpos_smaller (x : Qpos) : { y : Qpos & y < x }.
Proof.
exists (Qpos_mult Qpos_one_half x).
unfold lt.
simpl. 
setoid_replace (x : Q) with (Qmult 1%Q (Qmult 1%Q (x : Q))) at 2 by ring.
rewrite (Qmult_comm 1).
rewrite <- Qmult_assoc. apply Qmult_lt_compat_r.
ring_simplify. apply Qpos_prf.
reflexivity.
Qed.

Definition Qpos_larger (x : Qpos) : { y : Qpos & x < y }.
Proof.
exists (x + x)%Qpos. 
setoid_replace (x : Q) with (0 + x)%Q at 1 by ring.
simpl. apply Qplus_lt_l. apply Qpos_prf.
Qed.

Require Import Numbers.QFacts.

Definition Qpos_between {x y : Qpos} :
  x < y -> { mid : Qpos & x < mid /\ mid < y }.
Proof.
intros H.
destruct (Qbetween x y H) as (mid & midl & midh).
assert (0 < mid) as H'.
eapply Qlt_trans. apply Qpos_prf. apply midl.
exists (exist _ mid H'). simpl. split; assumption.
Qed.

Module PosUR.

(** I get a Coq error with using the typeclasses
    if I leave le as returning Prop *)
Definition le (x y : QposInf) : Type := QposInf_le x y.

Local Infix "<=" := le.

Definition lt (x y : QposInf) : Type :=
  ((x <= y) * ((y <= x) -> False))%type.

Local Infix "<" := lt.

Definition Ix (x : QposInf) : Type := match x with
  | Qpos2QposInf x => unit
  | QposInfinity => False
  end.

Definition C (q : QposInf) : Ix q -> Subset QposInf
  := match q with
  | Qpos2QposInf x => fun _ q' => lt q' x
  | QposInfinity => False_rect _
  end.

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
intros. destruct c; simpl.
- destruct a. 
  + exists tt. unfold C. intros.
  exists s. split. eapply lt_le_trans; eassumption.
  split. apply lt_le_weak. assumption. 
  reflexivity.
  + inversion X.
- destruct i.
Qed.

Definition fromQpos (x : Qpos) (y : QposInf) := x < y.

Require Import FormTopC.Cont.

Definition Pt := IGCont.pt le C.

Lemma Qpos_lt_equiv (x y : Qpos) :
  iffT (x < y) (x < y)%Q.
Proof.
split; intros.
- destruct X. simpl in *. apply Qnot_le_lt.
  unfold not; intros contra. apply f.
  unfold le. simpl. apply contra.
- split. apply Qlt_le_weak. assumption.
  intros. pose proof (Qlt_not_le _ _ H).
  apply H0. assumption.
Qed.

Definition Qpos_smaller' (x : Qpos) : { y : Qpos & y < x }.
Proof.
destruct (Qpos_smaller x) as [x' prf].
exists x'. apply Qpos_lt_equiv. apply prf.
Qed.

Definition QposInf_smaller (x : QposInf) : { y : Qpos & y < x }.
Proof.
destruct x.
- apply Qpos_smaller'.
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

Ltac inv H := inversion H; clear H; subst.

Lemma QposInf_between (x y : QposInf) : x < y ->
  { z : QposInf & ((x < z) * (z < y))%type }.
Proof.
intros H. destruct x, y.
Admitted.

Definition Qpos_pt (x : Qpos) : Pt (fromQpos x).
Proof.
constructor; intros.
- exists (x + 1)%Qpos. unfold In, fromQpos.
  apply Qpos_plus_lt.
- exists (QposInf_min b c). constructor.
  constructor. apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  unfold fromQpos in *.
  unfold QposInf_min. destruct b.
  + destruct c.
    apply QposMinMax.Qpos_min_case; intros; assumption.
    assumption.
  + assumption.
- unfold fromQpos in *. eapply lt_le_trans; eassumption.
- destruct a. 
  + destruct i. unfold fromQpos in *. unfold C.
    destruct (QposInf_between x q X).
    destruct p. exists x0. split; assumption.
  + destruct i.
Qed.


Definition URzero (x : QposInf) : Type := unit.

Definition URzero_pt : Pt URzero.
Proof.
constructor; intros.
- exists 1%Qpos. constructor.
- exists (QposInf_min b c). constructor.
  constructor.  apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  constructor.
- constructor.
- destruct a. 
  + destruct i. destruct (QposInf_smaller q).
  exists x. split. constructor. assumption.
  + destruct i.
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
- destruct a. 
  + destruct i. exists QposInfinity. split. constructor.
  simpl. inversion X. 
  + exists QposInfinity. split. assumption. destruct i.
Qed.

Record pt :=
  { LT :> Subset QposInf
  ; LT_pt : PosUR.Pt LT
  }.

Definition Cov := FormTop.GCov le C.

Local Open Scope Subset.

Definition pt_le (x y : pt) := forall q, LT x q -> Cov q (LT y).

Definition pt_eq (x y : pt) := (pt_le x y * pt_le y x)%type.
Definition zero : pt :=
  {| LT := URzero ; LT_pt := URzero_pt |}.

End PosUR.

Module Metric.
Section Metric.

(*
Variable X : Type.

Variable d : X -> X -> PosUR.pt.
Hypothesis d_refl : forall x : X, PosUR.pt_eq (d x x) PosUR.zero.
Hypothesis d_triangle : forall x y z : X,
*)

Hypothesis MS : MetricSpace.

Definition M : Type := msp_is_setoid MS.

Definition Ball : Type := (M * Qpos)%type.

Definition lt_ball (Bx By : Ball) : Type :=
  let (x, delta) := Bx in let (y, eps) := By in
  { d : Qpos | ball d x y /\ (d + delta < eps)%Qpos }.

Definition le_ball (Bx By : Ball) : Type := 
  let (y, eps) := By in
  forall e : Qpos, lt_ball Bx (y, e + eps)%Qpos.

Instance PreO : PreO.t le_ball.
Proof.
constructor; intros.
- destruct x. unfold le_ball. intros.
  destruct (Qpos_smaller e) as [e' eprf].
  exists e'. split. apply ball_refl. apply Qplus_lt_l. assumption.
- destruct x, y, z. unfold le_ball in *.
  intros e.
  specialize (H (Qpos_one_half * e)%Qpos).
  specialize (H0 (Qpos_one_half * e)%Qpos).
  destruct H as (d & balld & dlt).
  destruct H0 as (d' & balld' & d'lt).
  exists (d + d')%Qpos. split. eapply ball_triangle; eassumption.
  simpl. rewrite (Qplus_comm d d'), <- Qplus_assoc.
  eapply Qlt_le_trans.
  apply Qplus_lt_r. apply dlt. simpl.
  rewrite (Qplus_comm _ q0), Qplus_assoc. 
  eapply Qle_trans. apply Qplus_le_l.
  apply Qlt_le_weak. eassumption. simpl.
  rewrite Qplus_comm, Qplus_assoc.
  rewrite (one_half_sum e). apply Qle_refl.
Qed.


Existing Instance PreO.PreOrder_I.

Local Instance PreOrder_le_ball : Transitive le_ball := 
  PreOrder_Transitive.

Require Import Coq.QArith.Qminmax.


Lemma lt_le_weak : forall a b,
  lt_ball a b -> le_ball a b.
Proof.
unfold lt_ball, le_ball.
intros. destruct a, b.
destruct H as (d & b & l).
intros.
exists d. split. assumption.
eapply Qlt_le_trans. eassumption.
setoid_replace (q0 : Q) with (0 + q0)%Q at 1 by ring.
apply Qplus_le_l. apply Qlt_le_weak. apply Qpos_prf.
Qed.

Lemma lt_le_trans : forall a b c, 
   lt_ball a b -> le_ball b c -> lt_ball a c.
Proof.
intros. destruct a, b, c. 
unfold lt_ball, le_ball in *. 
destruct H as (d & dmm0 & dqq0).
destruct (Qpos_lt_plus dqq0) as [e eprf].
specialize (H0 e%Qpos).
destruct H0 as (d' & balld' & dd').
exists (d + d')%Qpos. split.
eapply ball_triangle; eassumption.
rewrite eprf in dd'.
apply (Qplus_lt_r _ _ e).
eapply Qlt_compat. 3: apply dd'.
simpl. ring. 
reflexivity.
Qed.

Lemma le_lt_trans : forall a b c,
  le_ball a b -> lt_ball b c -> lt_ball a c.
Proof.
intros. destruct a, b, c.
unfold lt_ball, le_ball in *.
destruct H0 as (d & dmm0 & dqq0).
destruct (Qpos_lt_plus dqq0) as [e eprf].
specialize (H e).
destruct H as (d' & balld' & dd').
exists (d' + d)%Qpos. split. 
eapply ball_triangle; eassumption.
rewrite eprf in dqq0. rewrite eprf.
clear eprf q1.
rewrite <- Qplus_assoc. rewrite (Qplus_comm q0 e).
simpl. rewrite <- (Qplus_assoc d' d q).
rewrite Qplus_comm. rewrite <- (Qplus_assoc d q d').
apply Qplus_lt_r. rewrite Qplus_comm. assumption.
Qed.

Lemma le_ball_applies {a c} : 
  le_ball a c
  -> forall x, ball (snd a) (fst a) x
  -> ball (snd c) (fst c) x.
Proof.
unfold le_ball. intros. destruct a, c.
simpl in *. apply ball_closed.
intros. 
specialize (H d). destruct H as (d' & balld' & qd').
apply ball_weak_le with (d' + q)%Qpos. 
apply Qlt_le_weak.
simpl. rewrite (Qplus_comm q0 d). assumption.
eapply ball_triangle. eapply ball_sym. eassumption.
assumption. 
Qed.

Lemma lt_ball_center : forall x (eps eps' : Qpos),
  eps < eps' -> lt_ball (x, eps) (x, eps').
Proof.
intros. unfold lt_ball.
destruct (Qpos_lt_plus H).
destruct (Qpos_smaller x0) as [x0' x0'small].
exists x0'. split. apply ball_refl.
rewrite Qplus_comm. rewrite q.
apply Qplus_lt_r. assumption.
Qed.

Lemma le_ball_center : forall x (eps eps' : Qpos),
  eps <= eps' -> le_ball (x, eps) (x, eps').
Proof.
intros. simpl. intros.
destruct (Qpos_smaller e) as [e' e'prf].
exists e'. split. apply ball_refl.
apply Qplus_lt_le_compat; assumption.
Qed.

Lemma lt_ball_shrink : forall Bx y eps,
  lt_ball Bx (y, eps)
  -> {eps' : Qpos & ((eps' < eps) * lt_ball Bx (y, eps'))%type }.
Proof.
intros. destruct Bx. destruct H. destruct a.
destruct (@Qpos_between (x + q)%Qpos eps H0).
destruct a.
exists x0. split. assumption. simpl.
exists x.  split. assumption. assumption.
Qed.

Lemma Qpos_one_half_lt : forall (x : Qpos),
  (Qpos_one_half * x)%Qpos < x.
Proof.
intros. rewrite <- (Qplus_0_r).
rewrite <- (one_half_sum x). 
apply Qplus_lt_r. apply Qpos_prf. 
Qed. 

Lemma lt_ball_grow : forall x delta By,
  lt_ball (x, delta) By
  -> { delta' : Qpos & ((delta < delta') * lt_ball (x, delta') By)%type }.
Proof.
intros. destruct By. destruct H as (d & balld & dlt).
destruct (Qpos_lt_plus dlt).
exists (delta + Qpos_one_half * x0)%Qpos. split.
  rewrite <- (Qplus_0_r delta) at 1. simpl. 
  apply Qplus_lt_r. apply (Qpos_prf (Qpos_one_half * x0)%Qpos).
  simpl. exists d. split.  assumption.
  rewrite q0. rewrite Qplus_assoc. apply Qplus_lt_r.
  apply Qpos_one_half_lt.
Qed.
   

Lemma Qlt_all_Qle (x y : Q) :
  (forall (eps : Qpos), x < y + eps) -> x <= y.
Proof.
intros H.
destruct (Qlt_le_dec y x); try assumption.
exfalso. 
destruct (Qpos_lt_plus q).
specialize (H x0).
rewrite q0 in H.
apply Qplus_lt_l in H.
eapply Qlt_irrefl. eassumption.
Qed.

Lemma Qadd_lt x y (eps : Qpos) : eps + x < y -> x < y.
Proof.
intros H.
setoid_replace (x : Q) with (0 + x) at 1 by ring.
eapply Qle_lt_trans. 2: eassumption.
apply Qplus_le_l. apply Qlt_le_weak.
apply Qpos_prf.
Qed.


Lemma lt_ball_radius x y (ex ey : Qpos)
  : lt_ball (x, ex) (y, ey) -> ex < ey.
Proof.
simpl. intros. destruct H as (d & bd & exey).
eapply Qadd_lt. eassumption.
Qed.

Lemma le_ball_radius {Bx By} :
  le_ball Bx By -> snd Bx <= snd By.
Proof.
destruct Bx, By. simpl. intros H.
apply Qlt_all_Qle.
intros. destruct (H eps). destruct a.
rewrite Qplus_comm. eapply Qadd_lt.
eassumption.
Qed.

Definition Ix (x : Ball) : Type := 
  option Qpos.

Definition C (b : Ball) (i : Ix b) : Subset Ball := 
  match i with
  | None         => fun b' => lt_ball b' b
  | Some epsilon => fun b' => snd b' = epsilon
  end.

(*
Theorem loc : @FormTop.localized _ le_ball Ix C.
Proof.
unfold FormTop.localized. intros.
destruct i; simpl.
- destruct s.
  pose proof (le_ball_radius H).
  assert (QposMinMax.Qpos_min x (snd a) <= snd a).
  apply QposMinMax.Qpos_min_lb_r.
  exists (Some (exist (fun q : Qpos => q <= snd a) _ H1)).
  simpl. intros.
  destruct H2. destruct s. simpl in *. subst.
  induction (QposMinMax.Qpos_min x (snd a)) 
     using (QposMinMax.Qpos_min_case x (snd a)).
  +  exists (m, x). split.  split. etransitivity; eassumption.
     reflexivity.
     split.  eassumption. reflexivity.
  + exists a. split. 
  exists (m, x). split. 
  exists (m, x). split. split. 
  apply lt_ball_radius. 
  exists (Some q). simpl. intros. destruct s. 
  destruct H0. subst. simpl in *.
  exists (m, q0). split. split. 
  eapply transitivity; eassumption. reflexivity.
  split. assumption. apply reflexivity.
- exists None. simpl. intros. 
  exists s. split. eapply lt_le_trans; eassumption.
  split. apply lt_le_weak. assumption. reflexivity.
Qed.
*)

Definition Cov := FormTop.GCov le_ball C.

End Metric.

Section Map.
Require Import FormTopC.Cont CMorphisms.
Require Import CoRN.metric2.UniformContinuity.

(** In an open ball *)
Inductive o_ball {X : MetricSpace} {eps : Qpos} {a b : X} : Type :=
  In_o_ball : forall e : Qpos, e < eps -> ball e a b -> o_ball.

Arguments o_ball {X} eps a b : clear implicits.

Lemma o_ball_ball {X : MetricSpace} eps (a b : X) 
  : o_ball eps a b -> ball eps a b.
Proof.
intros H. induction H.
eapply ball_weak_le. apply Qlt_le_weak. eassumption. 
assumption.
Qed.

Lemma le_ball_applies_o {X : MetricSpace} {a c : Ball X} : 
  le_ball _ a c
  -> forall x, o_ball (snd a) (fst a) x
  -> o_ball (snd c) (fst c) x.
Proof.
intros. 
destruct a, c. simpl in *. induction H0.
destruct (Qpos_lt_plus q1) as (diff & diffeq).
destruct (H diff) as (d & balld & dlt).
econstructor.
Focus 2. eapply ball_triangle. apply ball_sym.
eassumption. eassumption.
rewrite diffeq in dlt.
apply Qplus_lt_r with diff.
eapply Qlt_compat. 3: apply dlt.
simpl. ring. reflexivity.
Qed.


Lemma true_union S T (F : S -> Subset T) (t : T) : 
  { x : S & F x t} ->
  union (fun _ => True) F t.
Proof.
intros H. destruct H. econstructor; unfold In; eauto.
Qed.

Local Open Scope Subset.

Lemma true_union' S T (F : S -> Subset T) : 
  (fun t => { x : S & F x t}) ⊆
  union (fun _ => True) F.
Proof.
unfold Included, In, pointwise_rel, arrow.
apply true_union.
Qed.

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

Section Lipschitz.

Context {X Y : MetricSpace}.
Variable f : X -> Y.
Hypothesis f_lip : forall x x' eps, ball eps x x' -> ball eps (f x) (f x').

Lemma lt_monotone : forall x x' eps eps',
  lt_ball _ (x, eps) (x', eps') ->
  lt_ball _ (f x, eps) (f x', eps').
Proof.
simpl. intros.
destruct H as (d & bd & dlt).
exists d.  split. apply f_lip. assumption. assumption.
Qed.

Lemma le_monotone : forall x x' eps eps',
  le_ball _ (x, eps) (x', eps')
  -> le_ball _ (f x, eps) (f x', eps').
Proof.
intros. unfold le_ball. intros.
apply lt_monotone. apply H.
Qed.

Definition lift : Cont.map (Ball X) (Ball Y) := fun By Bx =>
  let (x, delta) := Bx in lt_ball _ (f x, delta) By.


Lemma lift_f_ap_lt : forall x (eps eps' : Qpos),
  eps < eps' -> lift (f x, eps') (x, eps).
Proof.
intros. 
simpl. destruct (Qpos_lt_plus H).
exists (Qpos_one_half * x0)%Qpos. split. apply ball_refl. rewrite q.
rewrite Qplus_comm. apply Qplus_lt_r. 
apply Qpos_one_half_lt.
Qed.

Lemma lift_f_le {a b u} : lift b a ->
   le_ball X u a
  -> lift b u.
Proof.
intros. destruct a, b, u.
unfold lift in *. eapply le_lt_trans. apply le_monotone. 
eassumption. assumption.
Qed.

Existing Instance PreO.

Theorem Cont : IGCont.t (le_ball X) 
  (FormTop.GCovL (le_ball X) (C X)) (le_ball Y)
 (FormTop.CL (le_ball Y) (C Y)) lift.
Proof.
constructor; intros.
- apply FormTop.glrefl. apply true_union'.
  destruct a. exists (f m, q + q)%Qpos. simpl.
  destruct (Qpos_smaller q).
  exists x. split. apply ball_refl.
  apply Qplus_lt_l. assumption.
- unfold lift in H, H0. destruct a.
  destruct b, c.
  pose proof (lt_ball_shrink _ _ _ _ H).
  destruct H1. destruct p. clear H.
  pose proof (lt_ball_shrink _ _ _ _ H0).
  destruct H. destruct p.  clear H0.
  destruct (Qpos_lt_plus q2).
  destruct (Qpos_lt_plus q3).
  destruct (Qpos_smaller (QposMinMax.Qpos_min x1 x2)).
  apply (fun U => FormTop.gle_infinity (Ix X) (C X) (m, q) 
  U (m, q) (Some x3) (PreO.le_refl (m, q))).
  intros. destruct X0. simpl in p. destruct p. subst.
  destruct d.
  destruct u.
  apply FormTop.glrefl.
  exists (f m2, (QposMinMax.Qpos_min x1 x2)).
  split.

  simpl. intros. destruct l as (d & balld & dlt).
  exists (e + q + d)%Qpos. split. Focus 2. 
  rewrite q4. simpl. rewrite <- !Qplus_assoc. 
  apply Qplus_lt_r. rewrite Qplus_assoc.
  eapply Qplus_lt_le_compat. rewrite Qplus_comm. assumption.
  apply QposMinMax.Qpos_min_lb_l.
  destruct (l1 e). destruct a. 
  eapply ball_triangle. 2:eassumption.
  eapply ball_weak_le. 2: eapply f_lip. 2: eassumption.
  etransitivity. Focus 2. apply Qlt_le_weak.
  eassumption. rewrite <- (Qplus_0_r x3) at 1.
  apply Qplus_le_r. apply Qlt_le_weak. apply Qpos_prf.

  simpl. intros. destruct l0 as (d & balld & dlt).
  exists (e + q + d)%Qpos. split. Focus 2. 
  rewrite q5. simpl. rewrite <- !Qplus_assoc. 
  apply Qplus_lt_r. rewrite Qplus_assoc.
  eapply Qplus_lt_le_compat. rewrite Qplus_comm. assumption.
  apply QposMinMax.Qpos_min_lb_r.
  destruct (l1 e). destruct a. 
  eapply ball_triangle. 2: eassumption.
  eapply ball_weak_le. 2: (eapply f_lip; eassumption).
  etransitivity. Focus 2. apply Qlt_le_weak.
  eassumption. rewrite <- (Qplus_0_r x3) at 1.
  apply Qplus_le_r. apply Qlt_le_weak. apply Qpos_prf.  

  apply lift_f_ap_lt. eapply Qle_lt_trans. 
  eapply (le_ball_radius _ l2). assumption.
- unfold lift in *. destruct a, c.
  eapply le_lt_trans. 2: eassumption.
  eapply le_monotone. assumption.
- destruct a. unfold lift. unfold lift in H. 
    eapply lt_le_trans; eassumption.
- destruct j; simpl in *. destruct x.
  destruct i.
  + simpl. clear x y. destruct (Qpos_smaller q).
    apply (FormTop.gle_infinity (Ix X) (C X) a _ a (Some x)).
    reflexivity.
    intros. destruct X0. simpl in p.
    destruct p. subst. destruct d.
    pose proof (lift_f_le H l). clear a H l.
    destruct (Qpos_between q0). destruct a.
    destruct u. unfold lift in H0.
    pose proof (lt_ball_grow _ _ _ _ H0).
    destruct H2 as (del' & q1del & lt_del').
    
    apply FormTop.glrefl.
    exists (f m, QposMinMax.Qpos_min x del'). unfold In.
    exists (f m, q). split.  reflexivity. destruct b. 
    split. eapply lt_le_weak. eapply le_lt_trans. 2: eassumption. 
    apply le_ball_center. apply QposMinMax.Qpos_min_lb_r.
    apply le_ball_center. etransitivity. 
    apply QposMinMax.Qpos_min_lb_l. apply Qlt_le_weak.
    assumption.

    apply lift_f_ap_lt.
    induction (QposMinMax.Qpos_min x del') using
       (QposMinMax.Qpos_min_case x del'). 2: eassumption.
    apply le_ball_radius in l0. simpl in l0.
    eapply Qle_lt_trans. eassumption. assumption.

  + unfold lift in H. destruct a, b.
    destruct (lt_ball_grow _ _ _ _ H).
    destruct p. apply FormTop.glrefl.
    econstructor. unfold In. simpl. 
    exists (f m, x0). split. 
    eapply lt_le_trans. eassumption. eassumption.
    split. apply lt_le_weak. eassumption. reflexivity.
    apply lift_f_ap_lt. assumption.
Qed.


End Lipschitz.

Context {X Y : MetricSpace}.
Delimit Scope uc_scope with uc.
Variable f : (X --> Y)%uc.

Definition mu' (eps : Qpos) : Qpos :=
  Qpossmaller (mu f eps).

Definition mu'_cont (eps : Qpos) a b :
  ball (mu' eps) a b -> ball eps (f a) (f b).
Proof.
intros. 
apply uc_prf. eapply ball_ex_weak_le.
apply Qpossmaller_prf. simpl. assumption.
Qed.

Existing Instances PreO PreO.PreOrder_I.

Definition lift_uc : Cont.map (Ball X) (Ball Y) :=
  fun By Bx => let (x, delta) := Bx in
   { eps' : Qpos & 
     ((delta < mu' eps') * lt_ball _ (f x, eps') By)%type }.

Lemma lift_shrink {x y delta eps} :
  lift_uc (y, eps) (x, delta) ->
  { eps' : Qpos & ((eps' < eps) * lift_uc (y, eps') (x, delta))%type }.
Proof.
intros. 
destruct H as (eps' & mueps' & ltballeps').
pose proof (lt_ball_shrink _ _ _ _ ltballeps') as H.
destruct H as (eps'0 & eps'small & lt_ball_shrunk).
exists eps'0. split. assumption. unfold lift.
exists eps'. split. assumption. assumption.
Qed.


Theorem Cont_uc : Cont.t (le_ball X) (le_ball Y)
 (Cov X) (Cov Y) lift_uc.
Proof.
Abort.

End Map.
End Metric.
