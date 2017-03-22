Require Import 
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC
  FormTopC.FormalSpace
  Numbers.QFacts
  Numbers.QPosFacts
  
  FormTopC.Cont
  Coq.QArith.Qminmax

  CoRN.metric2.Metric
  CoRN.model.structures.Qpossec
  Coq.QArith.QArith_base
  CoRN.model.structures.QposInf
  CoRN.metric2.UniformContinuity
  CMorphisms.

Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope FT.

Section Metric.
Universes A P I.

Context {MS : MetricSpace}.

Definition M@{} : Type@{A} := msp_is_setoid MS.

Definition Ball : Type@{A} := (M * Qpos)%type.

Definition lt_ball@{} (Bx By : Ball) : Type@{P} :=
  let (x, delta) := Bx in let (y, eps) := By in
  { d : Qpos | ball d x y /\ (d + delta < eps)%Qpos }.

Definition le_ball@{} (Bx By : Ball) : Type@{P} := 
  let (y, eps) := By in
  forall e : Qpos, lt_ball Bx (y, e + eps)%Qpos.

Instance PreO : PreO.t@{A P} le_ball.
Proof.
constructor.
- intros []. unfold le_ball. intros.
  destruct (Qpos_smaller e) as [e' eprf].
  exists e'. split. apply ball_refl. apply Qplus_lt_l. assumption.
- intros [] [] [] H H0. unfold le_ball in *.
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

Lemma lt_le_weak : forall a b,
  lt_ball a b -> le_ball a b.
Proof.
unfold lt_ball, le_ball.
intros [] [] (d & b & l).
intros e.
exists d. split. assumption.
eapply Qlt_le_trans. eassumption.
setoid_replace (q0 : Q) with (0 + q0)%Q at 1 by ring.
apply Qplus_le_l. apply Qlt_le_weak. apply Qpos_prf.
Qed.

Lemma lt_le_trans : forall a b c, 
   lt_ball a b -> le_ball b c -> lt_ball a c.
Proof.
intros [] [] [] H H0. 
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

Lemma le_lt_trans a b c :
  le_ball a b -> lt_ball b c -> lt_ball a c.
Proof.
intros H H0. destruct a, b, c.
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
unfold le_ball. intros H x H0. destruct a, c.
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
  (eps <= eps')%Q -> le_ball (x, eps) (x, eps').
Proof.
intros. simpl. intros.
destruct (Qpos_smaller e) as [e' e'prf].
exists e'. split. apply ball_refl.
apply Qplus_lt_le_compat; assumption.
Qed.

Lemma lt_ball_shrink Bx y eps :
  lt_ball Bx (y, eps)
  -> {eps' : Qpos & ((eps' < eps) * lt_ball Bx (y, eps'))%type }.
Proof.
intros H. destruct Bx. destruct H. destruct a.
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

Lemma lt_ball_grow x delta By :
  lt_ball (x, delta) By
  -> { delta' : Qpos & ((delta < delta') * lt_ball (x, delta') By)%type }.
Proof.
intros H. destruct By. destruct H as (d & balld & dlt).
destruct (Qpos_lt_plus dlt).
exists (delta + Qpos_one_half * x0)%Qpos. split.
  rewrite <- (Qplus_0_r delta) at 1. simpl. 
  apply Qplus_lt_r. apply (Qpos_prf (Qpos_one_half * x0)%Qpos).
  simpl. exists d. split.  assumption.
  rewrite q0. rewrite Qplus_assoc. apply Qplus_lt_r.
  apply Qpos_one_half_lt.
Qed.
   

Lemma Qlt_all_Qle (x y : Q) :
  (forall (eps : Qpos), x < y + eps) -> (x <= y)%Q.
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
  le_ball Bx By -> (snd Bx <= snd By)%Q.
Proof.
destruct Bx, By. simpl. intros H.
apply Qlt_all_Qle.
intros. destruct (H eps). destruct a.
rewrite Qplus_comm. eapply Qadd_lt.
eassumption.
Qed.

Definition IxUL@{} (x : Ball) : Set := 
  option Qpos.

Definition CUL (b : Ball) (i : IxUL b) : Subset@{A P} Ball := 
  match i with
  | None         => fun b' => lt_ball b' b
  | Some epsilon => fun b' => snd b' = epsilon
  end.

Definition MetricPO : FormTop.PreOrder@{A P} :=
  {| PO_car := Ball
   ; FormTop.le := le_ball 
  |}.

Definition MetricPS@{} : PreISpace.t@{A P I} :=
  {| PreISpace.S := MetricPO
   ; PreISpace.C := CUL
  |}.

Lemma shrink_ball (b : Ball) :
  { b' : Ball & lt_ball b' b }.
Proof.
destruct b as [m q].
destruct (Qpos_smaller q) as [q' qq'].
exists (m, q'). apply lt_ball_center. assumption.
Qed. 

Axiom undefined : forall A, A.

Lemma MPos_MUniv : FormTop.gtPos MetricPS.
Proof.
unshelve econstructor.
- exact (fun _ => True).
- simpl. auto.
- simpl. intros. destruct i.
  + exists (fst a, QposMinMax.Qpos_min q (snd a)).
    split. simpl. split. le_down. destruct a. simpl fst. 
    apply le_ball_center. apply QposMinMax.Qpos_min_lb_r.
    exists (fst a, q). reflexivity.
    apply le_ball_center. apply QposMinMax.Qpos_min_lb_l. auto.
  + destruct (shrink_ball a). exists x. split.
    split. le_down. apply lt_le_weak; eassumption.
    exists x. simpl. eapply lt_le_trans; eassumption.
    reflexivity. auto.
- simpl. auto.
Qed.


Local Instance MPos@{API'} : FormTop.gtPos MetricPS
  := MPos_MUniv@{API' API' API' P P P P P API' P P P P P}.


Definition Metric@{API'} : IGt@{A P I API'} :=
  {| IGS := MetricPS
   ; IGpos := MPos@{API'}
  |}.

End Metric.

Arguments Ball MS : clear implicits.

Section Map.

(** In an open ball *)
Inductive o_ball {X : MetricSpace} {eps : Qpos} {a b : X} : Set :=
  In_o_ball : forall e : Qpos, e < eps -> ball e a b -> o_ball.

Arguments o_ball {X} eps a b.

Lemma o_ball_ball {X : MetricSpace} eps (a b : X) 
  : o_ball eps a b -> ball eps a b.
Proof.
intros H. induction H.
eapply ball_weak_le. apply Qlt_le_weak. eassumption. 
assumption.
Qed.

Lemma o_ball_shrink {X : MetricSpace} {eps : Qpos} {a b : X}
  : o_ball eps a b -> { eps' : Qpos & ((eps' < eps) * o_ball eps' a b)%type }.
Proof.
intros. destruct H.
destruct (Qpos_between q) as (mid & midl & midh).
exists mid. split. assumption. eapply In_o_ball; eassumption.
Qed.

Lemma le_ball_applies_o {X : MetricSpace} {a c : Ball X} : 
  le_ball a c
  -> forall x : X, o_ball (snd a) (fst a) x
  -> o_ball (snd c) (fst c) x.
Proof.
intros H x H0. 
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

Lemma o_ball_refl : forall {X : MetricSpace} (x : X) eps,
  o_ball eps x x.
Proof.
intros. destruct (Qpos_smaller eps). 
econstructor. eassumption. apply ball_refl.
Qed.

Lemma o_ball_sym : forall {X : MetricSpace} (x y : X) eps,
  o_ball eps x y -> o_ball eps y x.
Proof.
intros. induction H. econstructor; eauto.
apply ball_sym; assumption.
Qed.

Section Lipschitz.

Context {X Y : MetricSpace}.


(** Yoneda embeddding of a point in its completion *)

Definition Yoneda (x : X) : Subset (Ball X) :=
  fun B => let (y, eps) := B in o_ball eps x y.

Existing Instance PreO.

Variable f : X -> Y.
Variable k : Qpos.
Definition Lipschitz : Prop := forall x x' eps, ball eps x x' -> ball (k * eps) (f x) (f x').

Hypothesis f_lip : Lipschitz.

Lemma lt_monotone : forall x x' eps eps',
  lt_ball (x, eps) (x', eps') ->
  lt_ball (f x, k * eps)%Qpos (f x', k * eps')%Qpos.
Proof.
simpl. intros.
destruct H as (d & bd & dlt).
exists (k * d)%Qpos. split. apply f_lip. assumption. 
simpl. rewrite <- Qmult_plus_distr_r. 
apply Qmult_lt_compat_l. apply Qpos_prf.
assumption.
Qed.

Lemma Qpos_div : forall (e y : Qpos), y * (Qpos_inv y * e) == e.
Proof.
intros. simpl. rewrite Qmult_assoc. rewrite Qmult_inv_r. 
ring. unfold not. intros contra.
eapply Qlt_not_eq. apply Qpos_prf. symmetry. eassumption.
Qed.

Lemma le_monotone x x' eps eps' :
  le_ball (x, eps) (x', eps')
  -> le_ball (f x, k * eps)%Qpos (f x', k * eps')%Qpos.
Proof.
intros H. unfold le_ball. intros.
apply lt_le_trans with (f x', k * (Qpos_inv k * e + eps'))%Qpos.
apply lt_monotone. apply H. apply le_ball_center.
apply Qeq_le.
simpl. rewrite Qmult_plus_distr_r. 
rewrite (Qpos_div e k). reflexivity.
Qed.

Definition lift : Cont.map (toPreSpace (IGS (@Metric X)))
   (toPreSpace (IGS (@Metric Y))) := fun By Bx =>
  let (x, delta) := Bx in lt_ball (f x, k * delta)%Qpos By.


Lemma lift_f_ap_lt : forall x (eps eps' : Qpos),
  eps < eps' -> lift (f x, k * eps')%Qpos (x, eps).
Proof.
intros. 
simpl. destruct (Qpos_lt_plus H).
exists (k * (Qpos_one_half * x0))%Qpos. split. apply ball_refl. rewrite q.
rewrite Qplus_comm. simpl. 
rewrite <- Qmult_plus_distr_r.
apply Qmult_lt_compat_l. apply Qpos_prf.
apply Qplus_lt_r. 
apply Qpos_one_half_lt.
Qed.

Lemma lift_f_ap_lt' x (eps eps' : Qpos) :
  k * eps < eps' -> lift (f x, eps') (x, eps).
Proof.
intros H.
pose proof (lift_f_ap_lt x eps (Qpos_inv k * eps')%Qpos) as H0.
simpl in H0.
assert (eps < / k * eps').
apply Qmult_lt_compat_l_inv with k. apply Qpos_prf.
rewrite Qmult_assoc. rewrite Qmult_inv_r.
rewrite Qmult_1_l. assumption.
unfold not. intros. 
eapply Qlt_not_eq. apply (Qpos_prf k).
symmetry; assumption.
specialize (H0 H1). clear H1.
destruct H0 as (d & balld & dlt).
exists d. split. assumption.
rewrite Qmult_assoc in dlt.
rewrite Qmult_inv_r in dlt.
rewrite Qmult_1_l in dlt. simpl. assumption.
unfold not. intros. eapply Qlt_not_eq.
apply (Qpos_prf k). symmetry; assumption.
Qed.

Lemma lift_f_le {a b u} : lift b a ->
   le_ball u a
  -> lift b u.
Proof.
intros. destruct a, b, u.
unfold lift in *. eapply le_lt_trans. apply le_monotone. 
eassumption. assumption.
Qed.

Lemma Qpos_inv_lt : forall x y q : Qpos,
  (x < Qpos_inv y * q
  -> y * x < q)%Qpos.
Proof.
intros. apply Qmult_lt_compat_l_inv with (Qpos_inv y).
apply Qpos_prf.
rewrite Qmult_assoc. rewrite (Qmult_comm _ y).
rewrite <- Qmult_assoc.
rewrite Qpos_div. assumption.
Qed.

Arguments M : clear implicits.

Theorem Cont : IGCont.t (toPreSpace (IGS Metric)) (IGS Metric) lift.
Proof.
constructor.
- intros a. apply FormTop.glrefl. apply true_union'.
  destruct a. exists (f m, q + k * q)%Qpos. simpl.
  destruct (Qpos_smaller q).
  exists x. split. apply ball_refl.
  apply Qplus_lt_l. assumption.
- intros a b c H H0. unfold lift in H, H0. destruct a.
  destruct b, c.
  pose proof (lt_ball_shrink _ _ _ H) as H1.
  destruct H1. destruct p. clear H.
  pose proof (lt_ball_shrink _ _ _ H0) as H.
  destruct H. destruct p.  clear H0.
  destruct (Qpos_lt_plus q2).
  destruct (Qpos_lt_plus q3).
  destruct (Qpos_smaller (QposMinMax.Qpos_min x1 x2)).
  apply (fun U => FormTop.gle_infinity (A := MetricPS) (m, q) 
  U (m, q) (Some (Qpos_inv k * x3))%Qpos (PreO.le_refl (m, q))).
  intros. destruct X0 as (l1 & P2). le_downH l1. destruct P2.
  simpl in i. unfold In in i. destruct a as [m4 x4]. simpl snd in *.
  subst. destruct u as [m2 ?].
  apply FormTop.glrefl.
  exists (f m2, (QposMinMax.Qpos_min x1 x2)).
  split; le_down.

  simpl. intros. destruct l as (d & balld & dlt).
  exists (e + k * q + d)%Qpos. split. Focus 2. 
  rewrite q4. simpl. rewrite <- !Qplus_assoc. 
  apply Qplus_lt_r. rewrite Qplus_assoc.
  eapply Qplus_lt_le_compat. rewrite Qplus_comm. assumption.
  apply QposMinMax.Qpos_min_lb_l.
  destruct (l1 (Qpos_inv k * e))%Qpos. destruct a. 
  eapply ball_triangle. 2:eassumption.
  eapply ball_weak_le. 2: eapply f_lip. 2: eassumption.
  etransitivity. Focus 2. apply Qlt_le_weak.
  simpl. rewrite <- (Qpos_div e k).
  rewrite <- Qmult_plus_distr_r.
  eapply Qmult_lt_compat_l. apply Qpos_prf.
  eassumption.
  pose proof (Qpos_div e k). simpl.
  rewrite Qmult_plus_distr_r.
  rewrite <- (Qplus_0_r (k * x4)) at 1.
  apply Qplus_le_r. apply Qlt_le_weak. 
  apply (Qpos_prf (k * q7)%Qpos).

  simpl. intros. destruct l0 as (d & balld & dlt).
  exists (e + k * q + d)%Qpos. split. Focus 2. 
  rewrite q5. simpl. rewrite <- !Qplus_assoc. 
  apply Qplus_lt_r. rewrite Qplus_assoc.
  eapply Qplus_lt_le_compat. rewrite Qplus_comm. assumption.
  apply QposMinMax.Qpos_min_lb_r.
  destruct (l1 (Qpos_inv k * e))%Qpos. destruct a. 
  eapply ball_triangle. 2:eassumption.
  eapply ball_weak_le. 2: eapply f_lip. 2: eassumption.
  etransitivity. Focus 2. apply Qlt_le_weak.
  simpl. rewrite <- (Qpos_div e k).
  rewrite <- Qmult_plus_distr_r.
  eapply Qmult_lt_compat_l. apply Qpos_prf.
  eassumption.
  pose proof (Qpos_div e k). simpl.
  rewrite Qmult_plus_distr_r.
  rewrite <- (Qplus_0_r (k * x4)) at 1.
  apply Qplus_le_r. apply Qlt_le_weak. 
  apply (Qpos_prf (k * q7)%Qpos).

  apply lift_f_ap_lt'. eapply Qle_lt_trans. 
  pose proof (le_ball_radius l2) as H.
  simpl in H. rewrite Qmult_comm. 
  apply <- Q.Qle_shift_div_l.
  etransitivity. eassumption.
  rewrite Qmult_comm. unfold Qdiv. reflexivity.
  apply Qpos_prf. assumption.
- intros a b c H H0. unfold lift in *. destruct a, c.
  eapply le_lt_trans. 2: eassumption.
  eapply le_monotone. assumption.
- intros [] b c H H0. unfold lift. unfold lift in H. 
    eapply lt_le_trans; eassumption.
- intros a b c ix l H. 
  destruct ix; simpl in *.
  + simpl. clear c l. destruct (Qpos_smaller (Qpos_inv k * q)%Qpos).
    apply (FormTop.gle_infinity (A := MetricPS) a _ a (Some x)).
    reflexivity.
    intros. destruct X0 as (l & d0). le_downH l. 
    destruct u. destruct d0.
    pose proof (lift_f_le H l) as H0. clear H l.
    destruct (Qpos_between q0) as (x0 & K). destruct K as (H1 & H2).
    destruct b. unfold lift in H0.
    pose proof (lt_ball_grow _ _ _ H0) as H3.
    destruct H3 as (del' & q1del & lt_del').
    
    apply FormTop.glrefl.
    exists (f m, QposMinMax.Qpos_min (k * x0)%Qpos del'). unfold In.
    split. le_down. 
    eapply lt_le_weak. eapply le_lt_trans. 2: eassumption.
    apply le_ball_center. apply QposMinMax.Qpos_min_lb_r.
    exists (f m, q). reflexivity.
    apply le_ball_center. etransitivity. 
    apply QposMinMax.Qpos_min_lb_l. apply Qlt_le_weak.
    apply Qpos_inv_lt. assumption.

    apply lift_f_ap_lt'.
    induction (QposMinMax.Qpos_min (k * x0) del') using
       (QposMinMax.Qpos_min_case (k * x0) del'). 2: eassumption.
    apply le_ball_radius in l0. simpl in l0.
    
    apply Qmult_lt_compat_l_inv with (Qpos_inv k).
    apply Qpos_prf.

    rewrite Qmult_assoc. rewrite (Qmult_comm _ k).
    rewrite <- Qmult_assoc. rewrite Qpos_div.
    eapply Qle_lt_trans. eassumption.
    simpl. 
    rewrite Qmult_assoc. rewrite (Qmult_comm _ k).
    rewrite <- Qmult_assoc. rewrite Qpos_div.
    unfold In in i. simpl in i. subst.
    assumption.
  + unfold lift in H. destruct a, b.
    destruct (lt_ball_grow _ _ _ H).
    destruct p. apply FormTop.glrefl.
    econstructor. unfold In.
    split. le_down. apply lt_le_weak. eassumption.
    exists (f m, x). eapply lt_le_trans. eassumption. eassumption.
    reflexivity.
    apply lift_f_ap_lt'. assumption.
Qed.


End Lipschitz.


(** Try to do it with maps that are only uniformly continuous,
    rather than just Lipschitz.
    I can't figure out how to do this proof. *)
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

Definition lift_uc : Cont.map (toPreSpace (IGS (@Metric X))) 
  (toPreSpace (IGS (@Metric Y))) :=
  fun By Bx => let (x, delta) := Bx in
   { eps' : Qpos & 
     ((delta < mu' eps') * lt_ball (f x, eps') By)%type }.

Lemma lift_shrink {x y delta eps} :
  lift_uc (y, eps) (x, delta) ->
  { eps' : Qpos & ((eps' < eps) * lift_uc (y, eps') (x, delta))%type }.
Proof.
intros H. 
destruct H as (eps' & mueps' & ltballeps').
pose proof (lt_ball_shrink _ _ _ ltballeps') as H.
destruct H as (eps'0 & eps'small & lt_ball_shrunk).
exists eps'0. split. assumption. unfold lift.
exists eps'. split. assumption. assumption.
Qed.


Theorem Cont_uc : Cont.t (toPreSpace (IGS (@Metric X))) 
  (toPreSpace (IGS (@Metric Y))) lift_uc.
Proof.
Abort.

End Map.