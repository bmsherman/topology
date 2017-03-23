Require Import
  Numbers.QFacts
  CoRN.model.structures.QposInf.

Set Universe Polymorphism.

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

Definition Qpos_between {x y : Qpos} :
  x < y -> { mid : Qpos & x < mid /\ mid < y }.
Proof.
intros H.
destruct (Qbetween H) as (mid & midl & midh).
assert (0 < mid) as H'.
eapply Qlt_trans. apply Qpos_prf. apply midl.
exists (exist _ mid H'). simpl. split; assumption.
Qed.

Lemma Qpos_one_half_lt : forall (x : Qpos),
  (Qpos_one_half * x)%Qpos < x.
Proof.
intros. rewrite <- (Qplus_0_r).
rewrite <- (one_half_sum x). 
apply Qplus_lt_r. apply Qpos_prf. 
Qed. 

Lemma Qpos_plus_comm (x y : Qpos)
  : (x + y == y + x)%Qpos.
Proof.
ring.
Qed.

Lemma Qpos_plus_lt_l (q : Q) (e : Qpos) :
  q < e + q.
Proof.
setoid_replace q with (0 + q)%Q at 1 by ring.
apply Qplus_lt_l. apply Qpos_prf.
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

Lemma Qpos_inv_scale_1 (y : Qpos) (e : Q) : y * (Qpos_inv y * e) == e.
Proof.
intros. simpl. rewrite Qmult_assoc. rewrite Qmult_inv_r. 
ring. unfold not. intros contra.
eapply Qlt_not_eq. apply Qpos_prf. symmetry. eassumption.
Qed.

Lemma Qpos_inv_scale_2 (eps : Qpos) (x : Q)
  : Qpos_inv eps * (eps * x) == x.
Proof.
rewrite Qmult_assoc. rewrite (Qmult_comm _ eps).
rewrite <- Qmult_assoc. apply Qpos_inv_scale_1.
Qed.

Lemma Qpos_inv_lt : forall x y q : Qpos,
  (x < Qpos_inv y * q
  -> y * x < q)%Qpos.
Proof.
intros. apply Qmult_lt_compat_l_inv with (Qpos_inv y).
apply Qpos_prf.
rewrite Qmult_assoc. rewrite (Qmult_comm _ y).
rewrite <- Qmult_assoc.
rewrite Qpos_inv_scale_1. assumption.
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