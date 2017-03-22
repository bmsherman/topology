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