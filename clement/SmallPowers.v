Require Import Qcanon QArith_base Qring.
Open Scope Q_scope.
Require Import Psatz.

Lemma Qlt_inverse_iff :
  forall a b,
    0 < a ->
    0 < b ->
    (/ a < / b <-> b < a).
Proof.
  intros.
  rewrite <- (Qmult_lt_l _ _ a) by assumption.
  rewrite <- (Qmult_lt_r _ _ b) by assumption.
  rewrite Qmult_inv_r, Qmult_1_l by (destruct a as ([ | ? | ?] & ?); discriminate).
  rewrite <- Qmult_assoc, (Qmult_comm _ b).
  rewrite Qmult_inv_r, Qmult_1_r by (destruct b as ([ | ? | ?] & ?); discriminate).
  reflexivity.
Qed.

Require Import Qpower.

Lemma power_more_than_linear_util:
  forall (q a : Q) (n : nat),
    0 < q ->
    0 < a ->
    a <= a * (1 + q) ^ Z.of_nat n.
Proof.
  intros; induction n.
  - simpl; rewrite Qmult_1_r; apply Qle_refl.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_l, Qpower_plus by lra; simpl.
    eapply Qle_trans; eauto.
    rewrite Qmult_assoc.
    apply Qmult_le_compat_r.
    + rewrite <- Qmult_1_r, Qmult_le_l at 1; lra.
    + apply Qpower_pos; lra.
Qed.

Lemma power_more_than_linear (q: Q):
  0 < q ->
  forall n : nat,
    1 + q * (inject_Z (Z.of_nat n)) <= (1 + q) ^ (Z.of_nat n).
Proof.
  intros.
  induction n.
  - unfold inject_Z.
    ring_simplify; simpl; compute; intro; discriminate.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_l, inject_Z_plus, Qmult_plus_distr_r, Qpower_plus, Qmult_1_r by lra.
    simpl.
    rewrite Qmult_plus_distr_l, Qmult_1_l.
    rewrite Qplus_assoc, (Qplus_comm 1 _) , <- Qplus_assoc, Qplus_comm at 1.
    apply Qplus_le_compat.
    + assumption.
    + apply power_more_than_linear_util; eauto.
Qed.

Lemma power_large_util'' :
  forall b a, (b > 0 -> exists n, a < S n * b)%nat.
Proof.
  intros; exists a; induction a; simpl in *; omega.
Qed.

Lemma power_large_util' (q epsilon: Q):
  0 < q ->
  0 < epsilon ->
  exists n : nat, epsilon < q * (inject_Z (Z.of_nat n)).
Proof.
  intros.
  destruct q as ([ | qn | qn ] & qd), epsilon as ([ | epsilonn | epsilonn ] & epsilond); simpl in *; try discriminate.
  edestruct (power_large_util'' (Pos.to_nat (qn * epsilond))) as [ n h ].
  - apply Pos2Nat.is_pos.
  - eexists (S n).
    rewrite <- (Qmult_lt_l _ _ (/ (' qn # qd))), Qmult_assoc, (Qmult_comm _ (' qn # qd)), Qmult_inv_r, Qmult_1_l
      by first [ lra | reflexivity ].
    unfold Qlt, Qinv in *; simpl in *; unfold Z.lt.
    rewrite <- Pos2Z.inj_compare, Pos2Nat.inj_compare, <- nat_compare_lt, !Pos2Nat.inj_mul, SuccNat2Pos.id_succ, <- !Pos2Nat.inj_mul.
    eassumption.
Qed.

Lemma power_large_util (q epsilon: Q):
  0 < q ->
  0 < epsilon ->
  exists n : nat, epsilon < 1 + q * (inject_Z (Z.of_nat n)).
Proof.
  intros.
  edestruct (power_large_util' q epsilon) as [n h]; try eassumption.
  exists n; eapply Qlt_le_trans with (q * inject_Z (Z.of_nat n)); try lra.
Qed.

Lemma power_large (q epsilon: Q):
  (1 < q ->
   0 < epsilon ->
   exists n : nat, epsilon < q ^ (Z.of_nat n))%Q.
Proof.
  intros.
  destruct (power_large_util (q - 1) epsilon) as [n h]; try lra.
  exists n.
  eapply Qlt_le_trans; eauto.
  remember (q - 1) as q';
    setoid_replace q with (1 + (q - 1)) using relation Qeq; subst.
  apply power_more_than_linear; lra.
  ring.
Qed.

Lemma Qpower_pos_lt:
  forall (q : Q) (n : nat), 0 < q -> 0 < q ^ Z.of_nat n.
Proof.
  intros; induction n.
  - simpl; lra.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_l, Qpower_plus by lra.
    erewrite <- Qmult_lt_l, Qmult_0_r in IHn; eassumption.
Qed.

Lemma Qpower_inv:
  forall (q : Q) (n : nat),
    0 < q ->
    (/ q) ^ Z.of_nat n == / q ^ Z.of_nat n.
Proof.
  intros; induction n.
  - reflexivity.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    setoid_rewrite (Qpower_plus (/ q)).
    setoid_rewrite IHn.
    change ((/ q) ^ 1) with (/ q).
    rewrite <- Qinv_mult_distr.
    setoid_rewrite (Qpower_plus q); try lra.
    reflexivity.
    apply Qinv_lt_0_compat in H; lra.
Qed.

Lemma power_small_Q (q epsilon: Q):
  0 < q ->
  q < 1 ->
  0 < epsilon ->
  exists n : nat, q ^ (Z.of_nat n) < epsilon.
Proof.
  intros qNonZero qSmall epsilonNonZero.
  destruct (power_large (/ q) (/ epsilon)) as [n h].
  - replace 1 with (/ 1) by reflexivity.
    rewrite Qlt_inverse_iff; lra.
  - eauto using Qinv_lt_0_compat.
  - exists n.
    setoid_replace ((/ q) ^ Z.of_nat n) with (/ q ^ (Z.of_nat n)) using relation Qeq in h.
    rewrite <- Qlt_inverse_iff; try lra.
    apply Qpower_pos_lt; lra.
    apply Qpower_inv; lra.
Qed.

Open Scope Qc_scope.

Lemma Qcpower_Qpower:
  forall (q : Qc),
    0 < q ->
    forall (n : nat), (q ^ n)%Qc == q ^ Z.of_nat n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_l, Qpower_plus.
    simpl Qcpower.
    unfold Qcmult.
    change (this (Q2Qc (q * (q ^ n)%Qc))) with (Qreduction.Qred (q * (q ^ n)%Qc)).
    setoid_rewrite Qreduction.Qred_correct.
    setoid_rewrite IHn.
    reflexivity.
    rewrite Qeq_alt.
    unfold Qclt in H; simpl in H; rewrite Qgt_alt in H.
    intro; congruence.
Qed.

Lemma power_small' (q epsilon: Qc):
  0 < q ->
  q < 1 ->
  0 < epsilon ->
  exists n : nat, q ^ n < epsilon.
Proof.
  intros.
  destruct (power_small_Q q epsilon) as [n h]; try eassumption.
  eexists n. unfold Qclt.
  setoid_rewrite Qcpower_Qpower; eassumption.
Qed.

Lemma power_small (q epsilon: Qc):
  0 <= q ->
  q < 1 ->
  0 < epsilon ->
  exists n : nat, q ^ n < epsilon.
Proof.
  intros h **.
  destruct (Qle_lt_or_eq _ _ h) as [ h' | h' ].
  - apply power_small'; eassumption.
  - exists 1%nat. unfold Qclt.
    replace (q ^ 1) with q by (simpl; rewrite Qcmult_1_r; reflexivity).
    setoid_rewrite <- h'; assumption.
Qed.