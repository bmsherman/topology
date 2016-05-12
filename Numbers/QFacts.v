Require Import QArith.

Definition Qaverage (x z : Q) : (x < z)%Q
  -> (let avg := ((x + z) / (1 + 1)) in x < avg /\ avg < z)%Q.
Proof. split.
- apply Qlt_shift_div_l. apply Qlt_alt. reflexivity.
  setoid_replace (x * (1 + 1))%Q with (x + x)%Q by ring.
  setoid_replace (x + z)%Q with (z + x)%Q by ring.
  apply Qplus_lt_le_compat. assumption. apply Qle_refl.
- apply Qlt_shift_div_r. apply Qlt_alt. reflexivity.
  setoid_replace (z * (1 + 1))%Q with (z + z)%Q by ring.
  apply Qplus_lt_le_compat. assumption. apply Qle_refl.
Qed.

Definition Qbetween (x z : Q) : (x < z)%Q
  -> { y | (x < y /\ y < z)%Q }.
Proof. intros. eexists. apply Qaverage. assumption.
Qed.

Instance Qle_Reflexive : Reflexive Qle.
Proof.
unfold Reflexive. apply Qle_refl.
Qed.

Instance Qle_Transitive : Transitive Qle.
Proof.
unfold Transitive. apply Qle_trans.
Qed.

Instance Qlt_Transitive : Transitive Qlt.
Proof.
unfold Transitive. apply Qlt_trans.
Qed.

Require Import RelationClasses.

Instance Qlt_le_Subrelation : subrelation Qlt Qle.
Proof. 
unfold subrelation, predicate_implication, pointwise_lifting
  , Basics.impl.
apply Qlt_le_weak.
Qed.

Instance Qplus_le_Proper : Proper (Qle ==> Qle ==> Qle) Qplus.
Proof.
unfold Proper, respectful.
intros. apply Qplus_le_compat; assumption.
Qed.

Lemma Qopp_lt_compat: forall p q : Q, (p < q)%Q -> (- q < - p)%Q.
Proof.
Admitted.

Lemma Qplus_open : forall q x y : Q, (q < x + y
  -> exists x' y', x' < x /\ y' < y /\ (q <= x' + y'))%Q.
Proof.
intros. 
pose proof (Qbetween (q - y) x).
pose proof (Qbetween (q - x) y).
Admitted.