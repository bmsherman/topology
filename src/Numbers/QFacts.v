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

Definition Qbetween {x z : Q} : (x < z)%Q
  -> { y | (x < y /\ y < z)%Q }.
Proof. intros. eexists. apply Qaverage. assumption.
Qed.

Lemma Qmult_lt_compat_l : forall x y z : Q, 0 < z -> x < y -> z * x < z * y.
Proof.
intros. rewrite (Qmult_comm _ x), (Qmult_comm _ y).
apply Qmult_lt_compat_r; assumption.
Qed.

Lemma Qmult_lt_compat_l_inv : forall x y z : Q, 
  0 < z -> z * x < z * y -> x < y.
Proof.
intros. rewrite <- (Qmult_1_l x), <- (Qmult_1_l y).
rewrite <- !(Qmult_inv_r z).
rewrite (Qmult_comm z).
rewrite <- !Qmult_assoc. apply Qmult_lt_compat_l.
apply Qinv_lt_0_compat. assumption. assumption.
unfold not. intros contra.
rewrite contra in H.
eapply Qlt_irrefl. eassumption.
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
intros. rewrite Qlt_minus_iff. rewrite Qopp_involutive.
rewrite Qplus_comm. rewrite <- Qlt_minus_iff.
assumption.
Qed.

Lemma Qeq_le : forall x y, x == y -> x <= y.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma Qminus_lt {q x y : Q} :
   q < x + y <-> q - y < x.
Proof.
rewrite (Qlt_minus_iff q).
rewrite (Qlt_minus_iff (q - y)).
split; intros;
  (eapply Qlt_le_trans; [ eassumption | apply Qeq_le; ring ]).
Qed.

Lemma Qplus_open : forall q x y : Q, (q < x + y
  -> exists x' y', x' < x /\ y' < y /\ (q <= x' + y'))%Q.
Proof.
intros. 
(** WRONG WRONG WRONG *)
assert (q - y < x) as d1. apply Qminus_lt. assumption.
assert (q - x < y) as d2. apply Qminus_lt.
rewrite Qplus_comm. assumption.
destruct (Qbetween d1) as (mid1 & midl1 & midh1).
pose proof (Qbetween d2) as (mid2 & midl2 & midh2).
exists mid1. exists mid2. split. 
assumption. split. assumption. 
apply Qminus_lt in midl1. apply Qminus_lt in midl2.
Admitted.