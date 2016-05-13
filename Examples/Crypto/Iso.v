Require Import BinNums Crypto.Spec.ModularArithmetic
  Crypto.ModularArithmetic.ModularArithmeticTheorems
  BinNat BinInt
  Eqdep_dec
  Types.Iso.

Definition FN (modulus : N) := { z : N | z = (z mod modulus)%N }.

Lemma FNeq (M : N) : forall (x y : FN M), projT1 x = projT1 y -> x = y.
Proof.
apply Iso.sig_eq. intros a. apply UIP_dec. apply N.eq_dec.
Qed.

Definition FN_to_F M (modgt0 : M <> 0%N) (x : FN M) : F (BinInt.Z.of_N M).
Proof.
destruct x. exists (Z.of_N x).
rewrite e at 1.
apply Znat.N2Z.inj_mod. assumption.
Defined.

Lemma Mgt0Z M : M <> 0%N -> (0 < Z.of_N M)%Z.
Proof.
intros H.
replace 0%Z with (Z.of_N 0%N) by reflexivity.
apply Znat.N2Z.inj_lt. apply N.neq_0_lt_0. assumption.
Qed.

Definition F_to_FN M (Ngt0 : M <> 0%N) (x : F (Z.of_N M))
  : FN M.
Proof.
destruct x.
exists (Z.to_N x).
rewrite e at 1.
pose (N' := Z.of_N M).
assert (Z.to_N N' = M) as H.
  unfold N'. apply Znat.N2Z.id.
assert (0 < N')%Z as H1 by (apply Mgt0Z; assumption).
rewrite <- H.
rewrite Znat.Z2N.id.
apply Znat.Z2N.inj_mod.
rewrite e.
apply Zdiv.Z_mod_lt.
apply Z.gt_lt_iff. apply H1. apply H1. 
apply Z.lt_le_incl. apply H1.
Defined.

Lemma to_F_to_FN M (Ngt0 : M <> 0%N) (x : FN M) :
   F_to_FN M Ngt0 (FN_to_F M Ngt0 x) = x.
Proof.
apply FNeq. destruct x; simpl.
apply Znat.N2Z.id.
Qed.

Lemma to_FN_to_F M (Ngt0 : M <> 0%N) (x : F (Z.of_N M)) :
  FN_to_F M Ngt0 (F_to_FN M Ngt0 x) = x.
Proof.
apply F_eq. destruct x; simpl. apply Znat.Z2N.id.
rewrite e. apply Zdiv.Z_mod_lt.
apply Z.gt_lt_iff. apply Mgt0Z. assumption.
Qed.

Definition F_FN_Iso M (Ngt0 : M <> 0%N) : Iso.T (F (Z.of_N M)) (FN M) :=
  {| Iso.to := F_to_FN M Ngt0
   ; Iso.from := FN_to_F M Ngt0
   ; Iso.from_to := to_FN_to_F M Ngt0
   ; Iso.to_from := to_F_to_FN M Ngt0
  |}.

Definition NisoNat : Iso.T nat N :=
  {| Iso.to := N.of_nat
   ; Iso.from := N.to_nat
   ; Iso.to_from := Nnat.N2Nat.id
   ; Iso.from_to := Nnat.Nat2N.id
  |}.

Lemma NisoSmall M (Ngt0 : M <> 0%N) : Iso.T (FN M) {x | (x < M)%N }.
Proof.
apply Iso.subsetSelf; try (intro x; apply UIP_dec).
intros. split; intros. symmetry in H. apply N.mod_small_iff; assumption.
symmetry. apply N.mod_small_iff; assumption.
apply N.eq_dec. decide equality.
Defined.

Scheme Induction for le Sort Prop.

Require Import Peano_dec.
Lemma le_irrel (m n : nat) (p : m <= n) : forall q, p = q.
Proof.
induction p using le_ind_dep; intros.
refine (
  (match q as q0 in le _ m' return forall (eqprf : m' = m), 
    le_n m = eq_rect m' (fun m'' => m <= m'') q0 _ eqprf with
  | le_n => fun eqprf => _
  | le_S m _ => fun eqprf => _
  end) eq_refl
). assert (eqprf = eq_refl).
  apply  UIP_dec. apply eq_nat_dec.
  rewrite H. simpl. reflexivity.
  apply False_rect.
  rewrite <- eqprf in l. apply Le.le_Sn_n in l. assumption.

  refine (
  (match q as q0 in le _ m' return forall (eqprf : m' = S m0)
    (p0 : m <= m0), 
    le_S m m0 p0 = eq_rect m' (fun m'' => m <= m'') q0 _ eqprf with
  | le_n => fun eqprf => _
  | le_S m _ => fun eqprf => _
  end) eq_refl p
  ); clear q; intros.
  apply False_rect.
  rewrite eqprf in p0. apply Le.le_Sn_n in p0. contradiction.
  assert (m1 = m0) by congruence. induction H.
  assert (eqprf = eq_refl). apply UIP_dec.
  apply eq_nat_dec. rewrite H. simpl. rewrite <- (IHp p0). 
  rewrite <- (IHp l). reflexivity.
Qed.  

Theorem NsmallnatSmall (n : nat) : 
  Iso.T {x | x < n} {x | (x < N.of_nat n)%N }.
Proof.
apply (Iso.subset _ _ NisoNat); intros.
- simpl. unfold N.lt. 
  rewrite Nnat.N2Nat.inj_compare.
  apply Compare_dec.nat_compare_lt.
  repeat rewrite Nnat.Nat2N.id. assumption.
- apply Compare_dec.nat_compare_lt.
  rewrite Nnat.Nat2N.inj_compare.
  rewrite Nnat.N2Nat.id. assumption.
- unfold lt in *. apply le_irrel.
- apply UIP_dec. decide equality.
Defined.

Theorem natSmallFin (n : nat) : Iso.T (Fin.t n) {x | x < n}.
Proof.
refine (
  {| Iso.to := Fin.to_nat
   ; Iso.from := fun ex => Fin.of_nat_lt (proj2_sig ex)
  |}
); intros.
- apply Fin.of_nat_to_nat_inv.
- destruct b. simpl. apply Iso.sig_eq. unfold lt. intros. apply le_irrel. 
  simpl.

  generalize dependent x.
  induction n; intros.
  + apply False_rect. apply Lt.lt_n_0 in l. assumption.
  + generalize dependent l. induction x; intros. 
    * simpl. reflexivity.
    * simpl. specialize (IHn _ (Lt.lt_S_n x n l)).
      destruct (Fin.to_nat (Fin.of_nat_lt (Lt.lt_S_n x n l))) eqn:destreqn.
      simpl in *. congruence.
Defined.

Theorem ZNnatcomposition (n : nat) : Z.of_nat n = Z.of_N (N.of_nat n).
Proof. 
destruct n; simpl; reflexivity.
Qed.

Theorem finiteF (n : nat) : Iso.T (F (Z.of_nat (S n))) (Fin.t (S n)).
Proof.
assert (N.of_nat (S n) <> 0%N) by (simpl; congruence).
eapply Iso.Trans. rewrite ZNnatcomposition. apply F_FN_Iso.
assumption. eapply Iso.Trans. apply NisoSmall. assumption.
eapply Iso.Trans. eapply Iso.Sym. apply NsmallnatSmall.
apply Iso.Sym. apply natSmallFin.
Defined.