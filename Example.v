Require Import Frame FormTop FrameVal.

(** If we view [F.prop] as locale corresponding to the 1-point set, then
    [unit_prop] is the unique probability distribution we can define for the 1-point 
    set; it puts all its mass (i.e., a measure of 1) on that single point. *)

Require Import LPReal Ring.

Definition unit_prop : Val.t One.FrameOne.
Proof.
refine (
  {| Val.val := fun P => LPRindicator (P I) |}
); simpl; intros.
- apply LPRind_false. unfold not. intros. destruct H.
  contradiction.
- unfold L.le in H. simpl in H. apply LPRind_imp. 
  unfold FormTop.leA, FormTop.Sat, One.Cov in *. 
  apply H. constructor.
- unfold FormTop.maxA, FormTop.minA.
  rewrite (LPRind_iff (exists u : True, _) (U I /\ V I)).
  rewrite (SRadd_comm LPRsrt (LPRindicator (U I \/ V I))).
  apply LPRind_modular.
  unfold FormTop.down. simpl. split; intros.
  destruct H as ([] & [] & Uu & Vv & _). auto.
  exists I. exists I. destruct H. auto.
- unfold Val.ContinuousV. intros.
  apply LPRind_exists. 
Defined.

Definition point {A} (x : A) : F.point (FormTop.FOps Logic.eq (Discrete.Cov A)).
Proof.
pose proof (@One.toFPoint A eq eq (PO.discrete A) (Discrete.Cov A)
  (Discrete.isCov A)).
specialize (X (fun x' => x' = x)).
apply X.
unfold One.Point. simpl.
constructor; unfold One.Cov, Discrete.Cov; intros.
- exists x. reflexivity.
- assumption.
- subst. exists x. split. split; reflexivity. reflexivity.
- exists b. auto.
Defined.

Section OTPExample.

Variable A : Type.
Hypothesis deceqA : forall a a' : A, {a = a'} + {a <> a'}.

Let Cov := Discrete.Cov A.

Instance POA : PO.t A Logic.eq Logic.eq := PO.discrete A.

Instance opsA : Frame.Ops (A -> Prop) := FormTop.FOps Logic.eq Cov.
Instance frameA : Frame.t (A -> Prop) opsA := FormTop.Frame Logic.eq Cov _
  (Discrete.isCov A).

Require Fin.
Import ValNotation.
Definition permutation {A} (f : A -> A) :=
  exists (g : A -> A), forall a, g (f a) = a.

Fixpoint finToVec {A} {n} : (Fin.t n -> A) -> Vector.t A n := match n with
  | 0 => fun _ => Vector.nil A
  | S n' => fun f => let ans := finToVec (fun x => f (Fin.FS x)) in
     Vector.cons A (f Fin.F1) _ ans
  end.

Definition uniformF {n : nat} (f : Fin.t (S n) -> A)
  := Val.uniform (finToVec (fun i => point (f i))).

End OTPExample.

Definition CovB := Discrete.Cov bool.
Instance OB : Frame.Ops (bool -> Prop) := FormTop.FOps Logic.eq CovB.
Instance PreOB : PreO.t bool Logic.eq := PreO.discrete bool.
Instance FB : Frame.t (bool -> Prop) OB := FormTop.Frame Logic.eq CovB (PreO.discrete bool) (Discrete.isCov bool).
Instance FTB : FormTop.t Logic.eq CovB := Discrete.isCov bool.

Require Import Qnn.
Local Open Scope LPR.
Import ValNotation.

Definition coin (p : Qnn) : Val.t FB :=
  (LPRQnn p * Val.unit (point true) + LPRQnn (1 - p)%Qnn * Val.unit (point false))%Val.

Definition faircoin := coin Qnnonehalf. 

Definition bfunc (f : bool -> bool) : Frame.cmap OB OB :=
  Cont.toCmap FTB FTB (Discrete.discrF f) (Discrete.fCont f).

Lemma LPRpluseq : forall (p a b a' b' : LPReal),
  a = a' -> b = b' ->
  (p * b + p * a = p * a' + p * b')%LPR.
Proof.
intros. subst. ring.
Qed.

Lemma LPRpluseq2 : forall (p a b a' b' : LPReal),
  a = a' -> b = b' ->
  (p * a + p * b = p * a' + p * b')%LPR.
Proof.
intros. subst. ring.
Qed.

Theorem reverse : forall (p : Qnn) (peven : (p = 1 - p)%Qnn),
  coin p = Val.map (bfunc negb) (coin p).
Proof.
intros. apply Val.eq_compat. unfold Val.eq.
intros. simpl. rewrite <- peven. clear peven.
unfold Cont.frame. 
apply LPRpluseq; apply LPRind_iff. 
- split; intros.
  + destruct H as (t' & Pt' & tt').
    subst. exists true. split. exists false. split. assumption. constructor.
    reflexivity.
  + destruct H as ([] & ([] & Pt & discr) & ttrue);
    exists false; inversion discr; auto. congruence.
- split;intros. 
  + destruct H as (t' & Pt' & tt').
    subst. exists false. split. exists true. split. assumption. constructor.
    reflexivity.
  + destruct H as ([] & ([] & Pt & discr) & ttrue);
    exists true; inversion discr; auto. congruence.
Qed.

Require Import Qcanon.
Close Scope Qc.
Lemma phalf : (Qnnonehalf = 1 - Qnnonehalf)%Qnn.
Proof.
apply Qnneq_prop. unfold Qnneq. apply Qceq_alt.
reflexivity. 
Qed.

Require Import FunctionalExtensionality.
Theorem OTP : forall (b : bool),
  Val.map (bfunc (xorb b)) faircoin = faircoin.
Proof.
intros. symmetry. destruct b. change (xorb true) with negb.
apply reverse. simpl. apply Qnneq_prop. unfold Qnneq. apply Qceq_alt.
reflexivity. 
replace (xorb false) with (@id bool).
simpl. unfold bfunc. apply Val.eq_compat. unfold Val.eq; intros.
simpl.
rewrite <- phalf.
apply LPRpluseq2; apply LPRind_iff; unfold Cont.frame.
- split; intros.
  + destruct H as (t & Pt & eqt). subst. exists true. split.
    exists true. split. assumption. constructor. reflexivity.
  + destruct H as ([] & ([] & Pt & discr) & ttrue);
    exists true; inversion discr; auto. congruence.
- split; intros.
  + destruct H as (t' & Pt' & tt').
    subst. exists false. split. exists false. split. assumption. constructor.
    reflexivity.
  + destruct H as ([] & ([] & Pt & discr) & ttrue);
    exists false; inversion discr; auto. congruence.
- apply functional_extensionality.
  intros []; reflexivity.
Qed.

Require Import BinNums Crypto.Spec.ModularArithmetic
  Crypto.ModularArithmetic.ModularArithmeticTheorems
  BinNat BinInt
  Eqdep_dec.

Require Iso.
Local Close Scope LPR.

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

Section Finite.
Require Finite.

Instance DOps A : Frame.Ops (A -> Prop) := FormTop.FOps Logic.eq (Discrete.Cov A).

Instance DiscretePreO (A : Type) :  PreO.t A eq := PreO.discrete A.
Instance DiscreteFrame (A : Type) : F.t (A -> Prop) (opsA A) := frameA A.


Definition Ffunc {A B} (f : A -> B) : Frame.cmap (DOps A) (DOps B) :=
  Cont.toCmap (Discrete.isCov A) (Discrete.isCov B) (Discrete.discrF f) (Discrete.fCont f).

Fixpoint build_finite {A : Type} (fin : Finite.T A) : (A -> LPReal) -> Val.t (frameA A)
  := match fin with
  | Finite.F0 => fun _ => 0%Val
  | Finite.FS _ fin' => fun f =>
     (f (inl I) * Val.unit (point (inl I)) + Val.map (Ffunc inr) (build_finite fin' (fun x => f (inr x))))%Val
  | Finite.FIso _ _ fin' t => fun f =>
     Val.map (Ffunc (Iso.to t)) (build_finite fin' (fun x => f (Iso.to t x)))
  end.

Lemma discrete_inj {A B} (f : A -> B) (inj_f : forall x y, f x = f y -> x = y) (x : A) : 
  L.eq (eq x) (Cont.frame (Discrete.discrF f) (eq (f x))).
Proof.
simpl. unfold FormTop.eqA, FormTop.Sat, Discrete.Cov, Cont.frame,
  Discrete.discrF. intros; split; intros. subst.
  exists (f s). auto. destruct H as (t' & fx & fs). 
  apply inj_f. congruence.
Qed.

Local Open Scope LPR.

Fixpoint sum_finite {A} (fin : Finite.T A) : (A -> LPReal) -> LPReal
  := match fin with
  | Finite.F0 => fun _ => 0
  | Finite.FS _ fin' => fun f => f (inl I) + sum_finite fin' (fun x => f (inr x))
  | Finite.FIso _ _ fin' i => fun f => sum_finite fin' (fun x => f (Iso.to i x))
  end.

Theorem sum_finite_equiv {A} (fin : Finite.T A) : forall f g,
  (forall a, f a = g a) -> sum_finite fin f = sum_finite fin g.
Proof.
induction fin; intros; simpl.
- reflexivity.
- rewrite (IHfin (fun x => f (inr x)) (fun x => g (inr x))). rewrite H. reflexivity.
  intros. apply H.
- erewrite IHfin. reflexivity. simpl. intros. apply H.
Qed.

Definition sum_finite_subset {A} (fin : Finite.T A) (P : A -> Prop) (f : A -> LPReal)
  := sum_finite fin (fun x => LPRindicator (P x) * f x)%LPR.

Theorem sum_finite_subset_le {A} fin : forall (P Q : A -> Prop) f, (forall a, P a -> Q a)
  -> sum_finite_subset fin P f <= sum_finite_subset fin Q f.
Proof.
induction fin; unfold sum_finite_subset; intros; simpl.
- apply LPRle_refl.
- apply LPRplus_le_compat. apply LPRmult_le_compat. apply LPRind_imp. apply H.
  apply LPRle_refl. apply IHfin. intros. apply H. assumption.
- apply IHfin. intros. apply H. assumption.
Qed.

Theorem iso_true_subset {A} : Iso.T A (sig (fun _ : A => True)).
Proof. refine (
  {| Iso.to := fun a => exist _ a I
   ; Iso.from := fun ea => let (a, _) := ea in a |}
); intros.
reflexivity. destruct b. destruct t. reflexivity.
Defined.

Require Import ProofIrrelevance.
Theorem fin_dec_subset {A} (fin : Finite.T A) {P : A -> Prop}
  : (forall a, {P a} + {~ P a}) -> Finite.T (sig P).
Proof.
generalize dependent P. induction fin; intros P decP.
- eapply Finite.FIso. apply Finite.F0.
  eapply Iso.Trans. apply iso_true_subset. 
  apply Iso.subsetSelf; firstorder.
- destruct (decP (inl I)). 
  + admit. 
  + eapply Finite.FIso.
    apply (IHfin (fun a => P (inr a))). intros. apply decP.
    admit.
- eapply Finite.FIso. apply (IHfin (fun a => P (Iso.to t a))). 
  intros. apply decP. apply Iso.subset with t; firstorder.
  rewrite Iso.to_from. assumption. apply proof_irrelevance.
  apply proof_irrelevance.
Admitted.

Theorem sum_finite_subset_dec_equiv {A} (fin : Finite.T A)
  (P : A -> Prop) (decP : forall a, {P a} + {~ P a}) (f : A -> LPReal)
  : sum_finite_subset fin P f =
    sum_finite (fin_dec_subset fin decP) (fun x => f (projT1 x)).
Proof.
Admitted.

Theorem sum_finite_iso {A B} (fin : Finite.T A) (f : A -> LPReal)
 (i : Iso.T A B) : sum_finite fin f = sum_finite 
  (Finite.FIso fin i) (fun y => f (Iso.from i y)).
Proof.
simpl. apply sum_finite_equiv.
intros. rewrite Iso.from_to. reflexivity.
Qed.

Theorem sum_finite_subset_iso {A B} (fin : Finite.T A) (P : A -> Prop) (f : A -> LPReal)
 (i : Iso.T A B) : sum_finite_subset fin P f = sum_finite_subset 
  (Finite.FIso fin i) (fun y => P (Iso.from i y)) (fun y => f (Iso.from i y)).
Proof.
unfold sum_finite_subset. simpl. apply sum_finite_equiv.
intros. rewrite Iso.from_to. reflexivity.
Qed.

Lemma LPRpluseq3 : forall (p a a' b b' : LPReal),
  a = a' -> b = b' ->
  (a * p + b = a' * p + b')%LPR.
Proof.
intros. subst. ring.
Qed.

Lemma discrete_subset : forall {A B} (f : A -> B) a b,
  Cont.frame (Discrete.discrF f) (eq b) a <-> f a = b.
Proof.
intros. unfold Cont.frame, Discrete.discrF.
split; intros. destruct H as (t' & bt' & fat'). congruence.
exists b. auto.
Qed.

Lemma build_finite_char {A} (fin : Finite.T A) (f : A -> LPReal)
  (P : A -> Prop) : build_finite fin f P = sum_finite_subset fin P f.
Proof.
induction fin. 
- simpl. reflexivity.
- simpl. unfold Cont.frame. rewrite IHfin.
  rewrite (SRmul_comm LPRsrt (f (inl I))).
  apply LPRpluseq3. apply LPRind_iff.
  split; intros. destruct H as (t' & Ptt & tinl).
  subst. assumption. exists (inl I). auto.
  assert (forall f g, f = g -> sum_finite fin f = sum_finite fin g) by
   (intros; subst; auto).
  apply H. clear H. apply functional_extensionality. intros.
  apply LPRmult_eq_compat. apply LPRind_iff. unfold Discrete.discrF.
  split; intros. destruct H as (t & Pt & inrt). subst. assumption.
  exists (inr x). auto. auto.
- simpl. rewrite IHfin. 
    assert (forall f g, f = g -> sum_finite fin f = sum_finite fin g) by
   (intros; subst; auto).
  apply H. clear H. apply functional_extensionality. intros.
  apply LPRmult_eq_compat. apply LPRind_iff. unfold Cont.frame, Discrete.discrF.
  split; intros. destruct H as (t' & Pt' & tt').
  subst. assumption. exists (Iso.to t x). auto. auto.
Qed.

Definition build_finite_ok {A} (fin : Finite.T A) (f : A -> LPReal) (x : A) :
  build_finite fin f (eq x) = f x.
Proof. 
induction fin.
- contradiction. 
- destruct x.
  + destruct t. simpl. unfold Cont.frame.
    rewrite LPRind_true.
    erewrite Val.val_iff. rewrite Val.strict. ring.
    simpl. unfold FormTop.eqA, FormTop.supA, FormTop.Sat, Discrete.Cov.
    intros s. split; intros.
    destruct H as (t' & int' & invt').
    induction invt'. congruence. destruct H. contradiction.
    eexists; auto.
  + simpl. rewrite LPRind_false.
    rewrite <- discrete_inj.
    rewrite IHfin. ring. congruence.
    unfold not. unfold Cont.frame. intros.
    destruct H as (t' & inrt' & inlt'). congruence.
- rewrite <- (Iso.to_from t x) at 1. simpl.
  rewrite <- (discrete_inj (Iso.to t)).
  rewrite IHfin. rewrite Iso.to_from. reflexivity.
  intros. rewrite <- (Iso.from_to t). rewrite <- H.
  rewrite (Iso.from_to t). reflexivity.
Qed.

(** With the right principles this should become easy. *)
Lemma fin_char {A : Type} : forall (fin : Finite.T A) (mu : Val.t (frameA A)),
  mu = build_finite fin (fun a => mu (eq a)).
Proof.
intros. induction fin; apply Val.eq_compat; unfold Val.eq; simpl; intros P.
- erewrite Val.val_iff. apply Val.strict. simpl. 
  unfold FormTop.eqA, FormTop.supA, FormTop.Sat, Discrete.Cov.
  intros s. contradiction.
Admitted.

Lemma fin_dec {A : Type} : forall (fin : Finite.T A)
  (mu nu : Val.t (frameA A))
  , (forall (a : A), mu (eq a) = nu (eq a))
  -> mu = nu.
Proof.
intros. rewrite (fin_char fin mu). rewrite (fin_char fin nu).
apply functional_extensionality in H. rewrite H. reflexivity.
Qed.

End Finite.

Section OneTimePad.

Context {n : nat}.

Let N := Z.of_nat (S n). 
  Definition ring_theory_modulo := @Fring_theory N.
  Definition ring_morph_modulo := @Fring_morph N.
  Definition morph_div_theory_modulo := @Fmorph_div_theory N.
  Definition power_theory_modulo := @Fpower_theory N.

  Add Ring GFring_Z : ring_theory_modulo
    (morphism ring_morph_modulo,
     constants [Fconstant],
     div morph_div_theory_modulo,
     power_tac power_theory_modulo [Fexp_tac]).

Theorem perm : forall (x z : F N), exists (y : F N),
  (x + y = z)%F.
Proof.
intros. exists (z - x)%F. ring.
Qed.

Definition plus2 (p : F N * F N) : F N := let (x, y) := p
  in (x + y)%F.

Definition iso : Iso.T (F N) (Fin.t (S n)) := finiteF n.

Lemma finiteFN : Finite.T (F N).
Proof.
eapply Finite.FIso. 2: eapply Iso.Sym; apply iso.
apply Finite.fin.
Defined.

Definition uniformFN : Val.t (frameA (F N)) :=
  build_finite finiteFN (fun _ => LPRQnn (Qnnfrac (S n))).

Definition uniformFN' : Val.t (frameA (F N)) := uniformF (F N) (Iso.from iso).

Lemma plus_inj (x : F N) : let f y := (x + y)%F in
  forall a b, f a = f b -> a = b.
Proof.
simpl. intros. eapply F_add_reg_l. eassumption.
Qed.

Theorem OPTFN : forall (x : F N),
  Val.map (Ffunc (fun y => x + y))%F uniformFN = uniformFN.
Proof.
intros. apply fin_dec. apply finiteFN.
intros. simpl. rewrite <- (Iso.from_to iso a) at 2.
rewrite <- (discrete_inj (Iso.from iso)).
rewrite build_finite_ok.
replace a with (x + (a - x))%F by ring.
pose proof (discrete_inj (fun y => (x + y)%F) (plus_inj x)) as dinj.
assert (forall x0, (eq x0) = (Cont.frame (Discrete.discrF (fun y : F N => (x + y)%F))
              (eq ((fun y : F N => (x + y)%F) x0))))
  by admit.
(** This is not in fact true. They are equal according to L.eq but not
    eq. However, there's some complicated rewriting to do, depending on
    getting good "Proper" instances for frame morphisms, and I haven't
    gotten to work yet.
    Should be able to do
    rewrite <- (discrete_inj (fun y => (x + y)%F))
    once this works. *)
clear dinj. rewrite <- H.
rewrite <- (Iso.from_to iso (a - x)%F).
rewrite <- (discrete_inj (Iso.from iso)).
rewrite build_finite_ok. reflexivity.
intros. rewrite <- (Iso.to_from iso). rewrite <- H0.
rewrite (Iso.to_from iso). reflexivity.
intros. rewrite <- (Iso.to_from iso). rewrite <- H.
rewrite (Iso.to_from iso). reflexivity.
Qed.

Definition build_finite_prod {A B} (fin : Finite.T (A * B))
  (f : A -> LPReal) (g : B -> LPReal) :=
  build_finite fin (fun z => let (x, y) := z in (f x * g y)%LPR).

Lemma sum_finite_const {A} {fin : Finite.T A} {c : LPReal} :
  sum_finite fin (fun _ => c) = (LPRQnn (Qnnnat (Finite.card fin)) * c)%LPR.
Proof.
induction fin; simpl.
- ring.
- rewrite IHfin. rewrite <- LPRQnn_plus. ring.
- assumption.
Qed.

Lemma map_build_finite {A B} {finA : Finite.T A} {finB : Finite.T B}
  : forall (f : A -> B) (mu : Val.t (frameA A)) y
  , let _ : F.t (B -> Prop) (DOps B) := frameA B in
    Val.map (Ffunc f) mu (eq y)
  = sum_finite_subset finA (fun x => f x = y) (fun x => mu (eq x)).
Proof.
intros. simpl. rewrite (fin_char finA mu) at 1.
rewrite build_finite_char.
    assert (forall f g, f = g -> sum_finite finA f = sum_finite finA g) by
   (intros; subst; auto).
apply H; clear H; apply functional_extensionality; intros a.
apply LPRmult_eq_compat; try reflexivity. apply LPRind_iff.
apply discrete_subset.
Qed.

Definition finiteFN2 : Finite.T (F N * F N) := 
  Finite.times finiteFN finiteFN.

Lemma pair_eq : forall A B (a a' : A) (b b' : B), a = a' -> b = b' -> (a, b) = (a', b').
Proof.
intros; subst; reflexivity.
Qed.

Theorem group_action_l : forall z, 
  Iso.T (sig (fun p : F N * F N => plus2 p = z)) (F N).
Proof.
intros.
assert (forall x, plus2 (x, z - x) = z)%F as eqprf.
intros. unfold plus2. ring.
 refine (
  {| Iso.to := fun p : (sig (fun p' => plus2 p' = z)) => let (x, y) := projT1 p in (z - y)%F
   ; Iso.from := fun x => exist _ (x, z - x)%F (eqprf x)
  |}).
- intros. apply Iso.sig_eq. intros. apply UIP_dec. apply F_eq_dec.
  simpl. destruct a. simpl. destruct x. simpl. unfold plus2 in e. rewrite <- e.
  apply pair_eq; ring.
- intros. simpl. ring.
Defined.

Theorem sum_finite_subset_eq :
  forall (A : Type) (fin : Finite.T A) (P Q : A -> Prop) (f : A -> LPReal),
  (forall a : A, P a <-> Q a) ->
  sum_finite_subset fin P f = sum_finite_subset fin Q f.
Proof.
intros. apply LPRle_antisym; apply sum_finite_subset_le; firstorder.
Qed.

Local Open Scope LPR.

Theorem sum_finite_scales : forall A (fin : Finite.T A) f c, 
    sum_finite fin (fun x => c * f x)
  = c * sum_finite fin f.
Proof.
intros A fin. induction fin; simpl; intros.
- ring.
- rewrite IHfin. ring.
- apply IHfin.
Qed.

Theorem sum_finite_fin_equiv : forall A (fin1 fin2 : Finite.T A) f,
  sum_finite fin1 f = sum_finite fin2 f.
Proof.
Admitted.

Theorem OTPGood : forall f,
  sum_finite finiteFN f = 1%LPR ->
  Val.map (Ffunc plus2) 
    (build_finite_prod finiteFN2
    f (fun _ => LPRQnn (Qnnfrac (S n)))) = uniformFN.
Proof.
intros. apply fin_dec. apply finiteFN.
intros x. unfold uniformFN. rewrite build_finite_ok.
unfold build_finite_prod. rewrite (@map_build_finite _ _ finiteFN2 finiteFN).
rewrite (sum_finite_subset_dec_equiv _ _ (fun x => F_eq_dec _ _)).
rewrite (sum_finite_iso _ _ (group_action_l x)). 
erewrite sum_finite_equiv. 
Focus 2. intros.  simpl. 
replace 
  (Cont.frame
        (Discrete.discrF
           (fun p : {_ : F N & F N} => let (x0, y) := p in (x0, y)))
        (eq (a, (x - a)%F)))
  with
  (eq (existT (fun _ => F N) a (x - a)))%F
  by admit. rewrite build_finite_ok.
  reflexivity.
erewrite sum_finite_equiv. Focus 2. intros.
rewrite (SRmul_comm LPRsrt). reflexivity.
rewrite sum_finite_scales.
rewrite (sum_finite_fin_equiv _ _ finiteFN).
rewrite H. ring.
Qed.

End OneTimePad.