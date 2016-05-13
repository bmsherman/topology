Require Import Numbers.LPReal.

Require Types.Finite Types.Iso.

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
- reflexivity.
- apply LPRplus_le_compat. apply LPRmult_le_compat. apply LPRind_imp. apply H.
  reflexivity. apply IHfin. intros. apply H. assumption.
- apply IHfin. intros. apply H. assumption.
Qed.

Require Import ProofIrrelevance Ring.

Theorem sum_finite_subset_dec_equiv {A} (fin : Finite.T A)
  (P : A -> Prop) (decP : forall a, {P a} + {~ P a}) (f : A -> LPReal)
  : sum_finite_subset fin P f =
    sum_finite (Finite.fin_dec_subset fin decP) (fun x => f (projT1 x)).
Proof.
unfold sum_finite_subset.
induction fin.
- simpl. reflexivity.
- simpl. destruct (decP (inl I)); simpl.
  + rewrite LPRind_true by assumption. ring_simplify.
    apply LPRplus_eq_compat. reflexivity.
    erewrite IHfin. apply sum_finite_equiv.
    intros. destruct a. simpl. reflexivity.
  + rewrite LPRind_false by assumption. ring_simplify.
    erewrite IHfin. apply sum_finite_equiv.
    intros.  destruct a. simpl. reflexivity. 
- simpl. erewrite IHfin. apply sum_finite_equiv.
  intros. destruct a. simpl. reflexivity.
Qed.

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

Theorem sum_finite_scales : forall A (fin : Finite.T A) f c, 
    sum_finite fin (fun x => c * f x)
  = c * sum_finite fin f.
Proof.
intros A fin. induction fin; simpl; intros.
- ring.
- rewrite IHfin. ring.
- apply IHfin.
Qed.

Theorem sum_finite_adds {A} (fin : Finite.T A) :
  forall (f g : A -> LPReal),
  sum_finite fin (fun x => f x + g x) 
  = sum_finite fin f + sum_finite fin g.
Proof.
induction fin; intros; simpl.
- ring.
- rewrite IHfin. ring.
- rewrite IHfin. ring.
Qed.

Require Import Numbers.Qnn.

Lemma sum_finite_const {A} {fin : Finite.T A} {c : LPReal} :
  sum_finite fin (fun _ => c) = (LPRQnn (Qnnnat (Finite.card fin)) * c)%LPR.
Proof.
induction fin; simpl.
- ring.
- rewrite IHfin. rewrite <- LPRQnn_plus. ring.
- assumption.
Qed.

Lemma sum_finite_pt {A} (fin : Finite.T A) :
  forall (x : A),
  sum_finite fin (fun y => LPRindicator (x = y)) = 1.
Proof.
induction fin; intros.
- contradiction.
- simpl. destruct x.
  + destruct t. rewrite LPRind_true by reflexivity.
    rewrite (sum_finite_equiv _ _ (fun _ => 0)).
    rewrite sum_finite_const. ring. intros.
    rewrite LPRind_false by congruence. reflexivity.
  + rewrite LPRind_false by congruence.
    rewrite (sum_finite_equiv _ _ (fun x => LPRindicator (a = x))).
    rewrite IHfin. ring.
    intros. apply LPRind_iff. split; congruence.
- simpl. rewrite <- (IHfin (Iso.from t x)).
  apply sum_finite_equiv. intros.
  apply LPRind_iff. split; intros; subst.
  apply Iso.from_to. symmetry. apply Iso.to_from.
Qed.

Lemma sum_finite_char {A} (fin : Finite.T A) :
  forall (f : A -> LPReal) x,
  f x = sum_finite fin (fun y => LPRindicator (x = y) * f y).
Proof.
intros.
assert (forall y, LPRindicator (x = y) * f y = f x * LPRindicator (x = y)).
intros. rewrite (SRmul_comm LPRsrt (f x)).
apply LPRle_antisym; apply LPRind_scale_le; intros; subst;
  rewrite LPRind_true by trivial; ring_simplify; apply LPRle_refl.
erewrite sum_finite_equiv.
2: apply H.
rewrite sum_finite_scales. rewrite sum_finite_pt.
ring.
Qed.


Theorem sum_finite_subset_eq :
  forall (A : Type) (fin : Finite.T A) (P Q : A -> Prop) (f : A -> LPReal),
  (forall a : A, P a <-> Q a) ->
  sum_finite_subset fin P f = sum_finite_subset fin Q f.
Proof.
intros. apply LPRle_antisym; apply sum_finite_subset_le; firstorder.
Qed.

Theorem sum_finite_fin_equiv : forall A (fin1 fin2 : Finite.T A) f,
  sum_finite fin1 f = sum_finite fin2 f.
Proof.
intros.
erewrite sum_finite_equiv. Focus 2. intros.
rewrite (sum_finite_char fin2). reflexivity.
induction fin2; simpl.
- rewrite sum_finite_const. ring.
- rewrite sum_finite_adds. erewrite sum_finite_equiv.
  Focus 2. intros. rewrite (SRmul_comm LPRsrt).
  rewrite (LPRind_iff _ (inl I = a)) by (split; auto). 
  reflexivity.
  rewrite sum_finite_scales. rewrite sum_finite_pt.
  apply LPRplus_eq_compat. ring.
  admit.
- admit.
Admitted.