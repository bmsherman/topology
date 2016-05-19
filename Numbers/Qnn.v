Require Import QFacts QArith Qcanon.

Require Import FunctionalExtensionality.

(** Non-negative rational numbers *)
(** Nothing here should be too surprising.
    Non-negative rationals, [Qnn] are represented by rational numbers
    in reduced form together with proofs that the rational numbers
    are non-negative. Using functional extensionality, these numbers
    are Leibniz equal whenever the rational numbers they represent are equal.

    There is a subtraction operation, [Qnnminus], which implements
    a truncated subtraction; if the result should have been negative, it will
    instead be zero. Lemmas show that it behaves nicely when we indeed
    subtracted a smaller number from a larger one.

    Division in [Qnn] is handled as in [Qc]: we arbitrarily have 0 / 0 = 0.

    We prove [Qnn] forms a semiring.

    Many definitions and lemmas from [Qc] are essentially reproduced, perhaps
    in an alterned form for the modified settings where all numbers are 
    non-negative.

    Axioms required:
    - functional extensionality: the proof of less-than-or-equal
      for [Z] is a negation, and to prove that any two negations are equal,
      we require functional extensionality.  *)

Record Qnn :=
  { qnn :> Qc
  ; nonneg : 0 <= qnn
  }.

Local Open Scope Z.

(** Proof irrelevance for <= on [Z], assuming
    functional extensionality. *)
Theorem Zle_irrel {x y : Z} (prf1 prf2 : x <= y) :
  prf1 = prf2. 
Proof. unfold Z.le in *.
extensionality z; contradiction.
Qed.

Local Close Scope Z.
Local Close Scope Qc.

Definition Qle_irrel {x y : Q} (prf1 prf2 : x <= y)
  : prf1 = prf2 := Zle_irrel prf1 prf2.

Local Open Scope Qc.
Definition Qcle_irrel {x y : Qc} (prf1 prf2 : x <= y)
  : prf1 = prf2 := Qle_irrel prf1 prf2.

(** Comparison operators for [Qnn] simply reduce to those for
    [Qc]. *)
Definition Qnnle (x y : Qnn) : Prop := x <= y.
Definition Qnnge (x y : Qnn) : Prop := Qnnle y x.
Definition Qnnlt (x y : Qnn) : Prop := x < y.
Definition Qnngt (x y : Qnn) : Prop := Qnnlt y x.

Definition Qnneq (x y : Qnn) : Prop := qnn x = qnn y.

Definition Qnnplus (x y : Qnn) : Qnn.
Proof.
refine ({| qnn := x + y |}).
abstract (replace 0 with (0 + 0) by field;
apply Qcplus_le_compat; destruct x, y; assumption).
Defined.

Definition Qnnmult (x y : Qnn) : Qnn.
Proof.
refine ({| qnn := x * y |}).
abstract (
replace 0 with (0 * y) by field;
apply Qcmult_le_compat_r; apply nonneg).
Defined.

Definition Qnnzero : Qnn := Build_Qnn 0%Qc (Qcle_refl 0%Qc).

Ltac makeQnn q := apply (Build_Qnn q); 
  abstract (unfold Qcle, Qle, Z.le; simpl; congruence).

Definition Qnnone : Qnn.
Proof. makeQnn 1.
Defined.

Definition Qnnonehalf : Qnn.
Proof. makeQnn (Qcmake (1 # 2) eq_refl).
Defined.

(** If two [Qnn]s have the same [Qc] values, they are
    Leibniz equal. *)
Theorem Qnneq_prop {x y : Qnn} :
  Qnneq x y -> x = y.
Proof. intros. destruct x, y. unfold Qnneq in H. simpl in H.
induction H. replace nonneg0 with nonneg1 by (apply Qcle_irrel).
reflexivity.
Qed.

Infix "<=" := Qnnle   : Qnn_scope.
Infix ">=" := Qnnge   : Qnn_scope.
Infix "<"  := Qnnlt   : Qnn_scope.
Infix ">"  := Qnngt   : Qnn_scope.
Infix "+"  := Qnnplus : Qnn_scope.
Infix "*"  := Qnnmult : Qnn_scope.
Infix "==" := Qnneq   : Qnn_scope.

Notation "'0'" := Qnnzero : Qnn_scope.
Notation "'1'" := Qnnone  : Qnn_scope.

Require Import Ring.

Local Close Scope Q.
Local Close Scope Qc.

Delimit Scope Qnn_scope with Qnn.

Local Open Scope Qnn.

Require Import QArith.Qminmax.

Definition Qnn_truncate (q : Q) : Qnn.
Proof.
refine {| qnn := !! (Qmax 0 q) |}.
unfold Qcle. simpl. rewrite Qred_correct.
apply Q.le_max_l.
Defined.

(** Non-negative rational numbers form a semiring *)
Theorem Qnnsrt : semi_ring_theory 0 1
  Qnnplus Qnnmult eq.
Proof.
constructor; intros;
  match goal with
  | [  |- _ = _ ] => apply Qnneq_prop; unfold Qnneq
  end;
  try solve[simpl; field].
Qed.

Add Ring Qnn_Ring : Qnnsrt.

Theorem Qnn_zero_prop {x : Qnn} :
  x <= 0 -> x = Qnnzero.
Proof.
intros. apply Qnneq_prop. unfold Qnneq.
unfold Qnnzero. simpl. apply Qcle_antisym.
assumption. apply nonneg.
Qed.

Lemma Qnnle_refl (x : Qnn) : x <= x.
Proof. apply Qcle_refl. Qed.

Lemma Qnnle_trans {x y z : Qnn}
  : x <= y -> y <= z -> x <= z.
Proof. intros. eapply Qcle_trans; eassumption. Qed.

Instance Qnnle_preorder : PreOrder Qnnle.
Proof.
constructor.
- unfold Reflexive. apply Qnnle_refl.
- unfold Transitive. apply @Qnnle_trans.
Qed.

Lemma Qnnle_antisym {x y : Qnn}
  : x <= y -> y <= x -> x = y.
Proof. intros. apply Qnneq_prop. eapply Qcle_antisym; eassumption. Qed.

Definition Qnnle_irrel {x y : Qnn} (prf1 prf2 : x <= y)
  : prf1 = prf2 := Qcle_irrel prf1 prf2.

Lemma Qnnle_lt_trans : forall x y z : Qnn
  , x <= y -> y < z -> x < z.
Proof. intros. eapply Qcle_lt_trans; eassumption. Qed.

Lemma Qnnlt_le_trans: forall x y z : Qnn
  , x < y -> y <= z -> x < z.
Proof. intros. eapply Qclt_le_trans; eassumption. Qed.

Definition Qnncompare (x y : Qnn) := (x ?= y)%Qc.

Infix "?=" := Qnncompare : Qnn_scope.

Lemma Qnnlt_alt {x y : Qnn} : (x ?= y) = Lt <-> x < y.
split; intros; apply Qclt_alt; assumption.
Qed. 

Lemma Qnngt_alt {x y : Qnn} : (x ?= y) = Gt <-> x > y.
split; intros; unfold Qnngt; apply Qcgt_alt; assumption.
Qed. 

Lemma Qnneq_alt {x y : Qnn} : (x ?= y) = Eq <-> x = y.
split; intros. apply Qnneq_prop. apply Qceq_alt; assumption.
apply Qceq_alt. induction H. reflexivity.
Qed. 

Lemma Qnnmult_le_compat {x y x' y' : Qnn}
  : x <= x' -> y <= y' -> x * y <= x' * y'.
Proof. intros.
assert (x * y <= x' * y).
apply Qcmult_le_compat_r. assumption. apply nonneg.
rewrite H1.
replace (x' * y) with (y * x') by ring.
replace (x' * y') with (y' * x') by ring.
apply Qcmult_le_compat_r. assumption. apply nonneg.
Qed.

Instance Qnnmult_le_compatI : Proper (Qnnle ==> Qnnle ==> Qnnle) Qnnmult.
Proof.
unfold Proper, respectful. intros. apply Qnnmult_le_compat; assumption.
Qed.

Lemma Qnnlt_zero_prop {q : Qnn} : ~(q < 0).
Proof. unfold not; intros contra.
assert (q = 0). apply Qnnle_antisym.
apply Qclt_le_weak. assumption.
apply nonneg.
eapply Qclt_not_eq. eassumption.
rewrite H. reflexivity.
Qed.

Definition Qnnmax (x y : Qnn) : Qnn := match x ?= y with 
   | Lt => y
   | Eq => x
   | Gt => x
   end.

Lemma Qnnmax_induction {x y} (P : Qnn -> Qnn -> Qnn -> Prop) :
  (y <= x -> P x y x) -> (x <= y -> P x y y) -> P x y (Qnnmax x y).
Proof.
intros. unfold Qnnmax. destruct (x ?= y) eqn:ceqn. 
  apply H. apply Qnneq_alt in ceqn. rewrite ceqn. apply Qnnle_refl.
  apply H0. apply Qclt_le_weak. apply Qnnlt_alt. assumption.
  apply H. apply Qnngt_alt in ceqn. apply Qclt_le_weak. assumption.
Qed.

Lemma Qnnmax_mult {x y z} : x * Qnnmax y z = Qnnmax (x * y) (x * z).
Proof. 
pattern y, z, (Qnnmax y z). apply Qnnmax_induction; intros.
- pattern (x * y), (x * z), (Qnnmax (x * y) (x * z)). 
  apply Qnnmax_induction; intros. reflexivity.
  apply Qnnle_antisym. assumption. apply Qnnmult_le_compat.
  reflexivity. assumption.
- pattern (x * y), (x * z), (Qnnmax (x * y) (x * z)). 
  apply Qnnmax_induction; intros.
  apply Qnnle_antisym. assumption. apply Qnnmult_le_compat.
  reflexivity. assumption. reflexivity.
Qed.

Lemma Qnnmax_l {x y} : x <= Qnnmax x y.
Proof. unfold Qnnmax; simpl. destruct (x ?= y) eqn:compare; simpl. 
- reflexivity.
- apply Qclt_le_weak. apply Qnnlt_alt. assumption.
- reflexivity.
Qed.

Lemma Qnnmax_r {x y} : y <= Qnnmax x y.
Proof. unfold Qnnmax; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnneq_alt in compare. induction compare. reflexivity.
- reflexivity. 
- apply Qclt_le_weak. apply Qnngt_alt. assumption.
Qed.

Lemma Qnninv_nonneg (x : Qnn) : (0 <= / x)%Qc.
Proof.
destruct (x ?= 0) eqn:comp. apply Qnneq_alt in comp.
subst. simpl. apply Qle_refl.
apply Qnnlt_alt in comp. apply Qnnlt_zero_prop in comp.
contradiction.
unfold Qcle. 
setoid_replace (this (/ x)%Qc) with (/ x)%Q by apply Qred_correct.
apply Qinv_le_0_compat. apply nonneg.
Qed.

Definition Qnninv (x : Qnn) : Qnn :=
  {| qnn := (/ x)%Qc
   ; nonneg := Qnninv_nonneg x
  |}.

Notation "/ x" := (Qnninv x) : Qnn_scope.

Lemma Qnn_dec (x y : Qnn) : {x < y} + {y < x} + {x = y}.
Proof. destruct (Qc_dec x y).
left. destruct s. left. assumption. right. assumption.
right. apply Qnneq_prop. assumption.
Qed. 

Lemma Qnnzero_prop2 (x : Qnn) : x > 0 <-> x <> 0.
Proof.
split; intros. unfold not. intros contra. subst. 
apply Qnnlt_zero_prop in H. assumption.
destruct (Qnn_dec x 0). destruct s.
apply Qnnlt_zero_prop in q. contradiction. assumption.
subst. unfold not in H. pose proof (H eq_refl). contradiction.
Qed.

Lemma Qnnmult_inv_r (x : Qnn) :
  x > 0 -> x * Qnninv x = 1.
Proof. intros. 
apply Qnneq_prop. apply Qcmult_inv_r. apply Qnnzero_prop2 in H.
unfold not. intros contra. assert (x = 0). apply Qnneq_prop. assumption.
contradiction. 
Qed.


Lemma Qnninv_zero1 {x : Qnn} : / x = 0 -> x = 0.
Proof. intros. destruct (x ?= 0) eqn:comp.
apply Qnneq_alt in comp. assumption.
apply Qnnle_antisym. apply Qclt_le_weak. assumption. apply nonneg.
apply Qnngt_alt in comp. replace x with (x * 1) by ring.
replace 1 with (Qnninv x * x). rewrite H. ring.
rewrite (SRmul_comm Qnnsrt).
apply Qnnmult_inv_r. assumption.
Qed. 

Lemma Qnninv_zero2 {x : Qnn} : 0 < x -> 0 < / x.
Proof. intros. apply Qnnzero_prop2. unfold not. intros contra.
apply Qnninv_zero1 in contra. subst. apply Qnnzero_prop2 in H. 
unfold not in H. apply H. reflexivity. 
Qed.

Definition Qnndiv (x y : Qnn) : Qnn := x * / y.

Infix "/" := Qnndiv : Qnn_scope.

Lemma Qnndiv_lt (num denom : Qnn) : num < denom -> num / denom < 1.
Proof. intros. unfold Qnndiv.
destruct (num ?= 0) eqn:comp. apply Qnneq_alt in comp.
subst. replace (0 * / denom) with 0 by ring. unfold Qnnlt. 
apply Qclt_alt. reflexivity.

apply Qnnlt_alt in comp. apply Qnnlt_zero_prop in comp. contradiction.

apply Qnngt_alt in comp. replace 1 with (denom * / denom).
apply Qcmult_lt_compat_r.
apply Qnninv_zero2. eapply Qnnle_lt_trans. apply (nonneg num). assumption.
assumption. 
apply Qnnmult_inv_r. eapply Qnnle_lt_trans. apply (nonneg num). assumption.
Qed. 

Ltac reduceQ := repeat (unfold Qcplus, Qcdiv, Qcinv, Qcmult; 
match goal with
| [ |- context[this (Q2Qc ?x)%Qc] ] => 
     setoid_replace (this (Q2Qc x)%Qc) with x by (apply Qred_correct)
end).


Definition Qcaverage (x z : Qc) : (x < z)%Qc
  -> (let avg := ((x + z) / (1 + 1)) in x < avg /\ avg < z)%Qc.
Proof. intros. destruct (Qaverage x z H).
assert ((this avg == (x + z) / (1 + 1))%Q). 
unfold avg. reduceQ. reflexivity.
unfold Qclt. split; setoid_rewrite H2; assumption.
Qed. 

Definition Qnnaverage (x z : Qnn) : (x < z)
  -> (let avg := ((x + z) * Qnnonehalf) in x < avg /\ avg < z).
Proof. intros.
pose proof (Qcaverage x z H).
assert (qnn avg = ((x + z) / (1 + 1))%Qc).
unfold avg. unfold Qcdiv. unfold Qnnmult. simpl. reflexivity.
unfold Qnnlt; rewrite H1. assumption.
Qed.

Definition Qcbetween (x z : Qc) : (x < z)%Qc
  -> { y | (x < y /\ y < z)%Qc }.
Proof. intros. eexists. apply Qcaverage. assumption.
Qed.

Definition Qnnbetween (x z : Qnn) : (x < z)
  -> { y | x < y /\ y < z }.
Proof. intros. eexists. apply Qnnaverage. assumption.
Qed.

Definition Qnnplus_le_lt_compat {x x' y y' : Qnn}
  : x <= x' -> y < y' -> x + y < x' + y'.
Proof.
intros.
apply Qclt_minus_iff. simpl.
eapply Qclt_le_trans.
apply Qclt_minus_iff in H0. eassumption.
replace (x' + y' + - (x + y))%Qc with (y' + - y + (x' + - x))%Qc by ring.
replace (y' + -y)%Qc with (y' + -y + 0)%Qc at 1 by ring.
apply Qcplus_le_compat. apply Qcle_refl.
apply -> Qcle_minus_iff. assumption.
Qed.

Lemma Qnnlt_le_weak {x y : Qnn}
  : x < y -> x <= y.
Proof. apply Qclt_le_weak. Qed.

Instance Qnnlt_le_subrelation : subrelation Qnnlt Qnnle.
Proof.
unfold subrelation, predicate_implication, pointwise_lifting,
  Basics.impl.
apply @Qnnlt_le_weak.
Qed.

Lemma Qnnmult_lt_compat_r {x y z : Qnn}
  : 0 < z -> x < y -> x * z < y * z.
Proof. apply Qcmult_lt_compat_r. Qed.

Lemma Qnnlt_not_le {x y : Qnn}
  : x < y -> ~ y <= x.
Proof. apply Qclt_not_le. Qed.

Lemma Qnnplus_le_compat {x x' y y' : Qnn}
  : x <= x' -> y <= y' -> x + y <= x' + y'.
Proof. apply Qcplus_le_compat. Qed.

Instance Qnnplus_le_compatI : Proper (Qnnle ==> Qnnle ==> Qnnle) Qnnplus.
Proof.
unfold Proper, respectful.
intros. apply Qnnplus_le_compat; assumption.
Qed.

Definition Qnnmin (x y : Qnn) : Qnn := match (x ?= y) with 
   | Lt => x
   | Eq => x
   | Gt => y
   end.

Lemma Qnnmin_l {x y} : (Qnnmin x y <= x)%Qnn.
Proof. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare; simpl. 
- reflexivity.
- reflexivity. 
- apply Qclt_le_weak. apply Qnngt_alt. assumption.
Qed.

Lemma Qnnmin_r {x y} : Qnnmin x y <= y.
Proof. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnneq_alt in compare. induction compare. reflexivity.
- apply Qclt_le_weak. apply Qnnlt_alt. assumption.
- reflexivity.
Qed.

Lemma Qnnmin_le_both {z x y} : 
  z <= x -> z <= y -> z <= Qnnmin x y.
Proof. intros. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare;
unfold Qnnle; simpl; assumption.
Qed.

Lemma Qnnmin_lt_both {z x y} : 
  z < x -> z < y -> z < Qnnmin x y.
Proof. intros. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare;
unfold Qnnle; simpl; assumption.
Qed.

Lemma Qnnminus_nonneg (x y : Qnn) : (0 <=  match (x ?= y)%Qnn with
   | Lt => 0%Qnn
   | Eq => 0%Qnn
   | Gt => (x - y)%Qc
   end)%Qc.
Proof.
destruct (x ?= y)%Qnn eqn:destr.
- apply nonneg.
- apply nonneg.
- apply -> Qcle_minus_iff.
  apply Qnnlt_le_weak. apply Qnngt_alt.
  assumption.
Qed.

Definition Qnnminus (x y : Qnn) : Qnn :=
  {| qnn := match (x ?= y)%Qnn with
   | Lt => 0%Qnn
   | Eq => 0%Qnn
   | Gt => (x - y)%Qc
   end
   ;  nonneg := Qnnminus_nonneg x y
  |}.

Infix "-" := Qnnminus : Qnn_scope.

Lemma Qnnminus_Qc {x y : Qnn} : y <= x ->
  qnn (x - y) = (qnn x - qnn y)%Qc.
Proof.
intros ylex. simpl.
destruct (x ?= y) eqn:destr; simpl.
- apply Qnneq_alt in destr. subst. ring.
- apply Qnnlt_alt in destr.
  apply Qnnlt_not_le in destr.
  specialize (destr ylex). contradiction.
- reflexivity.
Qed.

Definition Qnnminusp (x y : Qnn) (prf : y <= x) : Qnn.
Proof. refine (
  {| qnn := x - y |}
). abstract (apply -> Qcle_minus_iff; assumption).
Defined. 

Definition Qnnminusp_irrel {x y : Qnn} {p q : y <= x}
  : Qnnminusp x y p = Qnnminusp x y q.
Proof.
apply Qnneq_prop. unfold Qnneq. simpl. reflexivity.
Qed.

Lemma Qnnminus_equiv {x y : Qnn} {ylex : y <= x}
  : Qnnminusp x y ylex = Qnnminus x y.
Proof.
apply Qnneq_prop. unfold Qnneq. symmetry. apply Qnnminus_Qc.
assumption.
Qed.

Fixpoint Qnnpow (b : Qnn) (e : nat) := match e with
  | 0 => 1
  | S e' => b * Qnnpow b e'
  end.

Infix "^"  := Qnnpow : Qnn_scope.

Lemma Qnnpow_Qc : forall (b : Qnn) (e : nat),
  qnn (b ^ e) = ((qnn b) ^ e)%Qc.
Proof.
intros. induction e; simpl.
- reflexivity. 
- rewrite IHe. reflexivity.
Qed.

Lemma Qnnpow_le {x : Qnn} {n : nat} :
  x <= 1 -> x ^ n <= 1.
Proof.
intros. induction n; simpl. reflexivity.
replace 1 with (1 * 1) by ring.
apply Qnnmult_le_compat; assumption.
Qed.

Lemma Qnnminus_le {x y z : Qnn} : y <= x 
  -> (x - y <= z <-> x <= y + z).
Proof.
split; intros. 
- unfold Qnnle. apply Qcle_minus_iff. simpl.
  replace (y + z + - x)%Qc with (z - (x - y))%Qc by ring.
  apply -> Qcle_minus_iff. rewrite <- Qnnminus_Qc by assumption. 
  apply H0.
- unfold Qnnle. rewrite Qnnminus_Qc by assumption. 
  apply Qcle_minus_iff. simpl.
  replace (z + - (x - y))%Qc with (y + z - x)%Qc by ring.
  apply -> Qcle_minus_iff. apply H0. 
Qed.

Lemma Qnnminus_lt_l {x y z : Qnn} : (y <= x)
  -> (x - y < z <-> x < y + z).
Proof.
split; intros. 
- unfold Qnnle. apply Qclt_minus_iff. simpl.
  replace (y + z + - x)%Qc with (z - (x - y))%Qc by ring.
  apply -> Qclt_minus_iff. 
  rewrite <- Qnnminus_Qc by assumption.
  apply H0.
- apply Qclt_minus_iff. rewrite Qnnminus_Qc by assumption.
  replace (z + - (x - y))%Qc with (y + z - x)%Qc by ring.
  apply -> Qclt_minus_iff. apply H0. 
Qed.

Lemma Qnnminus_lt_r {x y z : Qnn} : y <= x
  -> (z < x - y <-> y + z < x).
Proof.
split; intros. 
- unfold Qnnlt. apply Qclt_minus_iff. simpl.
  replace (x + - (y + z))%Qc with ((x - y) - z)%Qc by ring.
  apply -> Qclt_minus_iff. 
  rewrite <- Qnnminus_Qc by assumption.
  apply H0.
- unfold Qnnlt. apply Qclt_minus_iff. 
  rewrite Qnnminus_Qc by assumption. 
  replace (x - y + - z)%Qc with (x - (y + z))%Qc by ring.
  apply -> Qclt_minus_iff. apply H0. 
Qed.


Lemma Qnnminus_plus {x y : Qnn}
  : x <= y -> (x + (y - x)) = y.
Proof.
  intros. apply Qnneq_prop. unfold Qnneq.
  replace (qnn (x + (y - x))) 
  with (qnn x + qnn (y - x)%Qnn)%Qc by reflexivity. 
  rewrite Qnnminus_Qc by assumption. ring.
Qed.

Lemma Qnnminus_mult_distr {c x y : Qnn}
  : (y <= x) -> c * (x - y) = c * x - c * y.
Proof.
intros. apply Qnneq_prop. unfold Qnneq. simpl.
destruct (x ?= y)%Qnn eqn:xy;
destruct (c * x ?= c * y)%Qnn eqn:cxcy;
try ring.
rewrite Qnneq_alt in xy. subst. rewrite Qnngt_alt in cxcy.
apply Qnnlt_not_le in cxcy. apply False_rect. apply cxcy.
reflexivity.
apply Qnnlt_alt in xy. apply Qnnlt_not_le in xy.
specialize (xy H). contradiction.
apply Qnneq_alt in cxcy.
destruct (Qnn_dec c 0). destruct s. apply Qnnlt_zero_prop in q.
contradiction.
rewrite Qnngt_alt in xy.
assert (y * c < x * c).
apply Qnnmult_lt_compat_r. assumption. 
unfold Qnngt in xy. assumption.
apply Qnnlt_not_le in H0. apply False_rect. apply H0.
replace (x * c) with (c * x) by ring.
replace (y * c) with (c * y) by ring.
rewrite cxcy. reflexivity.
subst. simpl. ring. apply Qnnlt_alt in cxcy. 
assert (x < y)%Qnn. replace x with (x * 1) by ring.
replace y with (y * 1)%Qnn by ring.
rewrite <- (Qnnmult_inv_r c).
repeat rewrite (SRmul_assoc Qnnsrt).
apply Qnnmult_lt_compat_r.
apply Qnnlt_alt in cxcy. 
apply Qnninv_zero2.
destruct (Qnn_dec c 0). destruct s.
apply Qnnlt_not_le in q. apply False_rect. apply q. apply nonneg.
assumption. subst. apply Qnnlt_not_le in cxcy.
apply False_rect. apply cxcy. ring_simplify. reflexivity.
rewrite (SRmul_comm Qnnsrt x). 
rewrite (SRmul_comm Qnnsrt y). 
apply Qnnlt_alt in cxcy. apply cxcy.
destruct (Qnn_dec c 0).
destruct s. apply Qnnlt_zero_prop in q. contradiction.
assumption. subst. apply Qnnlt_not_le in cxcy.
apply False_rect. apply cxcy. ring_simplify. reflexivity.
apply Qnnlt_not_le in H0. specialize (H0 H). contradiction.
Qed.

Lemma Qnnminus_plus2 {x y : Qnn}
  : ((x + y) - y = x)%Qnn .
Proof.
apply Qnneq_prop. unfold Qnneq.
rewrite Qnnminus_Qc. simpl. ring.
replace y with (0 + y)%Qnn at 1 by ring.
apply Qnnplus_le_compat. apply nonneg. reflexivity.
Qed.


Lemma Qnnminus_eq {x y : Qnn}
  : (y <= x)%Qnn -> forall z, ((x - y = z)%Qnn <-> (x = y + z)%Qnn).
Proof.
intros. split; intros.
- rewrite <- H0. rewrite Qnnminus_plus. reflexivity. assumption. 
- rewrite H0 in *. rewrite (SRadd_comm Qnnsrt). 
  apply Qnnminus_plus2.
Qed.

Lemma Qnnminus_plus_distr {x y a b : Qnn}
  : (a <= x -> b <= y -> 
    x - a + (y - b)
  = (x + y) - (a + b))%Qnn.
Proof.
intros.
symmetry. rewrite Qnnminus_eq.
replace (a + b + (x - a + (y - b)))%Qnn
with ((a + (x - a)) + (b + (y - b)))%Qnn by ring.
do 2 rewrite Qnnminus_plus by assumption. reflexivity. 
apply Qnnplus_le_compat; assumption.
Qed.

Lemma Qnnonehalf_split {x : Qnn}
  : (x = (x + x) * Qnnonehalf)%Qnn.
Proof. 
unfold Qnnonehalf. apply Qnneq_prop. unfold Qnnmult, Qnnplus.
simpl. unfold Qnneq. simpl. apply Qc_is_canon. reduceQ.
simpl. field.
Qed.

Lemma redistribute_onehalf : forall q x y,
 (   (q + (x + y)) * Qnnonehalf
  = (q * Qnnonehalf + x) * Qnnonehalf + (q * Qnnonehalf + y) * Qnnonehalf
  )%Qnn.
Proof.
intros. rewrite (@Qnnonehalf_split q) at 1. ring. 
Qed.

Fixpoint Qnnnat (n : nat) : Qnn := match n with 
  | 0 => 0%Qnn
  | S n' => (1 + Qnnnat n')%Qnn
  end.

Definition Qnnfrac (n : nat) := / (Qnnnat n).

Lemma Qnnnatfrac {n : nat} : (Qnnnat (S n) * Qnnfrac (S n) = 1)%Qnn.
Proof. unfold Qnnfrac. apply Qnnmult_inv_r. simpl.
replace 0%Qnn with (0 + 0)%Qnn by ring.
replace (1 + Qnnnat n)%Qnn with (Qnnnat n + 1)%Qnn by ring.
apply Qnnplus_le_lt_compat. apply nonneg.
apply Qnnlt_alt. reflexivity.
Qed.

Lemma Qnnnat_plus {x y : nat} : (Qnnnat (x + y) = Qnnnat x + Qnnnat y)%Qnn.
Proof.
induction x.
- simpl; ring.
- simpl. rewrite IHx. ring.
Qed.

Require Import clement.SmallPowers.
Local Close Scope Qc.
Local Close Scope Q.

Lemma smallPowers {p : Qnn} : p < 1
  -> forall (q : Qnn), (q > 0)
  -> exists (n : nat), (p ^ n < q).
Proof.
intros.
destruct (power_small p q (nonneg p) H H0).
exists x. unfold Qnnlt. rewrite Qnnpow_Qc. assumption.
Qed.

Lemma Qnnplus_open {q x y : Qnn} : q < x + y
  -> 0 < x -> 0 < y
  -> exists x' y', x' < x /\ y' < y /\ (q <= x' + y').
Proof.
intros. 
pose (((x + y) - q) * Qnnonehalf)%Qnn as eps.
pose (Qnnmin eps (Qnnmin x y)) as eps'.
exists (x - eps'). exists (y - eps').
assert (0 < eps)%Qnn. unfold eps.
replace 0%Qnn with (0 * Qnnonehalf)%Qnn by ring.
apply Qnnmult_lt_compat_r. rewrite <- Qnnlt_alt.
reflexivity. apply Qnnminus_lt_r. apply Qnnlt_le_weak.
assumption. ring_simplify. assumption.
assert (0 < eps')%Qnn.
apply Qnnmin_lt_both. assumption. apply Qnnmin_lt_both; assumption.
assert (eps' <= x)%Qnn. unfold eps'. rewrite Qnnmin_r. apply Qnnmin_l.
assert (eps' <= y)%Qnn. unfold eps'. rewrite Qnnmin_r. apply Qnnmin_r. 
split.
  simpl. apply Qnnminus_lt_l. assumption.
  replace x with (x + 0)%Qnn at 1 by ring.
  replace (eps' + x)%Qnn with (x + eps')%Qnn by ring.
  apply Qnnplus_le_lt_compat. reflexivity.
  assumption.
split. 
  simpl. apply Qnnminus_lt_l. assumption.
  replace y with (y + 0)%Qnn at 1 by ring.
  replace (eps' + y)%Qnn with (y + eps')%Qnn by ring.
  apply Qnnplus_le_lt_compat. reflexivity.
  assumption.
rewrite (@Qnnonehalf_split q).
replace ((q + q) * Qnnonehalf)%Qnn
  with (q * Qnnonehalf + q * Qnnonehalf)%Qnn by ring.
apply Qnnplus_le_compat.
admit. admit.
Admitted.

Lemma Qnnmult_open {q x y : Qnn} : q < x * y
  -> exists x' y', x' < x /\ y' < y /\ (q <= x' * y').
Proof.
Admitted.

Module Instances.

Require Import Frame.

Definition opsU : MeetLat.Ops Qnn := 
  {| MeetLat.le := Qnnle ; MeetLat.eq := Logic.eq; MeetLat.min := Qnnmin |}.

Definition ops : MeetLat.Ops Qnn := 
  {| MeetLat.le := Qnnge ; MeetLat.eq := Logic.eq; MeetLat.min := Qnnmax |}.

Instance UML : MeetLat.t Qnn opsU.
Proof.
constructor. constructor. constructor. 
- intros; reflexivity.
- intros. eapply Qnnle_trans; eassumption.
- solve_proper.
- intros; apply Qnnle_antisym; assumption.
- solve_proper.
- intros. constructor.
  + apply Qnnmin_l.
  + apply Qnnmin_r.
  + intros. apply Qnnmin_le_both; assumption.
Qed.

Instance ML : MeetLat.t Qnn ops.
Proof.
constructor. constructor. constructor. 
- intros; simpl; unfold Qnnge; reflexivity.
- intros. simpl in *. eapply Qnnle_trans; eassumption.
- solve_proper.
- intros; apply Qnnle_antisym; assumption.
- solve_proper.
- simpl in *. intros. constructor.
  + apply Qnnmax_l.
  + apply Qnnmax_r.
  + intros. apply Qnnmax_induction; auto.
Qed.

(** In fact, the [Qnnmin] operation is a idempotent,
    commutative semigroup. I think I have a more generic proof of this
    somewhere in Frame.v?
*)
Theorem lowerCommSG : CommIdemSG.t Qnn eq Qnnmin.
Proof.
pose opsU.
constructor; intros.
- apply eq_equivalence.
- solve_proper.
- replace (@eq Qnn _ _) with (@MeetLat.eq Qnn _ (MeetLat.min a a) a) by reflexivity. 
 apply MeetLat.min_idempotent.
- apply Qnnle_antisym; apply Qnnmin_le_both;
    (apply Qnnmin_r || apply Qnnmin_l).
- apply Qnnle_antisym. apply Qnnmin_le_both.
  apply Qnnmin_le_both. apply Qnnmin_l. rewrite Qnnmin_r.
  apply Qnnmin_l. rewrite Qnnmin_r. apply Qnnmin_r.
  apply Qnnmin_le_both. rewrite Qnnmin_l. apply Qnnmin_l.
  apply Qnnmin_le_both. rewrite Qnnmin_l. apply Qnnmin_r.
  apply Qnnmin_r.
Qed.
End Instances.