Require Import QArith Qcanon.

Require Import FunctionalExtensionality.

(** Non-negative rational numbers *)

Record Qnn :=
  { qnn :> Qc
  ; nonneg : qnn >= 0
  }.

Local Open Scope Z.

Theorem Zle_irrel {x y : Z} (prf1 prf2 : x <= y) :
  prf1 = prf2. 
Proof. unfold Z.le in *.
apply functional_extensionality.
intros z. contradiction.
Qed.

Local Close Scope Z.
Local Close Scope Qc.

Definition Qle_irrel {x y : Q} (prf1 prf2 : x <= y)
  : prf1 = prf2 := Zle_irrel prf1 prf2.

Local Open Scope Qc.
Definition Qcle_irrel {x y : Qc} (prf1 prf2 : x <= y)
  : prf1 = prf2 := Qle_irrel prf1 prf2.

Definition Qnnle (x y : Qnn) : Prop := x <= y.
Definition Qnnge (x y : Qnn) : Prop := x >= y.
Definition Qnnlt (x y : Qnn) : Prop := x < y.
Definition Qnngt (x y : Qnn) : Prop := x > y.

Definition Qnneq (x y : Qnn) : Prop := qnn x = qnn y.

Definition Qnnplus (x y : Qnn) : Qnn.
Proof.
refine ({| qnn := x + y |}).
replace 0 with (0 + 0) by field.
apply Qcplus_le_compat; destruct x, y; assumption.
Defined.

Definition Qnnmult (x y : Qnn) : Qnn.
Proof.
refine ({| qnn := x * y |}).
replace 0 with (0 * y) by field.
apply Qcmult_le_compat_r; apply nonneg.
Defined.

Definition Qnnzero : Qnn := Build_Qnn 0%Qc (Qcle_refl 0%Qc).

Ltac makeQnn q := apply (Build_Qnn q); unfold Qle; simpl;
  unfold Z.le; simpl; congruence.

Definition Qnnone : Qnn.
Proof. makeQnn 1.
Defined.

Definition Qnnonehalf : Qnn.
Proof. makeQnn (Qcmake (1 # 2) eq_refl).
Defined.

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

Lemma Qnnle_antisym {x y : Qnn}
  : x <= y -> y <= x -> x = y.
Proof. intros. apply Qnneq_prop. eapply Qcle_antisym; eassumption. Qed.

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
split; intros; apply Qcgt_alt; assumption.
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
eapply Qnnle_trans. eassumption.
replace (x' * y) with (y * x') by ring.
replace (x' * y') with (y' * x') by ring.
apply Qcmult_le_compat_r. assumption. apply nonneg.
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
  apply Qnnle_refl. assumption.
- pattern (x * y), (x * z), (Qnnmax (x * y) (x * z)). 
  apply Qnnmax_induction; intros.
  apply Qnnle_antisym. assumption. apply Qnnmult_le_compat.
  apply Qnnle_refl. assumption. reflexivity.
Qed.

Lemma Qnnmax_l {x y} : x <= Qnnmax x y.
Proof. unfold Qnnmax; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnnle_refl.
- apply Qclt_le_weak. apply Qnnlt_alt. assumption.
- apply Qnnle_refl.
Qed.

Lemma Qnnmax_r {x y} : y <= Qnnmax x y.
Proof. unfold Qnnmax; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnneq_alt in compare. induction compare. apply Qnnle_refl.
- apply Qnnle_refl. 
- apply Qclt_le_weak. apply Qnngt_alt. assumption.
Qed.

Definition Qnninv (x : Qnn) : Qnn.
Proof. refine (
  {| qnn := (/ x)%Qc |}
).
destruct (x ?= 0) eqn:comp. apply Qnneq_alt in comp.
subst. simpl. apply Qle_refl.
apply Qnnlt_alt in comp. apply Qnnlt_zero_prop in comp.
contradiction.
setoid_replace (this (/ x)%Qc) with (/ x)%Q.
apply Qinv_le_0_compat. apply nonneg.
simpl. apply Qred_correct.
Defined. 

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


Lemma Qnninv_zero1 {x : Qnn} : Qnninv x = 0 -> x = 0.
Proof. intros. destruct (x ?= 0) eqn:comp.
apply Qnneq_alt in comp. assumption.
apply Qnnle_antisym. apply Qclt_le_weak. assumption. apply nonneg.
apply Qnngt_alt in comp. replace x with (x * 1) by ring.
replace 1 with (Qnninv x * x). rewrite H. ring.
rewrite (SRmul_comm Qnnsrt).
apply Qnnmult_inv_r. assumption.
Qed. 

Lemma Qnninv_zero2 {x : Qnn} : 0 < x -> 0 < Qnninv x.
Proof. intros. apply Qnnzero_prop2. unfold not. intros contra.
apply Qnninv_zero1 in contra. subst. apply Qnnzero_prop2 in H. 
unfold not in H. apply H. reflexivity. 
Qed.

Definition Qnndiv (x y : Qnn) : Qnn := x * Qnninv y.

Lemma Qnndiv_lt (num denom : Qnn) : num < denom -> Qnndiv num denom < 1.
Proof. intros. unfold Qnndiv.
destruct (num ?= 0) eqn:comp. apply Qnneq_alt in comp.
subst. replace (0 * Qnninv denom) with 0 by ring. unfold Qnnlt. 
apply Qclt_alt. reflexivity.

apply Qnnlt_alt in comp. apply Qnnlt_zero_prop in comp. contradiction.

apply Qnngt_alt in comp. replace 1 with (denom * Qnninv denom).
apply Qcmult_lt_compat_r.
apply Qnninv_zero2. eapply Qnnle_lt_trans. apply (nonneg num). assumption.
assumption. 
apply Qnnmult_inv_r. eapply Qnnle_lt_trans. apply (nonneg num). assumption.
Qed. 

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

Ltac reduceQ := repeat (unfold Qcplus, Qcdiv, Qcinv, Qcmult; 
match goal with
| [ |- context[this (!! ?x)%Qc] ] => 
     setoid_replace (this (!! x)%Qc) with x by (apply Qred_correct)
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

Definition Qbetween (x z : Q) : (x < z)%Q
  -> { y | (x < y /\ y < z)%Q }.
Proof. intros. eexists. apply Qaverage. assumption.
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

Lemma Qnnmult_lt_compat_r {x y z : Qnn}
  : 0 < z -> x < y -> x * z < y * z.
Proof. apply Qcmult_lt_compat_r. Qed.

Lemma Qnnlt_not_le {x y : Qnn}
  : x < y -> ~ y <= x.
Proof. apply Qclt_not_le. Qed.

Lemma Qnnplus_le_compat {x x' y y' : Qnn}
  : x <= x' -> y <= y' -> x + y <= x' + y'.
Proof. apply Qcplus_le_compat. Qed.

Definition Qnnmin (x y : Qnn) : Qnn := match (x ?= y) with 
   | Lt => x
   | Eq => x
   | Gt => y
   end.

Lemma Qnnmin_l {x y} : (Qnnmin x y <= x)%Qnn.
Proof. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnnle_refl.
- apply Qnnle_refl. 
- apply Qclt_le_weak. apply Qnngt_alt. assumption.
Qed.

Lemma Qnnmin_r {x y} : Qnnmin x y <= y.
Proof. unfold Qnnmin; simpl. destruct (x ?= y) eqn:compare; simpl. 
- apply Qnneq_alt in compare. induction compare. apply Qnnle_refl.
- apply Qclt_le_weak. apply Qnnlt_alt. assumption.
- apply Qnnle_refl.
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

Definition Qnnminus (x y : Qnn) (prf : y <= x) : Qnn.
Proof. refine (
  {| qnn := x - y |}
). apply -> Qcle_minus_iff. assumption.
Defined. 

Fixpoint Qnnpow (b : Qnn) (e : nat) := match e with
  | 0 => 1
  | S e' => b * Qnnpow b e'
  end.

Lemma Qnnpow_le {x : Qnn} {n : nat} :
  x <= 1 -> Qnnpow x n <= 1.
Proof.
intros. induction n; simpl. apply Qnnle_refl.
replace 1 with (1 * 1) by ring.
apply Qnnmult_le_compat; assumption.
Qed.

Lemma Qnnminus_le {x y z : Qnn} (ylex : (y <= x)%Qnn)
  : (Qnnminus x y ylex <= z <-> x <= y + z)%Qnn.
Proof.
split; intros. 
- unfold Qnnle. apply Qcle_minus_iff. simpl.
  replace (y + z + - x)%Qc with (z - (x - y))%Qc by ring.
  apply -> Qcle_minus_iff. apply H.
- unfold Qnnle. apply Qcle_minus_iff. simpl.
  replace (z + - (x - y))%Qc with (y + z - x)%Qc by ring.
  apply -> Qcle_minus_iff. apply H. 
Qed.

Lemma Qnnminus_lt_l {x y z : Qnn} (ylex : (y <= x)%Qnn)
  : (Qnnminus x y ylex < z <-> x < y + z)%Qnn.
Proof.
split; intros. 
- unfold Qnnle. apply Qclt_minus_iff. simpl.
  replace (y + z + - x)%Qc with (z - (x - y))%Qc by ring.
  apply -> Qclt_minus_iff. apply H.
- unfold Qnnle. apply Qclt_minus_iff. simpl.
  replace (z + - (x - y))%Qc with (y + z - x)%Qc by ring.
  apply -> Qclt_minus_iff. apply H. 
Qed.

Lemma Qnnminus_lt_r {x y z : Qnn} (ylex : (y <= x)%Qnn)
  : (z < Qnnminus x y ylex <-> y + z < x)%Qnn.
Proof.
split; intros. 
- unfold Qnnlt. apply Qclt_minus_iff. simpl.
  replace (x + - (y + z))%Qc with ((x - y) - z)%Qc by ring.
  apply -> Qclt_minus_iff. apply H.
- unfold Qnnlt. apply Qclt_minus_iff. simpl.
  replace (x - y + - z)%Qc with (x - (y + z))%Qc by ring.
  apply -> Qclt_minus_iff. apply H. 
Qed.