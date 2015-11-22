Require Import QArith Qcanon.

Require Import FunctionalExtensionality.

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
induction H. replace nonneg0 with nonneg1. reflexivity.
apply Qcle_irrel.
Qed.

Theorem Qnn_zero_prop {x : Qnn} :
  x <= 0 -> x = Qnnzero.
Proof.
intros. apply Qnneq_prop. unfold Qnneq.
unfold Qnnzero. simpl. apply Qcle_antisym.
assumption. apply nonneg.
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

Theorem Qnnsrt : semi_ring_theory Qnnzero Qnnone
  Qnnplus Qnnmult eq.
Proof.
constructor; intros;
  match goal with
  | [  |- _ = _ ] => apply Qnneq_prop; unfold Qnneq
  end;
  try solve[simpl; field].
Qed.

Add Ring Qnn_Ring : Qnnsrt.

Local Close Scope Q.
Local Close Scope Qc.

Delimit Scope Qnn_scope with Qnn.

Local Open Scope Qnn.

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


Definition Qnnmax (x y : Qnn) : Qnn := match (x ?= y)%Qc with 
   | Lt => y
   | Eq => x
   | Gt => x
   end.

Lemma Qnnmax_induction {x y} (P : Qnn -> Qnn -> Qnn -> Prop) :
  (y <= x -> P x y x) -> (x <= y -> P x y y) -> P x y (Qnnmax x y).
Proof.
intros. unfold Qnnmax. destruct (x ?= y)%Qc eqn:ceqn. 
  apply H. unfold Qnnle. apply Qceq_alt in ceqn. rewrite ceqn. apply Qcle_refl.
  apply H0. unfold Qnnle. apply Qclt_le_weak. apply Qclt_alt. assumption.
  apply H. apply Qcgt_alt in ceqn. apply Qclt_le_weak. assumption.
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
Proof. unfold Qnnmax; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl. 
- apply Qcle_refl.
- apply Qclt_le_weak. apply Qclt_alt. assumption.
- apply Qcle_refl.
Qed.

Lemma Qnnmax_r {x y} : y <= Qnnmax x y.
Proof. unfold Qnnmax; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl. 
- apply Qceq_alt in compare. induction compare. apply Qcle_refl.
- apply Qcle_refl. 
- apply Qclt_le_weak. apply Qcgt_alt. assumption.
Qed.

Definition Qnninv (x : Qnn) : Qnn.
Proof. refine (
  {| qnn := (/ x)%Qc |}
).
destruct (x ?= 0)%Qc eqn:comp. apply Qceq_alt in comp.
assert (x = 0%Qnn). apply Qnneq_prop. assumption.
subst. simpl. apply Qle_refl.
apply Qclt_alt in comp. apply Qnnlt_zero_prop in comp.
contradiction. auto. 
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



(* Nonnegative lower reals *)
Record LPReal :=
  { lbound :> Qnn -> Prop
  ; dclosed : forall q, lbound q -> forall q', q' <= q -> lbound q'
  ; uopen   : forall q, lbound q -> exists q', q < q' /\ lbound q'
  }.

Definition LPRle (r s : LPReal) : Prop :=
  forall q, r q -> s q.

Definition LPRge (r s : LPReal) : Prop :=
  forall q, s q -> r q.

Definition LPRle_refl (r : LPReal) : LPRle r r :=
  fun _ p => p.

Definition LPRle_trans {r s t : LPReal} 
  (rs : LPRle r s) (st : LPRle s t) : LPRle r t :=
  fun q prf => (st q (rs q prf)).

Definition LPReq (r s : LPReal) : Prop :=
  LPRle r s /\ LPRle s r.

Lemma LPReq_refl (x : LPReal) : LPReq x x.
Proof. split; apply LPRle_refl. Qed.

Lemma LPReq_trans (x y z : LPReal) 
  : LPReq x y -> LPReq y z -> LPReq x z.
Proof. intros. destruct H; destruct H0; split;
  eapply LPRle_trans; eassumption.
Qed.

Lemma LPReq_compat_backwards (x y : LPReal) : x = y -> LPReq x y.
Proof. intros H; induction H; apply LPReq_refl. Qed.

Definition LPRQnn (q : Qnn) : LPReal.
Proof.
refine (
  {| lbound := fun q' => (q' < q)%Qnn |}
).
- intros. subst. eapply Qnnle_lt_trans; eassumption.
- intros. exists (Qnndiv (q0 + q) (1 + 1)). admit.
Defined.

Inductive LPRplusT {x y : LPReal} : Qnn -> Prop :=
  | LPRplusL : forall q, x q -> LPRplusT q
  | LPRplusR : forall q, y q -> LPRplusT q
  | LPRplusB : forall q q' sum , x q -> y q' -> sum <= q + q' -> LPRplusT sum.

Arguments LPRplusT : clear implicits.

Definition LPRplus (x y : LPReal) : LPReal.
Proof.
refine (
  {| lbound := LPRplusT x y |}
).
- intros.
  inversion H; subst; 
  [apply LPRplusL | apply LPRplusR | eapply LPRplusB].
  eapply dclosed; eassumption.
  eapply dclosed; eassumption.
  eassumption. eassumption. 
  eapply Qnnle_trans; eassumption.
- intros. destruct H.
  + pose proof (uopen _ _ H). destruct H0.
    exists x0. intuition. apply LPRplusL. assumption.
  + pose proof (uopen _ _ H). destruct H0.
    exists x0. intuition. apply LPRplusR. assumption.
  + pose proof (uopen _ _ H). destruct H2. 
    exists (x0 + q'). intuition. eapply Qnnle_lt_trans. eassumption.
    apply Qclt_minus_iff. simpl.
    replace (x0 + q' + - (q + q'))%Qc with (x0 + - q)%Qc by ring.
    apply -> Qclt_minus_iff. assumption.
    eapply LPRplusB. eassumption. eassumption. apply Qnnle_refl.
Defined.

Definition LPRmult (x y : LPReal) : LPReal.
Proof.
refine (
  {| lbound := fun q => exists a b,
     lbound x a /\ lbound y b /\ (q <= a * b)%Qnn |}
).
- intros.
  destruct H as [a [b [xa [yb sum]]]].
  exists a. exists b. intuition. eapply Qnnle_trans; eassumption.
- intros. destruct H as [a [b [pa [pb prod]]]].
  pose proof (uopen _ _ pa). destruct H as [a' [pa' xa']].
  pose proof (uopen _ _ pb). destruct H as [b' [pb' yb']].
  exists (a' * b'). split. eapply Qnnle_lt_trans. eassumption.
  apply Qnnle_lt_trans with (a * b').
  apply Qnnmult_le_compat. apply Qnnle_refl. apply Qclt_le_weak.
  assumption. apply Qcmult_lt_compat_r.
  eapply Qcle_lt_trans. apply (nonneg b). assumption. assumption.
  exists a'. exists b'. intuition. apply Qnnle_refl.
Defined.


Lemma LPReq_prop : forall r s, LPReq r s ->
  forall q, lbound r q <-> lbound s q.
Proof.
intros. destruct H. split. apply H. apply H0.
Qed.

Lemma LPReq_compat_OK 
  (propext : forall (x y : Prop), (x <-> y) -> x = y)
  (proof_irrel : forall (P : Prop) (x y : P), x = y)
  : forall r s, LPReq r s -> r = s. 
Proof.
intros. pose proof H as eq. destruct H.
unfold LPRle in *.
assert (lbound r = lbound s).
apply functional_extensionality.
intros q. apply propext. apply LPReq_prop.
assumption.
destruct r, s.
simpl in *. induction H1.
pose proof (proof_irrel _ dclosed0 dclosed1).
induction H1.
pose proof (proof_irrel _ uopen0 uopen1).
induction H1.
reflexivity.
Qed.

Axiom LPReq_compat : forall r s, LPReq r s -> r = s.

Ltac LPRsrttac := 
repeat match goal with
| [ |- _ /\ _ ] => split
| [ |- forall _, _] => intros
| [ H : lbound (LPRQnn _) _ |- _ ] => simpl in H
| [ H : lbound (LPRplus _ _) _ |- _ ] => destruct H
| [ H : lbound (LPRmult _ _) _ |- _ ] => destruct H
| [ H : exists x, _ |- _ ] => destruct H
| [ H : _ /\ _ |- _ ] => destruct H
| [ H : _ < 0 |- _ ] => apply Qclt_not_le in H; unfold not in H;
  apply False_rect; apply H; apply nonneg
| [ |- lbound (LPRplus (LPRQnn 0) _) _ ] => apply LPRplusR
| [ |- lbound (LPRplus _ (LPRQnn 0)) _ ] => apply LPRplusL
| [ Hm : lbound ?m _, Hn : lbound ?n _ |- lbound (LPRplus ?m ?n) _ ]
   => eapply LPRplusB; [ eassumption | eassumption | ]
| [ Hm : lbound ?m ?q |- lbound (LPRplus ?m _) ?q ]
   => apply LPRplusL
| [ Hn : lbound ?n ?q |- lbound (LPRplus _ ?n) ?q ]
   => apply LPRplusR
| [ |- _ ] => assumption
end.



Theorem LPRsrt : semi_ring_theory (LPRQnn 0) (LPRQnn 1)
  LPRplus LPRmult eq.
Proof.
constructor; intros; apply LPReq_compat; unfold LPReq, LPRle;
LPRsrttac.
- replace (q' + q) with (q + q') by ring. assumption.
- replace (q' + q) with (q + q') by ring. assumption.
- apply LPRplusL. LPRsrttac. 
- apply LPRplusL. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- apply LPRplusL. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- eapply LPRplusB with (q + q0) (q'). eapply LPRplusB with q q0.
  eassumption. eassumption. apply Qnnle_refl. assumption.
  eapply Qnnle_trans. eassumption. rewrite <- (SRadd_assoc Qnnsrt). 
  apply Qcplus_le_compat. apply Qcle_refl. assumption.
- apply LPRplusR. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- eapply LPRplusR. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- apply LPRplusR. LPRsrttac.
- eapply LPRplusB with q (q'0 + q'). assumption. 
  eapply LPRplusB with q'0 q'; try assumption.
  apply Qnnle_refl. eapply Qnnle_trans. eassumption.
  rewrite (SRadd_assoc Qnnsrt). 
  apply Qcplus_le_compat. assumption. apply Qcle_refl. 
- eapply dclosed. eassumption. eapply Qnnle_trans. eassumption.
  replace x0 with (1 * x0) at 2 by ring.
  apply Qnnmult_le_compat. apply Qclt_le_weak. assumption.
  apply Qnnle_refl.
- simpl. pose proof (uopen _ _ H). destruct H0 as [q' [qq' nq']].
  exists (Qnndiv q q'). exists q'. split. apply Qnndiv_lt. assumption. intuition.
  unfold Qnndiv. rewrite <- (SRmul_assoc Qnnsrt).
  replace (Qnninv q' * q') with 1. replace (q * 1) with q by ring.
  apply Qnnle_refl. symmetry. rewrite (SRmul_comm Qnnsrt). 
  apply Qnnmult_inv_r. eapply Qnnle_lt_trans. apply (nonneg q).
  assumption.
- simpl. exists x0. exists x. intuition.
  replace (x0 * x) with (x * x0) by ring.
  assumption.
- simpl. exists x0. exists x. intuition.
  replace (x0 * x) with (x * x0) by ring.
  assumption.
- simpl. exists (x * x1). exists x2. split.
  exists x. exists x1. intuition. apply Qnnle_refl.
  intuition. eapply Qnnle_trans. eassumption.
  rewrite <- (SRmul_assoc Qnnsrt).
  apply Qnnmult_le_compat. apply Qnnle_refl. assumption. 
- simpl. exists x1. exists (x0 * x2). intuition.
  exists x2. exists x0. intuition. rewrite (SRmul_comm Qnnsrt).
  apply Qnnle_refl. eapply Qnnle_trans. eassumption.
  replace (x1 * (x0 * x2)) with ((x1 * x2) * x0) by ring.
  apply Qnnmult_le_compat. assumption. apply Qnnle_refl.
- apply LPRplusL. simpl. exists q0. exists x0. auto.
- apply LPRplusR. simpl. exists q0. exists x0. auto.
- eapply LPRplusB. exists q0. exists x0. intuition. apply Qnnle_refl.
  exists q'. exists x0. intuition. apply Qnnle_refl. eapply Qnnle_trans.
  eassumption. rewrite <- (SRdistr_l Qnnsrt).
  apply Qnnmult_le_compat. assumption. apply Qnnle_refl.
- exists x. exists x0. intuition. apply LPRplusL. assumption.
- exists x. exists x0. intuition. apply LPRplusR. assumption.
- exists (x0 + x). exists (Qnnmax x1 x2). intuition. eapply LPRplusB; try eassumption.
  apply Qnnle_refl. 
  pattern x1, x2, (Qnnmax x1 x2). apply Qnnmax_induction; intros; assumption.
  eapply Qnnle_trans. eassumption.
  rewrite (SRdistr_l Qnnsrt). apply Qcplus_le_compat.
  pattern x1, x2, (Qnnmax x1 x2). apply Qnnmax_induction; intros.
  eapply Qnnle_trans. eassumption. apply Qnnmult_le_compat.
  apply Qnnle_refl. assumption. assumption.
  pattern x1, x2, (Qnnmax x1 x2). apply Qnnmax_induction; intros. assumption.
  eapply Qnnle_trans. eassumption. apply Qnnmult_le_compat.
  apply Qnnle_refl. assumption.
Qed.

Add Ring LPR_Ring : LPRsrt.

Infix "<=" := LPRle : LPR_scope.
Infix ">=" := LPRge : LPR_scope.
Infix "+" := LPRplus : LPR_scope.
Infix "*" := LPRmult : LPR_scope.

Notation "'0'" := (LPRQnn 0) : LPR_scope.
Notation "'1'" := (LPRQnn 1) : LPR_scope.

Delimit Scope LPR_scope with LPR.

Local Open Scope LPR.

Theorem LPRplus_le_compat {x y z t : LPReal}
  : (x <= y) -> (z <= t) -> (x + z <= y + t).
Proof. intros. unfold LPRle in *. intros.
simpl in *. destruct H1;
  [apply LPRplusL | apply LPRplusR | eapply LPRplusB ]; try intuition.
apply H. eassumption. apply H0. eassumption. assumption.
Qed.

Theorem LPRmult_le_compat {x x' y y' : LPReal}
  : x <= x' -> y <= y' -> x * y <= x' * y'.
Proof.
intros. unfold LPRle in *. intros.
simpl in *. destruct H1 as [a [b [H1 [H2 H3]]]].
do 2 eexists. split. apply H. eassumption. split.
apply H0. eassumption. assumption.
Qed.

Theorem LPRzero_min (r : LPReal) : 0 <= r.
Proof.
unfold LPRle. intros q Hq. simpl in *.
apply False_rect. eapply Qnnlt_zero_prop.
eassumption.
Qed.

Definition LPRsup {A : Type} (f : A -> LPReal)
  : LPReal.
Proof.
refine (
  {| lbound := fun q => exists (idx : A), f idx q |}
).
- intros. destruct H. exists x. apply dclosed with q. assumption. assumption.
- intros. destruct H. pose proof (uopen _ _ H).
  destruct H0 as [q' [qq' fq']]. 
  exists q'. split. assumption. exists x. assumption.
Defined.

Definition LPRinfinity : LPReal.
Proof. refine (
  {| lbound := fun q => True |}
); trivial.
intros. exists (1 + q)%Qnn. intuition.
apply Qclt_minus_iff.
simpl.
replace (1 + q + - q)%Qc with 1%Qc by ring.
apply Qclt_alt. reflexivity.
Defined.

Theorem LPRinfinity_max (r : LPReal) : r <= LPRinfinity.
Proof.
unfold LPRle. intros. simpl. constructor.
Qed.

Lemma LPRsup_ge {A : Type} {f : A -> LPReal} {a : A} 
  : f a <= LPRsup f.
Proof. unfold LPRle. simpl. intros. eexists. eassumption.
Qed.

Lemma LPRsup_le {A : Type} {f : A -> LPReal} {x : LPReal} 
  : (forall (a : A), (f a <= x)) -> LPRsup f <= x.
Proof. intros. unfold LPRle in *. simpl. intros. destruct H0.
subst. apply H with x0.
assumption.
Qed.

Lemma LPRsup_ge2 {A : Type} {f : A -> LPReal} {x : LPReal} 
  : (exists a, x <= f a) -> x <= LPRsup f.
Proof. intros. destruct H. eapply LPRle_trans. eassumption. apply LPRsup_ge.
Qed.

Lemma LPRsup_prop {A : Type} {f : A -> LPReal} {x : LPReal}
  : (forall (a : A), (f a <= x))
  -> (exists (a : A), x <= f a)
  -> LPRsup f = x.
Proof. intros. apply LPReq_compat. split. apply LPRsup_le.
assumption. eapply LPRsup_ge2. eassumption.
Qed.

Lemma LPRsup_monotonic {A : Type} (f g : A -> LPReal)
  : (forall (a : A), f a <= g a) -> LPRsup f <= LPRsup g.
Proof.
intros mono. unfold LPRle in *.
intros. simpl in *.
destruct H. exists x. apply mono. assumption.
Qed.

Lemma LPRsup_eq_pointwise {A : Type} (f g : A -> LPReal)
  : (forall (a : A), f a = g a) -> LPRsup f = LPRsup g.
Proof.
intros mono.
apply LPReq_compat. split; apply LPRsup_monotonic;
intros; rewrite mono; apply LPRle_refl.
Qed.

Lemma LPRsup_sum {A : Type} (f g : A -> LPReal)
  : LPRsup (fun x => f x + g x) <= LPRsup f + LPRsup g.
Proof. apply LPRsup_le. intros a.
apply LPRplus_le_compat; apply LPRsup_ge.
Qed.

Lemma LPRsup_sum_lattice {A : Type} (f g : A -> LPReal)
  (le : A -> A -> Prop)
  (max : A -> A -> A)
  (maxL  : forall (a b : A), le a (max a b))
  (maxR  : forall (a b : A), le b (max a b))
  (monof : forall n m, le n m -> f n <= f m)
  (monog : forall n m, le n m -> g n <= g m)
  : LPRsup (fun x => f x + g x) = LPRsup f + LPRsup g.
Proof.
apply LPReq_compat. split; [apply LPRsup_sum | ].
unfold LPRle. intros. simpl in *.
destruct H; simpl in *.
- destruct H. exists x. apply LPRplusL. assumption.
- destruct H. exists x. apply LPRplusR. assumption.
- destruct H. destruct H0. exists (max x x0). eapply LPRplusB.
  eapply monof. apply maxL. eassumption.
  eapply monog. apply maxR. eassumption. assumption.
Qed.

Lemma LPRsup_nat_ord (f g : nat -> LPReal)
  : (forall n m, (n <= m)%nat -> f n <= f m)
  -> (forall n m, (n <= m)%nat -> g n <= g m)
  -> LPRsup (fun x => f x + g x) = LPRsup f + LPRsup g.
Proof. intros. eapply LPRsup_sum_lattice; try eassumption.
apply Max.le_max_l.  apply Max.le_max_r.
Qed.

Definition LPRmax (x y : LPReal) : LPReal.
Proof. refine (
  {| lbound := fun q => x q \/ y q |}
).
- intros. destruct H; [left | right]; eapply dclosed; eassumption.
- intros. destruct H; 
  pose proof (uopen _ _ H) as H'; 
  destruct H' as [q' [qq' pq']]; exists q'; intuition.
Defined.

Lemma LPRmax_le_and {x y z : LPReal} 
  : x <= y -> y <= z -> LPRmax x y <= z.
Proof. intros.
unfold LPRle; simpl in *; intros; intuition.
Qed.

Lemma LPRmax_le_or {x y z : LPReal} 
  : z <= x \/ z <= y -> z <= LPRmax x y.
Proof. intros.
unfold LPRle; simpl in *; intros; intuition.
Qed.


Definition Qnnmin (x y : Qnn) : Qnn.
Proof.
refine (
  {| qnn := match (x ?= y)%Qc with 
   | Lt => x
   | Eq => x
   | Gt => y
   end |}
).
destruct (x ?= y)%Qc; apply nonneg.
Defined.

Lemma Qnnmin_l {x y} : (Qnnmin x y <= x)%Qnn.
Proof. unfold Qnnmin; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl. 
- apply Qcle_refl.
- apply Qcle_refl. 
- apply Qclt_le_weak. apply Qcgt_alt. assumption.
Qed.

Lemma Qnnmin_r {x y} : (Qnnmin x y <= y)%Qnn.
Proof. unfold Qnnmin; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl. 
- apply Qceq_alt in compare. induction compare. apply Qcle_refl.
- apply Qclt_le_weak. apply Qclt_alt. assumption.
- apply Qcle_refl.
Qed.

Lemma Qnnmin_le_both {z x y} : 
  (z <= x -> z <= y -> z <= Qnnmin x y)%Qnn.
Proof. intros. unfold Qnnmin; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl; assumption.
Qed.

Lemma Qnnmin_lt_both {z x y} : 
  (z < x -> z < y -> z < Qnnmin x y)%Qnn.
Proof. intros. unfold Qnnmin; simpl. destruct (x ?= y)%Qc eqn:compare;
unfold Qnnle; simpl; assumption.
Qed.

Definition LPRmin (x y : LPReal) : LPReal.
Proof. refine (
  {| lbound := fun q => x q /\ y q |}
).
- intros. destruct H; split; eapply dclosed; eassumption.
- intros. destruct H. 
  destruct (uopen _ _ H) as [q'x [qq'x pq'x]].
  destruct (uopen _ _ H0) as [q'y [qq'y pq'y]].
  exists (Qnnmin q'x q'y). split. eapply Qnnmin_lt_both; assumption.
  split; eapply dclosed; try eassumption. apply Qnnmin_l.
  apply Qnnmin_r.
Defined.

Theorem LPRle_antisym {x y : LPReal}
  : x <= y -> y <= x -> x = y.
Proof.
intros. apply LPReq_compat. split; assumption.
Qed.

Definition K {A} (x : A) {B} (y : B) := x.

Record Valuation {A : Type} :=
  { val :> (A -> Prop) -> LPReal
  ; strict : val (K False) = 0
  ; monotonic : forall (U V : A -> Prop), (forall z, U z -> V z)
              -> val U <= val V
  ; modular : forall {U V},
     val U + val V = val (fun z => U z /\ V z) + val (fun z => U z \/ V z)
  }.

Arguments Valuation : clear implicits.

Definition pointwise {A B : Type} (cmp : B -> B -> Prop)
  (f g : A -> B) : Prop := forall (a : A), cmp (f a) (g a).

Inductive Simple {A : Type} :=
  | SStep : LPReal -> (A -> Prop) -> Simple
  | SMax : Simple -> Simple -> Simple.

Arguments Simple : clear implicits.

Fixpoint SimpleIntegral {A : Type} (mu : (A -> Prop) -> LPReal) 
  (s : Simple A) : LPReal := match s with
  | SStep c P => c * mu P
  | SMax f g => LPRmax (SimpleIntegral mu f) (SimpleIntegral mu g)
  end.

Definition LPRindicator (P : Prop) : LPReal.
Proof. refine 
( {| lbound := fun q => P /\ (q < 1)%Qnn |}).
- intros. intuition. eapply Qnnle_lt_trans; eassumption. 
- intros. destruct H. exists (Qnndiv (q + 1) (1 + 1))%Qnn. intuition.
  admit. admit. 
Defined.

Lemma LPRind_bounded (P : Prop) : LPRindicator P <= 1.
Proof.
unfold LPRle; intros; simpl in *; intuition.
Qed.

Lemma LPRind_imp (P Q : Prop) (f : P -> Q)
  : LPRindicator P <= LPRindicator Q.
Proof.
unfold LPRle; intros; simpl in *. intuition.
Qed.

Lemma LPRind_iff (P Q : Prop) (equiv : P <-> Q)
  : LPRindicator P = LPRindicator Q.
Proof.
apply LPReq_compat; split;
unfold LPRle; intros; simpl in *; intuition.
Qed.

Lemma LPRind_true (P : Prop) : P -> LPRindicator P = 1.
Proof. intros. apply LPReq_compat.
split.
- apply LPRind_bounded.
- unfold LPRle; intros; simpl in *. intuition.
Qed.

Lemma LPRind_false (P : Prop) : ~ P -> LPRindicator P = 0.
Proof. intros. apply LPReq_compat. 
split.
- unfold LPRle; intros; simpl in *. intuition.
- apply LPRzero_min.
Qed.

Hint Resolve Qnnle_refl.

Lemma LPRind_scale_le {P : Prop} {x y : LPReal}
  : (P -> x <= y) -> LPRindicator P * x <= y.
Proof.
intros. unfold LPRle; simpl in *; intros.
destruct H0 as [a [b [pa [pb ab]]]].
destruct pa. apply H in H0. apply H0. eapply dclosed. 
eassumption. eapply Qnnle_trans. eassumption.
replace b with (1 * b)%Qnn at 2 by ring.
apply Qnnmult_le_compat. apply Qclt_le_weak. assumption.
apply Qnnle_refl.
Qed.

Lemma LPRind_mult {U V : Prop}
  : LPRindicator (U /\ V) = LPRindicator U * LPRindicator V.
Proof.
apply LPReq_compat. 
split; unfold LPRle; simpl in *; intros.
- admit.
- destruct H as [a [b [pa [pb ab]]]]. intuition.
  eapply Qnnle_lt_trans. eassumption. admit. 
Qed.

Lemma LPRind_max {U V : Prop}
  : LPRindicator (U \/ V) = LPRmax (LPRindicator U) (LPRindicator V).
Proof.
apply LPReq_compat.
split; unfold LPRle; simpl in *; intros; intuition.
Qed.

Lemma LPRind_min {U V : Prop}
  : LPRindicator (U /\ V) = LPRmin (LPRindicator U) (LPRindicator V).
Proof.
apply LPReq_compat.
split; unfold LPRle; simpl in *; intros; intuition.
Qed.

Lemma LPRind_modular {U V : Prop} :
   LPRindicator U + LPRindicator V =
   LPRindicator (U /\ V) + LPRindicator (U \/ V).
Proof.
apply LPReq_compat; split; unfold LPRle; intros q H.
- destruct H.
  + apply LPRplusR. rewrite LPRind_max. left. assumption.
  + apply LPRplusR. rewrite LPRind_max. right. assumption.
  +  simpl in *. intuition. eapply LPRplusB. rewrite LPRind_min.
     simpl in *. intuition.  apply H3. apply H3. rewrite LPRind_max.
     simpl. right. split. apply H. apply H4. assumption.
- destruct H.
  + eapply LPRplusB; simpl in *; intuition. eassumption. eassumption.
    replace q with (q + 0)%Qnn at 1 by ring.
    apply Qcplus_le_compat. apply Qcle_refl. apply nonneg.
  + simpl in *. destruct H. destruct H. 
    * apply LPRplusL. simpl. intuition.
    * apply LPRplusR. simpl. intuition.
  + simpl in *. eapply LPRplusB; simpl in *; intuition.
    eapply H3. assumption. eapply H4. assumption. assumption.
    assumption.
Qed.

Definition unitProb {A} (a : A) (P : A -> Prop) : LPReal :=
  LPRindicator (P a).

(* Here we consider a Simple as a pointwise function, in a sense,
   by integrating against a Dirac delta. *)
Definition SimpleEval {A : Type} (f : Simple A) (x : A) : LPReal :=
  SimpleIntegral (unitProb x) f.

Record IntegralT (A : Type) :=
  { integral : (A -> LPReal) -> Valuation A -> LPReal
  ; int_simple_sup : forall {f : A -> LPReal} {mu : Valuation A},
      integral f mu = LPRsup (fun (pr : { s | pointwise LPRle (SimpleEval s) f}) =>
      SimpleIntegral mu (proj1_sig pr))
  ; int_simple_ge : forall {s : Simple A} {f : A -> LPReal} {mu : Valuation A},
      pointwise LPRle f (SimpleEval s)
    -> integral f mu <= SimpleIntegral mu s
  ; int_monotonic : forall {f g : A -> LPReal}
     , pointwise LPRle f g -> forall (mu : Valuation A)
     , integral f mu <= integral g mu
  ; int_adds : forall {f g : A -> LPReal} {mu : Valuation A}
     , integral f mu + integral g mu = integral (fun x => f x + g x) mu
  ; int_scales : forall {f : A -> LPReal} {c : LPReal} {mu : Valuation A}
     , c * integral f mu = integral (fun x => c * f x) mu
  }.

Axiom integration : forall (A : Type), IntegralT A.

Lemma int_simple_le {A : Type} :
forall {s : Simple A} {f : A -> LPReal} {mu : Valuation A},
      pointwise LPRle (SimpleEval s) f
    ->  SimpleIntegral mu s <= integral _ (integration A) f mu.
Proof. intros.
pose (exist (fun s' => pointwise LPRle (SimpleEval s') f) s H).
eapply LPRle_trans. Focus 2.
rewrite int_simple_sup. eapply LPRsup_ge.
instantiate (1 := s0). simpl.
apply LPRle_refl.
Qed.

Lemma int_simple {A : Type} {s : Simple A} {mu : Valuation A}
  : integral _ (integration A) (SimpleEval s) mu = SimpleIntegral mu s.
Proof.
apply LPReq_compat.
split; [apply int_simple_ge | apply int_simple_le]
  ; unfold pointwise; intros a; apply LPRle_refl.
Qed.

Definition unit {A : Type} (a : A) : Valuation A.
Proof. refine (
 {| val := unitProb a |}
); intros.
- apply LPReq_compat. unfold LPReq. split.
  unfold unitProb. unfold LPRle. intros.
  destruct H. subst. simpl. apply Qcle_refl.
  destruct H. destruct H. apply LPRzero_min.
- unfold LPRle. intros q Hq. destruct Hq.
  left. assumption. right. destruct H0.
  split. apply H. assumption. assumption.
- unfold unitProb. apply LPRind_modular.
Defined.

(* Pushforward of a measure, i.e., map a function over a measure *)
Definition map {A B : Type} (f : A -> B) (v : Valuation A)
  : Valuation B.
Proof. refine (
  {| val := fun prop => val v (fun x => prop (f x)) |}
); intros.
- apply strict.
- apply monotonic. auto.
- apply modular; auto.
Defined.

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 = (andLq + orLq) + (andRq + orRq).
Proof. intros. ring. Qed.

Lemma LPRplus_eq_compat : forall x y x' y',
  x = x' -> y = y' -> x + y = x' + y'.
Proof. intros. subst. reflexivity. Qed.

Definition add {A : Type} (ValL ValR : Valuation A) : Valuation A.
Proof. refine (
  {| val := fun P => ValL P + ValR P |}
); intros.
- rewrite strict. rewrite strict. ring.
- apply LPRplus_le_compat; apply monotonic; assumption.
- rewrite qredistribute. 
  rewrite (qredistribute (ValL (fun z => U z /\ V z))).
  apply LPRplus_eq_compat; apply modular.
Defined.

Lemma LPRmult_eq_compat : forall x y x' y',
  x = x' -> y = y' -> x * y = x' * y'.
Proof. intros. subst. reflexivity. Qed.

Definition scale {A : Type} (c : LPReal) 
  (Val : Valuation A) : Valuation A.
Proof. refine (
  {| val := fun P => c * Val P |}
); intros.
- rewrite strict. ring.
- apply LPRmult_le_compat. apply LPRle_refl.
  apply monotonic; assumption.
- replace (c * Val U + c * Val V) with (c * (Val U + Val V)) by ring.
  replace (c * Val _ + c * Val _) 
  with (c * (Val (fun z : A => U z /\ V z) + Val (fun z : A => U z \/ V z))) by ring.
  apply LPRmult_eq_compat. reflexivity.
  apply modular.
Qed.

Definition zeroVal {A : Type} : Valuation A.
Proof. refine (
  {| val := fun P => 0 |}
).
- reflexivity.
- intros. apply LPRle_refl.
- intros. reflexivity.
Defined.

Definition Valle {A : Type} (val1 val2 : Valuation A) : Prop :=
  forall (P : A -> Prop), val1 P <= val2 P.

Lemma Valle_refl {A : Type} (val : Valuation A) : Valle val val.
Proof. unfold Valle. intros. apply LPRle_refl. Qed.

Lemma Valle_trans {A : Type} (x y z : Valuation A)
  : Valle x y -> Valle y z -> Valle x z.
Proof. intros. unfold Valle in *. intros P.
eapply LPRle_trans. apply H. apply H0.
Qed.

Definition Measurable {A B : Type} (f : A -> B)
  := forall (PB : B -> Prop), exists (PA : A -> Prop), forall (a : A), PB (f a) <-> PA a.

Lemma all_measurable {A B : Type} (f : A -> B)
  : Measurable f.
Proof. unfold Measurable. intros.
exists (fun a => PB (f a)). intros. split; trivial.
Qed.

Definition Valeq {A : Type} (val1 val2 : Valuation A) : Prop :=
  forall (P : A -> Prop), val1 P = val2 P.

Lemma Valle_antisym {A : Type} (x y : Valuation A)
  : Valle x y -> Valle y x -> Valeq x y.
Proof. intros. unfold Valle, Valeq in *. intros.
apply LPRle_antisym. apply H. apply H0.
Qed.

Lemma Valeq_compat_OK 
  (proof_irrel : forall (P : Prop) (x y : P), x = y)
  { A : Type }
  : forall (mu nu : Valuation A), Valeq mu nu -> mu = nu. 
Proof.
intros.
unfold Valeq in *.
destruct mu, nu. simpl in *.
assert (val0 = val1).
apply functional_extensionality. assumption.
induction H0.
pose proof (proof_irrel _ strict0 strict1).
induction H0.
pose proof (proof_irrel _ monotonic0 monotonic1).
induction H0.
pose proof (proof_irrel _ modular0 modular1).
induction H0.
reflexivity.
Qed.

Axiom Valeq_compat : forall (A : Type) (mu nu : Valuation A)
  , Valeq mu nu -> mu = nu.

Lemma Valplus_comm {A : Type} : forall {x y : Valuation A}
  , add x y = add y x.
Proof.
intros. apply Valeq_compat.
unfold Valeq. intros. simpl. ring.
Qed.

Lemma integral_zero {A : Type} : forall {mu : Valuation A} (c : LPReal)
  , integral A (integration A) (SimpleEval (SStep c (K False))) mu = 0.
Proof.
intros.
rewrite int_simple. simpl. 
replace (mu (K False)) with 0. ring. symmetry. apply strict.
Qed.

Lemma int_pointwise_eq {A : Type} : 
  forall (f g : A -> LPReal), pointwise LPReq f g ->
  forall (mu : Valuation A),
  integral _ (integration A) f mu = integral _ (integration A) g mu.
Proof.
intros. apply LPReq_compat. unfold pointwise in H.
unfold LPReq. split; apply int_monotonic; unfold pointwise;
apply H.
Qed.

Definition bind {A B : Type}
  (v : Valuation A) (f : A -> Valuation B)
  : Valuation B.
Proof. refine (
  {| val := fun P => integral A (integration A) (fun x => (f x) P) v |}
).
- apply LPReq_compat. unfold LPReq. split.
  erewrite <- integral_zero.
  apply int_monotonic.
  unfold pointwise. intros.
  instantiate (1 := 0).
  rewrite strict. apply LPRzero_min.
  apply LPRzero_min.
- intros. apply int_monotonic.
  unfold pointwise. intros.
  apply monotonic. assumption.
- intros. do 2 rewrite int_adds. apply int_pointwise_eq.
  unfold pointwise. intros a.
  assert (
((f a) U + (f a) V) =
((f a) (fun z : B => U z /\ V z) + (f a) (fun z : B => U z \/ V z))
). apply modular. rewrite H. split; apply LPRle_refl.
Defined.

Definition product {A B : Type}
  (muA : Valuation A) (muB : Valuation B)
  : Valuation (A * B) := 
  bind muA (fun a => map (fun b => (a, b)) muB).

Theorem int_dirac_simple {A : Type} {s : Simple A} {a : A} :
 SimpleIntegral (unit a) s = SimpleEval s a.
Proof.
unfold SimpleEval. induction s; simpl; reflexivity.
Qed.

Theorem int_indicator {A : Type} {P : A -> Prop} {mu : Valuation A}
  : integral A (integration A) (fun x => LPRindicator (P x)) mu = mu P.
Proof.
rewrite int_pointwise_eq with (g := SimpleEval (SStep 1 P)).
rewrite int_simple. simpl. ring.
unfold SimpleEval. simpl. unfold unitProb.
unfold pointwise. intros. apply LPReq_compat_backwards. ring.
Qed.


Theorem int_dirac_test {A : Type} {f : A -> LPReal} {a : A}
  (s : Simple A)
  : pointwise LPRle (SimpleEval s) f
  -> integral A (integration A) (SimpleEval s) (unit a) <= f a.
Proof.
intros. rewrite int_simple. rewrite int_dirac_simple. apply H. 
Qed.

Lemma undo_proj1sig {A : Type} {B : A -> Prop} 
  (a : A) (b : B a) : proj1_sig (exist _ a b) = a.
Proof. reflexivity. Qed.

Theorem int_dirac {A : Type} {f : A -> LPReal} {a : A}
  : integral A (integration A) f (unit a) = f a.
Proof.
intros.
pose (s := SStep (f a) (fun a' => a = a')).
 rewrite int_simple_sup. eapply LPRsup_prop.
- intros pr. destruct pr. simpl. 
  replace (unitProb a) with (val (unit a)) by reflexivity.
  rewrite int_dirac_simple. apply p.
- eexists. rewrite undo_proj1sig.
  instantiate (1 := s).
  rewrite int_dirac_simple. unfold SimpleEval; simpl.
  unfold unitProb. rewrite LPRind_true by reflexivity.
  replace (f a * 1) with (f a) by ring.
  apply LPRle_refl.
  Grab Existential Variables.
  simpl. unfold pointwise. intros. unfold SimpleEval.
  simpl. rewrite (SRmul_comm LPRsrt). apply LPRind_scale_le.
  intros H. induction H. apply LPRle_refl.
Qed. 

Theorem unitProdId {A B : Type}
  (a : A) (muB : Valuation B) (P : (A * B) -> Prop)
  : product (unit a) muB P = muB (fun b => P (a, b)).
Proof. simpl. rewrite int_dirac. reflexivity. Qed.

Theorem product_prop {A B : Type}
  (muA : Valuation A)
  (muB : Valuation B)
  (PA : A -> Prop) (PB : B -> Prop)
  : (product muA muB) (fun p => let (x, y) := p in PA x /\ PB y)
  = muA PA * muB PB.
Proof. simpl.
rewrite <- int_indicator.
rewrite (SRmul_comm LPRsrt).
rewrite int_scales.
apply int_pointwise_eq. unfold pointwise.
intros a.
do 2 rewrite <- int_indicator.
rewrite (SRmul_comm LPRsrt).
rewrite int_scales.
eapply LPReq_compat_backwards.
apply int_pointwise_eq.
unfold pointwise. intros.
rewrite LPRind_mult.
apply LPReq_refl.
Qed.

(** WARNING: Work in progress *)

Require Vector.

Fixpoint product_n {A : Type} (v : Valuation A)
  (n : nat) : Valuation (Vector.t A n) := match n with
  | 0 => unit (Vector.nil A)
  | S n' => bind v (fun x => map (Vector.cons A x n') (product_n v n'))
  end.

Require Streams.

Fixpoint take_n {A : Type} (s : Streams.Stream A) (n : nat)
  : Vector.t A n := match n, s with
  | 0, _ => Vector.nil A
  | S n', Streams.Cons x xs => Vector.cons A x n' (take_n xs n')
end.

Definition restrictToVec {A : Type} (P : Streams.Stream A -> Prop)
  (n : nat) (x : Vector.t A n) : Prop :=
  forall (s : Streams.Stream A), take_n s n = x -> P s.

Lemma restrictToVecBot {A : Type} {n : nat}
  (nonempty : A)
  : forall xs, ~ (@restrictToVec A (K False) n xs).
Proof.
admit. 
Qed.

Lemma restrictToVecMonotonicP {A : Type} {n : nat}
  : forall { U V : Streams.Stream A -> Prop }
  , (forall (s : Streams.Stream A), U s -> V s)
  -> forall xs, restrictToVec U n xs -> restrictToVec V n xs.
Proof.
intros. unfold restrictToVec in *.
intros s take. apply H. apply H0. assumption.
Qed.

Lemma restrictToVecMonotonicN {A : Type} : 
 forall (v : Valuation A) (U : Streams.Stream A -> Prop),
 v (K True) = 1 ->
 forall n m : nat,
 (n <= m)%nat ->
 (product_n v n) (restrictToVec U n) <=
 (product_n v m) (restrictToVec U m).
Proof. intros. generalize dependent U.
induction H0; intros. apply LPRle_refl.
simpl.
eapply LPRle_trans. apply IHle.
rewrite <- int_indicator in H.
replace ((product_n v m) (restrictToVec U m))
   with ((product_n v m) (restrictToVec U m) * 1) by ring.
rewrite <- H.
rewrite int_scales.
apply int_monotonic.
unfold pointwise. intros a. unfold K.
rewrite LPRind_true by trivial.
replace ((product_n v m) (restrictToVec U m) * 1)
   with ((product_n v m) (restrictToVec U m)) by ring.
(* should see that we can snoc instead of cons and get the
   same measure *)
apply monotonic. intros.
admit.
Qed.


Theorem inf_product {A : Type} (v : Valuation A)
  (nonempty : A)
  (vIsProb : v (K True) = 1)
  : Valuation (Streams.Stream A).
Proof.
refine (
  {| val := fun P => LPRsup (fun n => (product_n v n) (restrictToVec P n))
  |}
); intros.
- apply LPReq_compat. split; [| apply LPRzero_min].
  unfold LPRle. simpl. intros. destruct H. subst.
  apply Qnnle_refl. destruct H.
  apply (monotonic _ _ (K False)) in H.
  rewrite (strict (product_n v x)) in H.
  simpl in H. assumption.
  apply restrictToVecBot.
  apply nonempty.
- apply LPRsup_monotonic.
  intros n. induction n; simpl.
  + unfold unitProb. apply LPRind_imp.
    unfold restrictToVec. intros H1.
    intros. apply H. apply H1. apply H0.
  + apply int_monotonic. unfold pointwise.
    intros a. apply monotonic. intros.
    eapply restrictToVecMonotonicP. eassumption.
    assumption.
- do 2 (rewrite <- LPRsup_nat_ord; 
  try (apply restrictToVecMonotonicN);
  try assumption).
  apply LPRsup_eq_pointwise.
  intros idx.
  (* apply modular. *)
Abort.

CoInductive Partial {A : Type} : Type :=
 | Now : A -> Partial
 | Later : Partial -> Partial.

CoFixpoint loop {A : Type} := @Later A loop.

Arguments Partial : clear implicits.

Fixpoint fixn {A : Type}
  (f : Valuation A -> Valuation A) (n : nat)
  : Valuation A
  := match n with
  | 0 => zeroVal
  | S n' => f (fixn f n')
  end.

Fixpoint runPartial {A : Type} (px : Partial A)
  (n : nat) : option A := match px with
  | Now x => Some x
  | Later px' => match n with
    | 0 => None
    | S n' => runPartial px n'
    end 
  end.

Definition partialize {A : Type} (P : A -> Prop)
  (px : Partial A) : Prop := exists n, match runPartial px n with
  | None => False
  | Some x => P x
  end.

Lemma partial_now {A : Type} (a : A) (n : nat)
  : runPartial (Now a) n = Some a.
Proof. induction n; unfold runPartial; intuition. Qed. 

Lemma partial_mono {A : Type} : forall (m n : nat) (px : Partial A)
  (a : A), (m <= n)%nat -> runPartial px m = Some a -> runPartial px n = Some a.
Proof.
intros. induction H. assumption. simpl. rewrite IHle.
  destruct px. simpl in *. rewrite partial_now in H0. assumption.
  reflexivity.
Qed.

Lemma partialize_and {A : Type} {U V : A -> Prop}
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  : partialize (fun z => U z /\ V z) 
  = fun z => partialize U z /\ partialize V z.
Proof. apply functional_extensionality.
intros. apply propext. split; intros;
unfold partialize in *. destruct H;
split; exists x0; destruct (runPartial x x0); intuition.
destruct H. destruct H. destruct H0.
exists (max x0 x1). destruct (runPartial x x0) eqn:p0;
  destruct (runPartial x x1) eqn:p1; try contradiction.
  apply partial_mono with (n := max x0 x1) in p0.
  apply partial_mono with (n := max x0 x1) in p1.
  rewrite p0 in p1. injection p1. intros. subst.
  rewrite p0. split; assumption.
  apply Max.le_max_r. apply Max.le_max_l.
Qed.

Lemma partialize_or {A : Type} {U V : A -> Prop}
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  : partialize (fun z => U z \/ V z) 
  = fun z => partialize U z \/ partialize V z.
Proof. apply functional_extensionality.
intros. apply propext. split; intros;
unfold partialize in *. destruct H.
destruct (runPartial x x0) eqn:partial.
destruct H; [left | right]; exists x0;
rewrite partial; assumption. contradiction.
destruct H; destruct H; exists x0;
destruct (runPartial x x0) eqn:partial; intuition.
Qed.

Definition partialValuation {A : Type}
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  (v : Valuation (Partial A))
  : Valuation A.
Proof. refine (
  {| val := fun P => v (partialize P) |}
).
- apply LPReq_compat. split. 
  + erewrite <- strict.
    apply monotonic. intros. unfold partialize, K in *.
    destruct H. destruct (runPartial z x); assumption.
  + apply LPRzero_min.
- intros.
  apply monotonic. intros z PU.
  unfold partialize in *. destruct PU.
  exists x. destruct (runPartial z x). apply H; assumption.
  assumption.
- intros. rewrite partialize_and. rewrite partialize_or.
  apply modular.
  apply propext. apply propext.
Qed.

Lemma fixnmono {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, Valle u v -> Valle (f u) (f v))
  : forall (n : nat), Valle (fixn f n) (fixn f (S n)).
Proof. intros. induction n.
simpl. unfold Valle; intros. simpl. apply LPRzero_min.
simpl. apply fmono. assumption.
Qed.

Lemma fixnmono2 {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, Valle u v -> Valle (f u) (f v))
  : forall (m n : nat), (m <= n)%nat -> Valle (fixn f m) (fixn f n).
Proof. intros. induction H. apply Valle_refl. 
eapply Valle_trans. eassumption. apply fixnmono. assumption.
Qed.

Definition fixValuation {A : Type}
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, Valle u v -> Valle (f u) (f v))
  : Valuation A.
Proof. refine (
  {| val := fun P => LPRsup (fun n => (fixn f n) P) |}
).
- apply LPReq_compat. split. 
  + apply LPRsup_le. intros. erewrite <- strict.
    apply monotonic. intros. assumption. 
  + apply LPRzero_min.
- intros. apply LPRsup_monotonic. intros n.
  apply monotonic. assumption. 
- intros.
  rewrite <- LPRsup_nat_ord by (intros; apply fixnmono2; assumption).
  rewrite <- LPRsup_nat_ord by (intros; apply fixnmono2; assumption).
  apply LPRsup_eq_pointwise. intros.
  apply modular.
Defined.


Lemma fixValuation_subProb {A : Type}
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, Valle u v -> Valle (f u) (f v))
  (fbounded : forall v, val v (K True) <= 1 -> f v (K True) <= 1)
  : (fixValuation propext f fmono) (K True) <= 1.
Proof. simpl. apply LPRsup_le.
intros n. induction n. simpl. apply LPRzero_min.
simpl. apply fbounded. assumption.
Qed.

Definition rejectionFunc {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (f : Valuation A) : Valuation A :=
  bind v (fun a => if pred a
    then unit a
    else f).

Lemma rejectionFunc_mono {A : Type} (v : Valuation A)
  (pred : A -> bool)
  : let f := rejectionFunc v pred 
    in forall mu1 mu2, Valle mu1 mu2 -> Valle (f mu1) (f mu2).
Proof. 
intros. unfold Valle in *. intros P. simpl.
apply int_monotonic. unfold pointwise. intros a.
destruct (pred a). apply LPRle_refl. apply H.
Qed.

Definition rejection {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  : Valuation A
  := fixValuation propext (rejectionFunc v pred)
     (rejectionFunc_mono v pred).

Definition rejection_subProb {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (vProb : v (K True) = 1)
  (predPos : ~ (v (fun x => pred x = true) <= 0))
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  : (rejection v pred propext) (K True) <= 1.
Proof.
apply fixValuation_subProb. intros. unfold rejectionFunc.
simpl. rewrite <- vProb. rewrite <- int_indicator.
apply int_monotonic. unfold pointwise. unfold K.
intros. destruct (pred a). simpl.
apply LPRind_imp. trivial.
rewrite LPRind_true by trivial. apply H.
Qed.

Definition inf_productFunc {A : Type} (v : Valuation A)
  (f : Valuation (Streams.Stream A)) : Valuation (Streams.Stream A)
  := bind v (fun x => map (Streams.Cons x) f).

Lemma inf_productFunc_mono {A : Type} (v : Valuation A)
  : forall mu1 mu2, Valle mu1 mu2 -> Valle (inf_productFunc v mu1) (inf_productFunc v mu2).
Proof. 
intros. unfold Valle in *. intros P. simpl.
apply int_monotonic. unfold pointwise. intros a.
apply H.
Qed.

Definition inf_product {A : Type} (v : Valuation A)
  (propext : forall (P Q : Prop), (P <-> Q) -> P = Q)
  : Valuation (Streams.Stream A)
  := fixValuation propext (inf_productFunc v) (inf_productFunc_mono v).
