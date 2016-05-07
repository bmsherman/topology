Require Import QArith QFacts Morphisms SetoidClass.

Record LReal :=
  { lbound :> Q -> Prop
  ; dclosed : forall q, lbound q -> forall q', q' <= q -> lbound q'
  ; uopen : forall q, lbound q -> exists q', (q < q') /\ lbound q'
  ; nonempty : exists q, lbound q
  }.

Definition LRle (x y : LReal) : Prop := forall q, x q -> y q.
Definition LReq (x y : LReal) : Prop := LRle x y /\ LRle y x.
Definition LRlt (x y : LReal) : Prop := exists q, ~ x q /\ y q.

Definition LRQ (x : Q) : LReal.
Proof.
refine ( {| lbound := fun q' => q' < x |}); intros.
- eapply Qle_lt_trans; eassumption.
- destruct (Qbetween q x H) as (mid & between).
  exists mid. apply between.
- exists (x - 1). apply Qlt_minus_iff.
  ring_simplify. reflexivity.
Defined.

Inductive LRplusT {x y : LReal} : Q -> Prop :=
  LRplusB : forall q q' sum, x q -> y q' -> sum <= q + q' -> LRplusT sum.

Arguments LRplusT : clear implicits. 

Definition LRplus (x y : LReal) : LReal.
Proof.
refine ( {| lbound := LRplusT x y |}); intros.
- destruct H. econstructor; try eassumption.
  rewrite H0. apply H2.
- destruct H. destruct (uopen _ _ H).
  destruct H2.
  exists (x0 + q'). split. eapply Qle_lt_trans. eassumption.
  apply Qplus_lt_l. assumption. 
  econstructor; try eassumption.
  reflexivity.
- destruct (nonempty x). destruct (nonempty y).
  exists (x0 + x1). econstructor; eauto.
  reflexivity.
Defined.

Require Import Coq.Sets.Ensembles ProofIrrelevance.

Infix "+" := LRplus : LR_scope.
Infix "<=" := LRle : LR_scope.
Infix "<" := LRlt : LR_scope.
Infix "==" := LReq : LR_scope.
Notation "0" := (LRQ 0) : LR_scope. 
Delimit Scope LR_scope with LR.
Local Open Scope LR.

Theorem LRplus_comm_le : forall x y, x + y <= y + x.
Proof.
unfold LRle. simpl. intros. destruct H.
econstructor; eauto. rewrite Qplus_comm. assumption.
Qed.

Theorem LRplus_comm : forall x y, (x + y == y + x)%LR.
Proof.
intros. unfold LReq; split; apply LRplus_comm_le.
Qed.

Theorem LRplus_assoc : forall x y z, ((x + y) + z == x + (y + z))%LR.
Proof.
intros. unfold LReq; unfold LRle; split; simpl; intros;
repeat match goal with
| [ H : LRplusT _ _ _  |- _ ] => destruct H; simpl in *
| [  |- LRplusT _ _ _ ] => econstructor; simpl in *
| [  |- lbound _ _ ] => eassumption
end.
Focus 2. rewrite H1. rewrite H3. rewrite (Qplus_comm q (q'0 + q')). 
  ring_simplify. reflexivity. reflexivity.
Focus 2.
  rewrite H1. rewrite H3. rewrite (Qplus_assoc q q0 q'). 
  reflexivity. reflexivity.
Qed.

Definition LReal_eq_compat (x y : LReal) :
  (x == y)%LR -> x = y.
Proof.
intros H. unfold LReq, LRle in H. destruct H.
destruct x, y; simpl in *.
assert (lbound0 = lbound1).
apply Extensionality_Ensembles. unfold Same_set, Included, In.
split; assumption.
induction H1. f_equal; apply proof_irrelevance. 
Qed.

Lemma LRle_refl : forall (x : LReal), x <= x.
Proof.
unfold LRle. auto.
Qed.

Instance LRle_Reflexive : Reflexive LRle.
Proof.
unfold Reflexive. apply LRle_refl.
Qed.

Lemma LRle_trans : forall x y z : LReal, x <= y -> y <= z -> x <= z.
Proof.
intros. unfold LRle in *. auto.
Qed.

Instance LRle_Transitive : Transitive LRle.
Proof.
unfold Transitive. apply LRle_trans.
Qed.

Require Import Coq.Program.Basics.

Instance LReal_proper (x : LReal) : Proper (Qle --> impl) (lbound x).
Proof.
unfold Proper, respectful, impl, flip. intros.
eapply dclosed; eassumption.
Qed.

Instance LReal_proper2 (x : LReal) : Proper (Qeq ==> iff) (lbound x).
Proof.
unfold Proper, respectful. intros. split; intros; 
  (eapply dclosed; [eassumption| rewrite H; apply Qle_refl]).
Qed.

Definition LRplus_le_compat : forall x x' y y'
  , x <= x' -> y <= y' -> x + y <= x' + y'.
Proof.
intros. unfold LRle in *; simpl. intros.
destruct H1. econstructor; eauto.
Qed.

Instance LRplus_le_Proper : Proper (LRle ==> LRle ==> LRle) LRplus.
Proof.
unfold Proper, respectful. intros.
apply LRplus_le_compat; assumption.
Qed.

Instance LRplus_Proper : Proper (LReq ==> LReq ==> LReq) LRplus.
Proof.
unfold Proper, respectful. intros.
destruct H, H0. split; apply LRplus_le_compat; assumption.
Qed.

Instance LRle_Proper : Proper (LReq ==> LReq ==> iff) LRle.
Proof.
unfold Proper, respectful. intros.
destruct H, H0. split; intros.
- rewrite H1, H3. assumption.
- rewrite <- H2, <- H3. assumption.
Qed.

Instance LRle_Proper_impl : Proper (LReq ==> LReq ==> flip impl) LRle.
Proof.
unfold Proper, respectful. intros.
destruct H, H0. unfold flip, impl. intros. 
rewrite <- H2, <- H3. assumption.
Qed.

Definition LPRsup {A : Type} (inh : A) (f : A -> LReal) : LReal.
Proof.
refine ({| lbound := fun q => exists (idx : A), f idx q |}); intros.
- destruct H. exists x. rewrite H0. assumption.
- destruct H. destruct (uopen _ _ H) as (q' & qq' & fq').
  exists q'. split. assumption. exists x.  assumption.
- destruct (nonempty (f inh)). exists x. exists inh. assumption.
Defined.

Definition LRinfinity : LReal.
Proof.
refine ({| lbound := fun q => True |}); intros; auto.
- exists (q + 1)%Q. intuition. rewrite Qlt_minus_iff. ring_simplify.
  reflexivity.
- exists 0%Q. constructor.
Defined.

Theorem LRinfinity_max (r : LReal) : r <= LRinfinity.
Proof.
unfold LRle; simpl; auto.
Qed.

Definition LRmax (x y : LReal) : LReal.
Proof. refine (
  {| lbound := fun q => x q \/ y q |}
); intros.
- destruct H; [left | right]; eapply dclosed; eassumption.
- destruct H; 
  pose proof (uopen _ _ H) as H'; 
  destruct H' as [q' [qq' pq']]; exists q'; intuition.
- destruct (nonempty x) as (q & qx). exists q. auto.
Defined.

Lemma LRmax_le_and : forall x y z : LReal
  , x <= z -> y <= z -> LRmax x y <= z.
Proof. intros.
unfold LRle; simpl in *; intros; intuition.
Qed.

Lemma LRmax_le_or : forall x y z : LReal
  , z <= x \/ z <= y -> z <= LRmax x y.
Proof. intros.
unfold LRle; simpl in *; intros; intuition.
Qed.

Lemma LRmax_le {x y x' y' : LReal} 
  : x <= x' -> y <= y' -> LRmax x y <= LRmax x' y'.
Proof.
intros. unfold LRle. intros q Hmax. simpl in *.
destruct Hmax; [left | right].
- apply H. assumption.
- apply H0. assumption.
Qed.

Lemma LRmax_plus {x x' y y' : LReal}
  : LRmax (x + x') (y + y') <= LRmax x y + LRmax x' y'.
Proof.
apply LRmax_le_and; apply LRplus_le_compat; apply LRmax_le_or;
  (left; apply LRle_refl) || (right; apply LRle_refl).
Qed.

Require Import QArith.Qminmax.

Definition LRmin (x y : LReal) : LReal.
Proof. refine (
  {| lbound := fun q => x q /\ y q |}
).
- intros. destruct H; split; eapply dclosed; eassumption.
- intros. destruct H. 
  destruct (uopen _ _ H) as [q'x [qq'x pq'x]].
  destruct (uopen _ _ H0) as [q'y [qq'y pq'y]].
  exists (Qmin q'x q'y). split. eapply Q.min_glb_lt; assumption.
  split; eapply dclosed; try eassumption. apply Q.le_min_l.
  apply Q.le_min_r.
- destruct (nonempty x) as (q & qx).
  destruct (nonempty y) as (q' & q'y).
  exists (Qmin q q'). split. rewrite Q.le_min_l. assumption.
  rewrite Q.le_min_r. assumption.
Defined.

Inductive UReal := | Negate : LReal -> UReal.

Definition ubound (x : UReal) (q : Q) : Prop := match x with
  Negate l => l (- q)%Q 
  end.

Definition unegate (u : UReal) : LReal := match u with
  Negate l => l
  end.

Coercion ubound : UReal >-> Funclass.

(** A non-located real number *)
Record RealNL := 
  { lower : LReal
  ; upper : LReal
  ; disjoint : lower + upper <= 0
  }.

Theorem LReal_reassoc : forall x y a b : LReal,
  ((x + y) + (a + b)  == (x + a) + (y + b))%LR.
Proof.
intros.
(** Eventually I'd like a commutative monoid tactic
    to handle this. *) 
admit.
Qed.

Theorem LReal_reassoc_eq : forall x y a b : LReal,
  (x + y) + (a + b) = (x + a) + (y + b).
Proof.
intros. apply LReal_eq_compat. apply LReal_reassoc.
Qed.

Lemma Qopp_lt_compat: forall p q : Q, (p < q)%Q -> (- q < - p)%Q.
Proof.
Admitted.


Theorem LRzero_plus_id_l : forall x, (x + 0 == x)%LR.
Proof.
intros. unfold LReq, LRle; simpl; split; intros.
- destruct H. rewrite H1. simpl in H0.
  eapply dclosed. eassumption. rewrite H0.
  ring_simplify. reflexivity.
- destruct (uopen _ _ H) as (p & qp & xp). 
  econstructor. eapply xp. 
  rewrite Qlt_minus_iff in qp. 
  apply Qopp_lt_compat in qp. ring_simplify in qp.
  apply qp. ring_simplify. reflexivity.
Qed.

Theorem LRzero_plus_id_l_eq : forall x : LReal, x + 0 = x.
Proof.
intros. apply LReal_eq_compat. apply LRzero_plus_id_l.
Qed.

Definition RNLplus (x y : RealNL) : RealNL.
Proof.
refine ({| lower := lower x + lower y
  ; upper := upper x + upper y |}); intros.
rewrite LReal_reassoc_eq.
rewrite (disjoint y), (disjoint x). 
rewrite LRzero_plus_id_l_eq.
reflexivity.
Defined.

Lemma Qnnplus_open : forall q x y : Q, (q < x + y
  -> exists x' y', x' < x /\ y' < y /\ (q <= x' + y'))%Q.
Proof.
intros. 
pose proof (Qbetween (q - y) x).
pose proof (Qbetween (q - x) y).
Admitted.

Lemma LRQ_plus : forall x y : Q,
  (LRQ x + LRQ y == LRQ (x + y)%Q)%LR.
Proof.
intros. unfold LReq, LRle; split; simpl; intros.
- destruct H; simpl in *.
  eapply Qle_lt_trans. eassumption.
  apply Qplus_lt_le_compat; auto.
  rewrite H0. reflexivity.
- pose proof (Qnnplus_open q x y H).
  destruct H0 as (x' & y' & x'x & y'y & qx'y'). 
  econstructor; simpl; eassumption.
Qed.

Lemma LRQ_plus_eq : forall x y : Q,
  LRQ x + LRQ y = LRQ (x + y)%Q.
Proof.
intros. apply LReal_eq_compat.  apply LRQ_plus.
Qed.

Instance LRQ_Proper : Proper (Qeq ==> eq) LRQ.
Proof.
unfold Proper, respectful.
intros. apply LReal_eq_compat. 
unfold LReq, LRle; split; simpl; intros.
rewrite <- H. assumption. rewrite H. assumption.
Qed.

Definition RNLQ (q : Q) : RealNL.
Proof.
refine ({| lower := LRQ q
        ; upper := LRQ (- q)
        |}).
rewrite LRQ_plus_eq. rewrite Qplus_opp_r.
reflexivity.
Defined.

Record Real :=
  { L : LReal
  ; U : LReal
  ; cut : L + U = 0
  }.

Definition Rzero : Real.
Proof.
refine (
  {| L := LRQ 0
   ; U := LRQ 0 |}); intros.
rewrite LRzero_plus_id_l_eq. reflexivity.
Defined.

Definition Rplus (x y : Real) : Real.
Proof.
refine (
  {| L := L x + L y
   ; U := U x + U y
  |}).
rewrite LReal_reassoc_eq.
rewrite (cut x), (cut y).
rewrite LRzero_plus_id_l_eq. reflexivity.
Defined.

Inductive RmultT {x y : LReal} : Q -> Prop :=
  | RmultLH : forall qx qy, x qx -> y qy -> RmultT (- qx * qy).