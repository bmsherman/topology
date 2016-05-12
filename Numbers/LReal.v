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

Theorem LRplus_comm_eq : forall x y, x + y = y + x.
Proof.
intros. apply LReal_eq_compat. apply LRplus_comm.
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

Lemma LReq_refl : forall (x : LReal), (x == x)%LR.
Proof.
intros; unfold LReq; split; apply LRle_refl.
Qed.

Lemma LReq_trans : forall x y z : LReal, (x == y)%LR -> (y == z)%LR -> (x == z)%LR.
Proof.
intros. destruct H, H0. split; eapply LRle_trans; eassumption.
Qed.

Lemma LReq_sym : forall x y : LReal, (x == y)%LR -> (y == x)%LR.
Proof.
intros. destruct H; split; auto.
Qed.

Instance LReq_Reflexive : Reflexive LReq.
Proof.
unfold Reflexive. apply LReq_refl.
Qed.

Instance LReq_Transitive : Transitive LReq.
Proof.
unfold Transitive. apply LReq_trans.
Qed.

Instance LReq_Symmetric : Symmetric LReq.
Proof.
unfold Symmetric. apply LReq_sym.
Qed.

Instance LReq_Equivalence : Equivalence LReq.
Proof.
constructor. apply LReq_Reflexive. apply LReq_Symmetric.
apply LReq_Transitive.
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

Delimit Scope RNL_scope with RNL.

(** A non-located real number *)
Record RealNL := 
  { lower : LReal
  ; upper : LReal
  ; disjoint : lower + upper <= 0
  }.

Definition RNLopp (x : RealNL) : RealNL.
Proof.
refine (
  {| lower := upper x
   ; upper := lower x
  |}).
rewrite LRplus_comm. apply disjoint.
Defined.

Notation "- x" := (RNLopp x) : RNL_scope.

Definition RNLle (x y : RealNL) : Prop :=
  lower x <= lower y /\ upper y <= upper x.

Infix "<=" := RNLle : RNL_scope.

Theorem RNLle_refl : forall x : RealNL, (x <= x)%RNL.
Proof.
intros. unfold RNLle. split; reflexivity.
Qed.

Theorem RNLle_trans : forall x y z : RealNL, (x <= y -> y <= z -> x <= z)%RNL.
Proof.
intros. destruct H, H0.
split; eapply LRle_trans; eassumption.
Qed.

Instance RNLle_Reflexive : Reflexive RNLle := RNLle_refl.
Instance RNLle_Transitive : Transitive RNLle := RNLle_trans.

Definition RNLeq (x y : RealNL) : Prop := (x <= y /\ y <= x)%RNL.

Infix "==" := RNLeq : RNL_scope.

Theorem RNLeq_refl : forall x : RealNL, (x == x)%RNL.
Proof.
intros. unfold RNLeq; split; apply RNLle_refl.
Qed.

Theorem RNLeq_sym : forall x y : RealNL, (x == y)%RNL -> (y == x)%RNL.
Proof.
intros. destruct H. split; assumption.
Qed.

Theorem RNLeq_trans : forall x y z : RealNL, 
  (x == y)%RNL -> (y == z)%RNL -> (x == z)%RNL.
Proof.
intros. destruct H, H0. split; eapply RNLle_trans; eassumption.
Qed.

Instance RNLeq_Reflexive : Reflexive RNLeq := RNLeq_refl.
Instance RNLeq_Symmetric : Symmetric RNLeq := RNLeq_sym.
Instance RNLeq_Transitive : Transitive RNLeq := RNLeq_trans.

Theorem LReal_reassoc : forall x y a b : LReal,
  ((x + y) + (a + b)  == (x + a) + (y + b))%LR.
Proof.
intros.
(** Eventually I'd like a commutative monoid tactic
    to handle this. *) 
admit.
Qed.

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

Definition RNLplus (x y : RealNL) : RealNL.
Proof.
refine ({| lower := lower x + lower y
  ; upper := upper x + upper y |}); intros.
rewrite LReal_reassoc.
rewrite (disjoint y), (disjoint x). 
rewrite LRzero_plus_id_l.
reflexivity.
Defined.

Lemma LRQ_plus : forall x y : Q,
  (LRQ x + LRQ y == LRQ (x + y)%Q)%LR.
Proof.
intros. unfold LReq, LRle; split; simpl; intros.
- destruct H; simpl in *.
  eapply Qle_lt_trans. eassumption.
  apply Qplus_lt_le_compat; auto.
  rewrite H0. reflexivity.
- pose proof (Qplus_open q x y H).
  destruct H0 as (x' & y' & x'x & y'y & qx'y'). 
  econstructor; simpl; eassumption.
Qed.

Inductive RmultT {xl xu yl yu : LReal} : Q -> Prop :=
  | RmultB : forall qxl qxu qyl qyu p
    , xl qxl -> xu qxu -> yl qyl -> yu qyu
    -> (p <= qxl * qyl
    -> p <= - qxl * qyu
    -> p <= - qxu * qyl
    -> p <= qxu * qyu
    -> RmultT p)%Q.

Arguments RmultT : clear implicits.

Definition RmultLbound (x y : RealNL) : LReal.
Proof.
refine ({| lbound := RmultT (lower x) (upper x) (lower y) (upper y) |}); intros.
- induction H. econstructor; try eassumption; rewrite H0; assumption.
- admit.
- admit.
Qed.

(** I just wrote this down quickly. It is probably wrong! *)
Definition RNLmult (x y : RealNL) : RealNL.
Proof.
refine (
  {| lower := RmultLbound x y
   ; upper := RmultLbound (RNLopp x) (RNLopp y)
  |}).
Abort.

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
rewrite LRQ_plus. rewrite Qplus_opp_r.
reflexivity.
Defined.

Record Real :=
  { L : LReal
  ; U : LReal
  ; cut : (L + U == 0)%LR
  }.

Definition Rzero : Real.
Proof.
refine (
  {| L := LRQ 0
   ; U := LRQ 0 |}); intros.
rewrite LRzero_plus_id_l. reflexivity.
Defined.

Definition Rplus (x y : Real) : Real.
Proof.
refine (
  {| L := L x + L y
   ; U := U x + U y
  |}).
rewrite LReal_reassoc.
rewrite (cut x), (cut y).
rewrite LRzero_plus_id_l. reflexivity.
Defined.

Definition Ropp (x : Real) : Real.
Proof.
refine (
  {| L := U x
   ; U := L x
  |}).
rewrite LRplus_comm_eq.
apply (cut x).
Defined.