Require Import Qnn.

Local Open Scope Qnn.

Require Import FunctionalExtensionality.

(** Nonnegative lower reals *)
(* These guys are interesting because we can have proofy
   bits in them. For example, we can create a real number
   which is 0 if P = NP and 1 if P /= NP. *)
Record LPReal :=
  { lbound :> Qnn -> Prop
  ; dclosed : forall q, lbound q -> forall q', q' <= q -> lbound q'
  ; uopen   : forall q, lbound q -> exists q', q < q' /\ lbound q'
  }.

Definition LPRle (r s : LPReal) : Prop :=
  forall q, r q -> s q.

Definition LPRge (r s : LPReal) : Prop := LPRle s r.

Definition LPRlt (r s : LPReal) : Prop :=
  exists q, ~ r q /\ s q.

Definition LPRgt (r s : LPReal) : Prop := LPRlt s r.

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
- intros. pose proof (Qnnbetween q0 q H). destruct H0.
  exists x. assumption.
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
    rewrite (SRadd_comm Qnnsrt).
    rewrite (SRadd_comm Qnnsrt x0).
    apply Qnnplus_le_lt_compat. apply Qnnle_refl. assumption. 
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
  apply Qnnmult_le_compat. apply Qnnle_refl. apply Qnnlt_le_weak.
  assumption. apply Qnnmult_lt_compat_r.
  eapply Qnnle_lt_trans. apply (nonneg b). assumption. assumption.
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
| [ H : _ < 0 |- _ ] => apply Qnnlt_not_le in H; unfold not in H;
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
  apply Qnnplus_le_compat. apply Qnnle_refl. assumption.
- apply LPRplusR. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- eapply LPRplusR. LPRsrttac.
- eapply LPRplusB; try eassumption. LPRsrttac.
- apply LPRplusR. LPRsrttac.
- eapply LPRplusB with q (q'0 + q'). assumption. 
  eapply LPRplusB with q'0 q'; try assumption.
  apply Qnnle_refl. eapply Qnnle_trans. eassumption.
  rewrite (SRadd_assoc Qnnsrt). 
  apply Qnnplus_le_compat. assumption. apply Qnnle_refl. 
- eapply dclosed. eassumption. eapply Qnnle_trans. eassumption.
  replace x0 with (1 * x0) at 2 by ring.
  apply Qnnmult_le_compat. apply Qnnlt_le_weak. assumption.
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
  rewrite (SRdistr_l Qnnsrt). apply Qnnplus_le_compat.
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
Infix ">"  := LPRgt : LPR_scope.
Infix "<"  := LPRlt : LPR_scope.
Infix "+"  := LPRplus : LPR_scope.
Infix "*"  := LPRmult : LPR_scope.

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

Lemma LPRlt_not_le {x y : LPReal}
  : x < y -> ~ (y <= x).
Proof. intros. unfold LPRlt, LPRle, not in *.
intros. destruct H as [q [notxq yq]].
apply notxq. apply H0. assumption.
Qed.


Lemma LPRQnn_le {x y : Qnn} : LPRQnn x <= LPRQnn y <-> (x <= y)%Qnn.
Proof.
split; intros.
- unfold LPRle in H. simpl in *. destruct (Qnn_dec x y).
  destruct s. apply Qnnlt_le_weak. assumption.
  pose proof (H _ q). apply Qnnlt_not_le in H0.
  apply False_rect. apply H0. apply Qnnle_refl.
  induction e. apply Qnnle_refl.
- unfold LPRle. simpl in *. intros.
  eapply Qnnlt_le_trans. eassumption. assumption.
Qed.

Lemma LPRQnn_plus {x y : Qnn} 
  : LPRQnn x + LPRQnn y = LPRQnn (x + y)%Qnn.
Proof.
apply LPReq_compat. unfold LPReq.
split; unfold LPRle; intros; simpl in *.
- destruct H; simpl in *.
  + replace q with (0 + q)%Qnn by ring. 
    replace (x + y)%Qnn with (y + x)%Qnn by ring.
    apply Qnnplus_le_lt_compat. apply nonneg. assumption. 
  + replace q with (0 + q)%Qnn by ring. 
    apply Qnnplus_le_lt_compat. apply nonneg. assumption.
  + eapply Qnnle_lt_trans. eassumption.
    eapply Qnnplus_le_lt_compat. apply Qnnlt_le_weak. 
    assumption. assumption.
- destruct (Qnn_dec x 0%Qnn) as [[H0 | H0] | H0].
  + apply Qnnlt_zero_prop in H0. contradiction.
  + destruct (Qnn_dec y 0%Qnn) as [[H1 | H1] | H1].
    * apply Qnnlt_zero_prop in H1. contradiction.
    * pose (Qnnminusp _ _ (Qnnlt_le_weak H)).
      pose ((Qnnonehalf * Qnnonehalf * q0)%Qnn) as eps.
      admit.
    * apply LPRplusL. simpl.
      eapply Qnnlt_le_trans. eassumption.
      subst. replace (x + 0)%Qnn with x by ring.
      apply Qnnle_refl.
  + apply LPRplusR. simpl. eapply Qnnlt_le_trans.
    eassumption. subst. replace (0 + y)%Qnn with y by ring.
    apply Qnnle_refl.
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
intros. exists (q + 1)%Qnn. intuition.
replace q with (q + 0)%Qnn at 1 by ring.
apply Qnnplus_le_lt_compat.
apply Qnnle_refl. apply Qnnlt_alt. reflexivity. 
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

Lemma LPRsup_monotonic_gen {A B : Type} (f : A -> LPReal) (g : B -> LPReal)
  : (forall (a : A), exists (b : B), f a <= g b) -> LPRsup f <= LPRsup g.
Proof.
intros mono. unfold LPRle in *.
intros. simpl in *. destruct H. 
destruct (mono x).
exists x0. apply H0.  assumption.
Qed.

Lemma LPRsup_monotonic {A : Type} (f g : A -> LPReal)
  : (forall (a : A), f a <= g a) -> LPRsup f <= LPRsup g.
Proof. 
intros. apply LPRsup_monotonic_gen. intros. exists a. auto.
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
  : x <= z -> y <= z -> LPRmax x y <= z.
Proof. intros.
unfold LPRle; simpl in *; intros; intuition.
Qed.

Lemma LPRmax_le_or {x y z : LPReal} 
  : z <= x \/ z <= y -> z <= LPRmax x y.
Proof. intros.
unfold LPRle; simpl in *; intros; intuition.
Qed.

Lemma LPRmax_le {x y x' y' : LPReal} 
  : x <= x' -> y <= y' -> LPRmax x y <= LPRmax x' y'.
Proof.
intros. unfold LPRle. intros q Hmax. simpl in *.
destruct Hmax; [left | right].
- apply H. assumption.
- apply H0. assumption.
Qed.

Lemma LPRmax_plus {x x' y y' : LPReal}
  : LPRmax (x + x') (y + y') <= LPRmax x y + LPRmax x' y'.
Proof.
apply LPRmax_le_and; apply LPRplus_le_compat; apply LPRmax_le_or;
  (left; apply LPRle_refl) || (right; apply LPRle_refl).
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

(* An real number which is an indicator for a logical proposition.
   It is 0 if P is false and 1 if P is true. Without a proof or
   refutation of P, you will not know which! *)
Definition LPRindicator (P : Prop) : LPReal.
Proof. refine 
( {| lbound := fun q => P /\ (q < 1)%Qnn |}).
- intros. intuition. eapply Qnnle_lt_trans; eassumption. 
- intros. destruct H. pose proof (Qnnbetween q 1%Qnn H0).
  destruct H1. exists x. intuition.
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
apply Qnnmult_le_compat. apply Qnnlt_le_weak. assumption.
apply Qnnle_refl.
Qed.

Lemma qnn_sqrt {x : Qnn}
  : (x < 1)%Qnn -> exists y, (y < 1 /\ x <= y * y)%Qnn.
Proof.
Admitted.

Lemma LPRind_mult {U V : Prop}
  : LPRindicator (U /\ V) = LPRindicator U * LPRindicator V.
Proof.
apply LPReq_compat. 
split; unfold LPRle; simpl in *; intros.
- intuition. pose proof (qnn_sqrt H1). 
  destruct H0. exists x. exists x. intuition.
- destruct H as [a [b [pa [pb ab]]]]. intuition.
  eapply Qnnle_lt_trans. eassumption.
  apply Qnnle_lt_trans with (a * 1)%Qnn.
  apply Qnnmult_le_compat. apply Qnnle_refl.
  apply Qnnlt_le_weak. assumption. 
  replace 1%Qnn with (1 * 1)%Qnn at 2 by ring. 
  apply Qnnmult_lt_compat_r. apply Qnnlt_alt. reflexivity.
  assumption.
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
    apply Qnnplus_le_compat. apply Qnnle_refl. apply nonneg.
  + simpl in *. destruct H. destruct H. 
    * apply LPRplusL. simpl. intuition.
    * apply LPRplusR. simpl. intuition.
  + simpl in *. eapply LPRplusB; simpl in *; intuition.
    eapply H3. assumption. eapply H4. assumption. assumption.
    assumption.
Qed.

Lemma LPRplus_eq_compat : forall x y x' y',
  x = x' -> y = y' -> x + y = x' + y'.
Proof. intros. subst. reflexivity. Qed.

Lemma LPRmult_eq_compat : forall x y x' y',
  x = x' -> y = y' -> x * y = x' * y'.
Proof. intros. subst. reflexivity. Qed.

Lemma LPRQnn_eq {x y : Qnn} : x = y -> LPRQnn x = LPRQnn y.
Proof. intros; subst; reflexivity. Qed.

Lemma LPRmax_scales {c x y : LPReal} 
  : LPRmax (c * x) (c * y) = c * LPRmax x y.
Proof. 
apply LPReq_compat. split.
- apply LPRmax_le_and; (apply LPRmult_le_compat;
  [ apply LPRle_refl 
  | apply LPRmax_le_or; auto using LPRle_refl]).
- unfold LPRle; simpl; intros. 
  destruct H as [a [b [ca [xyb qab]]]].
  destruct xyb; [left | right];
  exists a; exists b; auto.
Qed.

Lemma LPRsup_scales {A : Type} {f : A -> LPReal}
  {c : LPReal}
  : c * LPRsup f = LPRsup (fun x => c * f x).
Proof.
apply LPReq_compat; split.
- unfold LPRle; simpl; intros.
  destruct H as [a [b [ca [sup qab]]]].
  destruct sup. exists x. exists a. exists b. intuition.
- apply LPRsup_le. intros. apply LPRmult_le_compat.
  apply LPRle_refl. apply LPRsup_ge.
Qed.

Lemma LPRsup_constant {A : Type} (x : LPReal) :
  A -> LPRsup (fun _ : A => x) = x.
Proof.
intros. apply LPReq_compat; split; unfold LPRsup, LPRle; simpl; intros.
destruct H. assumption. exists X. assumption. 
Qed.

Lemma smallPowers {p : Qnn} : (p < 1)%Qnn
  -> forall (q : Qnn), (q > 0)%Qnn 
  -> exists (n : nat), (p ^ n < q)%Qnn.
Admitted.

Lemma Qnnpowsup {p : Qnn} (plt1 : (p < 1)%Qnn)
  : LPRsup (fun n => LPRQnn (1 - (p ^ n)))%Qnn = 1.
Proof.
apply LPReq_compat. split.
- replace 1 with (LPRsup (fun _ : nat => 1)).
  apply LPRsup_monotonic. intros n.
  induction n; simpl.
   + unfold LPRle. simpl. intros. 
     apply Qnnminus_lt_r in H; [|apply Qnnle_refl].
     eapply Qnnle_lt_trans; [| eassumption].
     replace q with (0 + q)%Qnn at 1 by ring. apply Qnnplus_le_compat.
     apply nonneg. apply Qnnle_refl. 
   + unfold LPRle. simpl. intros. 
     apply LPRQnn_le in IHn. apply Qnnminus_lt_r in H.
     eapply Qnnle_lt_trans. Focus 2. apply H.
     replace q with (0 + q)%Qnn at 1 by ring.
     apply Qnnplus_le_compat. apply nonneg. apply Qnnle_refl.
     pose proof (Qnnpow_le (Qnnlt_le_weak plt1) (n := S n)) as pn1.
     apply pn1.
   + apply LPRsup_constant. exact 0%nat.
- unfold LPRle; simpl; intros.
  pose proof (Qnnlt_le_weak H) as Hle.
  pose proof (smallPowers plt1 (1 - q)%Qnn).
  destruct (Qnn_dec q 0%Qnn).
  destruct s. apply Qnnlt_zero_prop in q0. contradiction.
  assert (1 - q > 0)%Qnn.
  apply Qnnminus_lt_r. assumption. 
  replace (q + 0)%Qnn with q by ring. assumption. 
  apply H0 in H1. destruct H1. exists x. apply Qnnminus_lt_r.
  apply Qnnpow_le. apply Qnnlt_le_weak. assumption.
  apply Qnnminus_lt_r in H1. rewrite (SRadd_comm Qnnsrt).
  assumption. assumption. subst. exists 1%nat. simpl. apply Qnnminus_lt_r.
  replace (p * 1)%Qnn with p by ring. apply Qnnlt_le_weak.
  assumption.
  replace (p * 1 + 0)%Qnn with p by ring. assumption.
Qed.


Lemma LPRQnn_mult {x y : Qnn} : LPRQnn x * LPRQnn y = LPRQnn (x * y)%Qnn.
Proof. 
Admitted.