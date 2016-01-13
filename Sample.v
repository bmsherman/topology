Require Import Qnn LPReal Valuation.

Require Import FunctionalExtensionality.

Local Open Scope LPR.

(** A data type for random samplers. [R] is the type of the random seed,
    and [A] is the type for which values are sampled. Our correctness property
    says that if we are given a seed which comes from the distribution [random]
    and then apply the sampling function [sample], the result is distributed as
    a new random seed distributed as [random] and a value of [A] distributed
    according to the measure [mu], and these two results are independent. *)
Record Sampler {R A : Type} (random : Valuation R) (mu : Valuation A)
  : Type :=
  { sample     :> R -> R * A
  ; sample_ind :  map sample random = product random mu
  }.

(** Samplers, too, form a monad, and here's the (very boring) unit. *)
Definition sunit {R A : Type} (random : Valuation R)
  (a : A) : Sampler random (unit a).
Proof. refine (
  {| sample := fun r => (r, a) |}
).
apply Valeq_compat. unfold Valeq. intros. simpl.
rewrite <- int_indicator. apply int_pointwise_eq.
unfold pointwise. intros r.
reflexivity.
Defined.

(** If we believe the statement of Fubini's theorem above, then
    we have a bind operation on random samplers! *)
Definition sbind {R A B : Type} (random : Valuation R)
  (mu : Valuation A) (smu : Sampler random mu) 
  (f : A -> Valuation B) (sf : forall a, Sampler random (f a))
  : Sampler random (bind mu f).
Proof. 
pose (func := fun p : (R * A) => sf (snd p) (fst p)).
refine (
  {| sample := fun r => func (smu r) |}
).
rewrite map_compose.
rewrite (sample_ind _ _ smu).
apply Valeq_compat. unfold Valeq. intros. simpl.

erewrite fubini_no_funext.
Focus 2. intros. rewrite <- int_indicator. reflexivity.
Focus 3. intros. simpl. reflexivity.
Focus 2. intros. reflexivity.

pose (func2 := fun p => (f (snd p)) (fun b => P (fst p, b))).
assert (
 (fun x : R =>
      integral (fun x0 : A => (f x0) (fun x1 : B => P (x, x1))) mu)
 = 
 (fun x : R =>
      integral (fun x0 : A => func2 (x, x0)) mu)
).
extensionality r.
reflexivity. rewrite H. clear H. 
rewrite fubini.
apply int_pointwise_eq. unfold pointwise. intros a.
pose proof (sample_ind _ _ (sf a)).
unfold func2. simpl.
assert (forall P, (map (sf a) random) P = (product random (f a)) P).
intros. rewrite H. reflexivity.
simpl in H0.
rewrite int_indicator. apply H0.
Defined.

(** * Streams *)

Require Vector.
Module V := Vector.

(** An n-fold IID product of a given measure. *)
Fixpoint product_n {A : Type} (v : Valuation A)
  (n : nat) : Valuation (Vector.t A n) := match n with
  | 0 => unit (V.nil A)
  | S n' => bind v (fun x => map (V.cons A x n') (product_n v n'))
  end.

Fixpoint product_n2 {A : Type} (v : Valuation A)
  (n : nat) {struct n} : Valuation (Vector.t A n) := match n with
  | 0 => unit (V.nil A)
  | S n' => bind (product_n2 v n') (fun xs => map (fun x => V.shiftin x xs) v)
  end.

Lemma commute_cons_shiftin {A : Type} {n : nat}
  : forall {xs : Vector.t A n} {a z : A},
    V.cons A a _ (V.shiftin z xs)
  = V.shiftin z (V.cons A a _ xs).
Proof.
destruct n; reflexivity.
Qed.

Theorem product_n_same {A : Type} {v : Valuation A}
  {n : nat}
  : product_n v n = product_n2 v n.
Proof.
induction n; apply Valeq_compat; unfold Valeq; intros.
- simpl. reflexivity. 
- simpl.
assert (
    (fun x : A =>
      (product_n v n) (fun x0 : Vector.t A n => P (Vector.cons A x n x0)))
=
    (fun x : A =>
      (product_n2 v n) (fun x0 : Vector.t A n => P (Vector.cons A x n x0)))
).
apply functional_extensionality. intros. rewrite IHn. reflexivity.
rewrite H. clear H.
Admitted.

Require Streams.

Module S := Streams.

(* Restrict a property of streams to a property of vectors of length n.
   The property is true for a vector of length in if the property is
   true for ALL streams which begin with that finite prefix. *)
Fixpoint restrictToVec {A : Type} (P : S.Stream A -> Prop)
  (n : nat) (prefix : Vector.t A n) : Prop :=
 (match n as n' return Vector.t A n' -> Prop with
  | 0 => fun _ => forall (s : S.Stream A), P s
  | S n' => fun v => match v with
    | V.cons x n0 xs => restrictToVec (fun s => P (S.Cons x s)) n0 xs
    | V.nil => False
    end
  end) prefix.

Lemma restrictToVecBot {A : Type} {n : nat}
  (nonempty : A)
  : forall xs, ~ (@restrictToVec A (K False) n xs).
Proof.
intros. induction xs; simpl; unfold not, K; intros.
- apply H. exact (S.const nonempty).
- apply IHxs. apply H.
Qed.

Lemma restrictToVecFactorizes {A : Type} : 
  A ->
  forall U P n v,
  @restrictToVec A (fun z => P /\ U z) n v
  <-> P /\ @restrictToVec A U n v.
Proof.
intros. generalize dependent U.
induction v; simpl.
- split; intros. pose proof (H (S.const X)).
  destruct H0. split. assumption. intros.
  destruct (H s). assumption. destruct H. split.
  assumption. apply H0.
- intros U. apply (IHv (fun s => U (S.Cons h s))).
Qed.

Lemma restrictToVecMonotonicP {A : Type} {n : nat}
  : forall { U V : S.Stream A -> Prop }
  , (forall (s : S.Stream A), U s -> V s)
  -> forall (xs : Vector.t A n), restrictToVec U n xs -> restrictToVec V n xs.
Proof.
intros. generalize dependent V. generalize dependent U.
induction xs; simpl in *.
- intros. apply H. apply H0.
- intros. eapply IHxs. eassumption.
  intros. apply H. apply H1.
Qed.

Lemma restrictToVecShiftin {A : Type} : forall U n a (z : A),
    restrictToVec U n a
  -> restrictToVec U (S n) (V.shiftin z a).
Proof.
intros. generalize dependent U. induction a.
- simpl in *. intros. apply H.
- intros. rewrite <- commute_cons_shiftin.
  apply IHa. apply H.
Qed.

Lemma restrictToVecMonotonicN {A : Type} : 
 forall (v : Valuation A) (U : Streams.Stream A -> Prop),
 v (K True) = 1 ->
 forall n : nat,
 (product_n v n) (restrictToVec U n) <=
 (product_n v (S n)) (restrictToVec U (S n)).
Proof. 
intros. rewrite (@product_n_same _ v (S n)).
simpl. rewrite <- product_n_same.
rewrite <- int_indicator. apply int_monotonic.
unfold pointwise. intros.
replace (LPRindicator _)  with (LPRindicator (restrictToVec U n a) * 1)
  by ring.
rewrite <- H. rewrite <- factorizes. 
apply monotonic. unfold K. intros.
destruct H0.
apply restrictToVecShiftin. assumption.
Qed.

Lemma restrictToVecMonotonicN' {A : Type} : 
 forall (v : Valuation A) (U : Streams.Stream A -> Prop),
 v (K True) = 1 ->
 forall m n : nat, (m <= n)%nat ->
 (product_n v m) (restrictToVec U m) <=
 (product_n v n) (restrictToVec U n).
Proof. 
intros. induction H0. apply LPRle_refl.
eapply LPRle_trans. apply IHle. apply restrictToVecMonotonicN.
assumption.
Qed.

Lemma valPosNonEmpty {A : Type} {mu : Valuation A}
  (P : A -> Prop) (pos : mu P > 0)
  : ((A -> False) -> False).
Proof.
intros. 
pose proof (strict mu).
rewrite <- H0 in pos.
assert (~ (forall x, P x = (K False) x)).
unfold not. intros.
apply functional_extensionality in H1.
rewrite H1 in pos. 
unfold LPRgt in pos. unfold LPRlt in pos.
destruct pos. destruct H2. apply H2 in H3.
assumption.
apply H1. intros. apply False_rect. apply H. assumption.
Qed.

(* An infinite product measure, generated by considering finite
   products and taking the limit. *)
Theorem inf_product {A : Type} (v : Valuation A)
  (vIsProb : v (K True) = 1) (nonempty : A)
  : Valuation (S.Stream A).
Proof.
refine (
  {| val := fun P => LPRsup (fun n => (product_n v n) (restrictToVec P n))
  |}
); intros.
- apply LPReq_compat. split; [| apply LPRzero_min].
  unfold LPRle. simpl. intros. destruct H.
  apply (monotonic _ _ (K False)) in H.
  rewrite (strict (product_n v x)) in H.
  simpl in H. assumption.
  apply restrictToVecBot.
  apply nonempty.
- apply LPRsup_monotonic.
  intros. apply monotonic. apply restrictToVecMonotonicP. assumption.
- do 2 (rewrite <- LPRsup_nat_ord; 
  try (apply restrictToVecMonotonicN');
  try assumption).
  (* This is definitely not the case pointwise (check n = 0). 
     It seems that for this to be the case, we must need U and V to
     be open sets! This will have to reduce to a Tychonoff-like thing;
     apparently infinite product measures are not exactly trivial. 
  *)
  admit. 
- rewrite LPRsup_scales.
  apply LPRsup_eq_pointwise.
  intros. rewrite (val_iff (restrictToVecFactorizes nonempty _ _ _)).
  apply factorizes.
Defined.

Lemma streamTl {A : Type} (mu : Valuation A)
  (nonempty : A)
  (mu1 : mu (K True) = 1)
  : map (@Streams.tl A) (inf_product mu mu1 nonempty) = 
    inf_product mu mu1 nonempty.
Proof.
(* This proof can almost definitely be cleaned up and made shorter! *)
apply Valeq_compat. unfold Valeq. intros P.
simpl. apply LPReq_compat. 
split; apply LPRsup_le; intros n;
apply LPRsup_ge2.
- induction n.
  + simpl. exists 0%nat. simpl. apply LPRind_imp; intros.
    apply (H (S.Cons nonempty s)).
  + destruct IHn. simpl.
    erewrite int_pointwise_eq.
    Focus 2. unfold pointwise. intros.
    rewrite <- (SRmul_1_l LPRsrt) at 1.
    rewrite (SRmul_comm LPRsrt).
    rewrite <- (LPRind_true True) by trivial.  reflexivity. 
    exists n. rewrite <- int_scales.
    rewrite int_indicator. unfold K in mu1. rewrite mu1.
    ring_simplify. apply monotonic. trivial.
- exists (S n). simpl.
    erewrite int_pointwise_eq.
    Focus 2. unfold pointwise. intros.
    rewrite <- (SRmul_1_l LPRsrt) at 1.
    rewrite (SRmul_comm LPRsrt).
    rewrite <- (LPRind_true True) by trivial.  reflexivity. 
    rewrite <- int_scales. rewrite int_indicator. unfold K in mu1.
    rewrite mu1. ring_simplify. apply LPRle_refl.
Qed.

(** The truthiness of this axiom is very much up to debate.
    Probably, it's not true in general. Oh, well, right now
    foundations are out the window anyway. *)
Axiom product_char : forall (A B : Type) (mu nu : Valuation (A * B)),
  (forall (PA : A -> Prop) (PB : B -> Prop), 
     let P (p : A * B) := let (x, y) := p in PA x /\ PB y in
     mu P = nu P)
  -> mu = nu.

Definition streamSampler {A : Type} (mu : Valuation A)
  (nonempty : A)
  (mu1 : mu (K True) = 1)
  : Sampler (inf_product mu mu1 nonempty) mu.
Proof. refine (
  {| sample := fun r => match r with
     | Streams.Cons a r' => (r', a)
     end
  |}
).
apply product_char.
intros.
remember (inf_product mu mu1 nonempty) as infp.
unfold P. simpl.
erewrite int_pointwise_eq.
Focus 2. unfold pointwise. intros. rewrite factorizes.
rewrite (SRmul_comm LPRsrt).
reflexivity.
rewrite <- int_scales. rewrite int_indicator.
erewrite val_iff.
Focus 2. intros. 
instantiate (1 := fun s => PA (S.tl s) /\ PB (S.hd s)).
simpl. destruct a. intuition.
rewrite Heqinfp at 1. simpl.
Admitted.

(** * Partial valuations *)

(** A datatype for partial computations. We will use this
    to allow definitions of measures which might not be guaranteed
    to terminate. For example, consider the geometric distribution,
    where we might worry that we keep getting "heads". *)
CoInductive Partial {A : Type} : Type :=
 | Now : A -> Partial
 | Later : Partial -> Partial.

Arguments Partial : clear implicits.

(** We can use this to loop. *)
CoFixpoint loop {A : Type} := @Later A loop.

Definition unfold_Partial {A : Type} : forall (px : Partial A),
  px = match px with
      | Now x => Now x
      | Later px' => Later px'
      end.
Proof. destruct px; reflexivity. Qed.


(** Run a partial computation for n steps, returning the value if
    we got a value in that many steps or fewer. *)
Fixpoint runPartial {A : Type} (px : Partial A)
  (n : nat) : option A := match px with
  | Now x => Some x
  | Later px' => match n with
    | 0 => None
    | S n' => runPartial px n'
    end 
  end.

(** Transform a property of values of A to a property of 
    partial computations which may return an A, where the new 
    property is true only if the computation indeed eventually 
    returns a value for which the original property was true. *)
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
  : forall a, (partialize (fun z => U z /\ V z)) a
  <-> (fun z => partialize U z /\ partialize V z) a.
Proof. intros; split; intros;
unfold partialize in *. destruct H.
split; exists x; destruct (runPartial a x); intuition.
destruct H. destruct H. destruct H0.
exists (max x x0). destruct (runPartial a x) eqn:p0;
  destruct (runPartial a x0) eqn:p1; try contradiction.
  apply partial_mono with (n := max x x0) in p0.
  apply partial_mono with (n := max x x0) in p1.
  rewrite p0 in p1. injection p1. intros. subst.
  rewrite p0. split; assumption.
  apply Max.le_max_r. apply Max.le_max_l.
Qed.

Lemma partialize_or {A : Type} {U V : A -> Prop}
  : forall a, (partialize (fun z => U z \/ V z)) a
  <-> (fun z => partialize U z \/ partialize V z) a.
Proof. intros. split; intros;
unfold partialize in *. destruct H.
destruct (runPartial a x) eqn:partial.
destruct H; [left | right]; exists x;
rewrite partial; assumption. contradiction.
destruct H; destruct H; exists x;
destruct (runPartial a x) eqn:partial; intuition.
Qed.

Lemma partialize_factorizes {A : Type}
  : forall {P U} a, (partialize (fun z : A => P /\ U z)) a
       <-> P /\ partialize U a.
Proof.
intros. split; intros.
destruct H. destruct (runPartial a x) eqn:ran. destruct H.
split. assumption. exists x. rewrite ran. assumption. contradiction.
destruct H. destruct H0. destruct (runPartial a x) eqn:ran.
exists x. rewrite ran. intuition. contradiction.
Qed.

(** We can convert a measure on [Partial A]s to a measure on 
    [A]s by essentially just setting measure 0 to any of the
    values which never terminated. *)
Definition partialValuation {A : Type}
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
- intros. rewrite (val_iff partialize_and). 
  rewrite (val_iff partialize_or).
  apply modular.
- intros. rewrite (val_iff partialize_factorizes).
  apply factorizes.
Defined.

(** Random samplers which may diverge. *)
Record PSampler {R A : Type} (random : Valuation R) (mu : Valuation A)
  : Type :=
  { psample     :> R -> Partial (R * A)
  ; psample_ind :  partialValuation (map psample random) = product random mu
  }.

Lemma partialValNow {A : Type} (mu : Valuation A)
  : partialValuation (map Now mu) = mu.
Proof.
apply Valeq_compat. unfold Valeq; intros.
simpl.
apply val_iff.
intros. split; intros. unfold partialize in H.
destruct H. rewrite partial_now in H. assumption.
unfold partialize. exists 0%nat. simpl. assumption.
Qed.

(** Any total sampler can be considered as a partial sampler. *)
Definition partializeSampler {R A : Type}
  {random : Valuation R} {mu : Valuation A} (f : Sampler random mu)
  : PSampler random mu.
Proof.
refine (
  {| psample := fun r => Now (f r) |}
).
rewrite map_compose. rewrite (sample_ind _ _ f).
apply partialValNow.
Defined.

Lemma partialLoop {A : Type} : forall n, runPartial loop n = (@None A).
intros. induction n. simpl. reflexivity.
simpl. apply IHn.
Qed.

Definition zeroPSampler {R A : Type}
  {random : Valuation R}
  : PSampler random (@zeroVal A).
Proof. refine (
  {| psample := fun r => loop |}
).
apply Valeq_compat. unfold Valeq. intros P.
simpl. rewrite <- (LPRind_false False) by auto.
rewrite int_indicator.
apply val_iff. 
intros. split; intros.
unfold partialize in H. destruct H. rewrite partialLoop in H.
assumption. contradiction.
Defined.

(** * Rejection sampling *)

(** The functional which corresponds to rejection sampling. *)
Definition rejectionFunc {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (f : Valuation A) : Valuation A :=
  bind v (fun a => if pred a
    then unit a
    else f).

(** This functional is indeed monotonic. *)
Lemma rejectionFunc_mono {A : Type} (v : Valuation A)
  (pred : A -> bool)
  : let f := rejectionFunc v pred 
    in forall mu1 mu2, (mu1 <= mu2 -> f mu1 <= f mu2)%Val.
Proof. 
intros. unfold Valle in *. intros P. simpl.
apply int_monotonic. unfold pointwise. intros a.
destruct (pred a). apply LPRle_refl. apply H.
Qed.

(** Modify a measure by rejection sampling. *)
Definition rejection {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  : Valuation A
  := fixValuation (rejectionFunc v pred)
     (rejectionFunc_mono v pred).

Lemma restrict_integral : forall (A : Type) (mu : Valuation A) (P : A -> Prop)
  (f : A -> LPReal),
    integral f (restrict mu P) 
  = integral (fun x => LPRindicator (P x) * f x) mu.
Proof.
Admitted.

Lemma int_ifthen : forall A (pred : A -> bool) (f fthen felse : A -> LPReal)
  (mu : Valuation A), 
  (forall x, f x = if pred x then fthen x else felse x)
  -> integral f mu
  = integral fthen (restrict mu (fun x => pred x = true))
  + integral felse (restrict mu (fun x => pred x = false)).
Proof.
intros.
pose proof (@val_destruct_dec A mu (fun x => pred x = true)).
erewrite int_pointwise_eq. 2: unfold pointwise; apply H.
rewrite <- H0 at 1.
simpl. unfold val_destruct. 
replace (fun a : A => pred a <> true) with (fun a : A => pred a = false).
rewrite int_adds_val.
repeat rewrite restrict_integral.
Admitted.

Definition rejection_Prob_lemmaT {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (vProb : v (K True) = 1)
  (p : Qnn)
  (ple1 : (p <= 1)%Qnn)
  (predPos : v (fun x => pred x = true) p)
  (n : nat) :
   (LPRQnn (1 - (p ^ n))%Qnn) <= (fixn (rejectionFunc v pred) n) (K True).
Proof.
pose proof (fun n => Qnnpow_le ple1 (n := n)).
induction n. 
- simpl. apply LPRQnn_le. apply Qnnminus_le.
  apply Qnnle_refl.
  replace (1 + 0)%Qnn with 1%Qnn by ring.
  apply Qnnle_refl.
-  simpl. 
   erewrite (@int_ifthen _ pred _).
   Focus 2. intros. destruct (pred x); reflexivity.
   erewrite int_pointwise_eq.
   Focus 2. unfold pointwise. intros. rewrite unit_prob. 
   rewrite <- (LPRind_true True) by trivial. reflexivity.
   rewrite int_indicator.
   erewrite int_pointwise_eq.
   Focus 2. unfold pointwise. intros.
   rewrite <- (SRmul_1_l LPRsrt) at 1.
   rewrite (SRmul_comm LPRsrt). rewrite <- (LPRind_true True) by trivial.
   reflexivity.
   rewrite <- int_scales, int_indicator.
   replace (1 - p * p ^ n)%Qnn with
     ((p ^ n * (1 - p)) + (1 - p ^ n))%Qnn.
   rewrite <- (SRadd_0_l LPRsrt) at 1.
   rewrite (SRadd_comm LPRsrt).

   eapply LPRle_trans. Focus 2. eapply LPRplus_le_compat.
   simpl. rewrite (@val_iff _ _ _ (fun a => pred a = true))
     by intuition. instantiate (1 := LPRQnn p). unfold LPRle. 
   intros. simpl in H0. eapply dclosed. eassumption. 
   apply Qnnlt_le_weak. assumption.
   eapply LPRmult_le_compat. apply IHn. simpl.
   rewrite (@val_iff _ _ _ (fun a => pred a = false)) by intuition.
   apply LPRle_refl.
   
Admitted. 


(** Rejection sampling gives a probability distribution if the
    predicate has a positive probability of occurence. *)
Definition rejection_Prob {A : Type} (v : Valuation A)
  (pred : A -> bool) 
  (vProb : v (K True) = 1)
  (predPos : v (fun x => pred x = true) > 0)
  : (rejection v pred) (K True) = 1.
Proof.
apply LPReq_compat. split.
- apply fixValuation_subProb. intros. unfold rejectionFunc.
  simpl. rewrite <- vProb. rewrite <- int_indicator.
  apply int_monotonic. unfold pointwise. unfold K.
  intros. destruct (pred a). simpl.
  apply LPRind_imp. trivial.
  rewrite LPRind_true by trivial. apply H.
- unfold LPRgt, LPRlt in predPos. destruct predPos.
  destruct H. 
  assert ((v (fun x0 : A => pred x0 = true)) <= 1).
  rewrite <- vProb.  apply monotonic. unfold K. intuition.
  assert (x < 1)%Qnn. unfold LPRle in H1. simpl in H1.
  apply H1. assumption.
  pose proof (Qnnpowsup H2).
  simpl. rewrite <- H3.
  apply LPRsup_monotonic.
  intros n.
  apply rejection_Prob_lemmaT. assumption.
  apply Qnnlt_le_weak. assumption. assumption.
Qed.

Record SemiDec {P : Prop} :=
  { decide : nat -> option P
  ; decide_ok : P -> exists n p, decide n = Some p }.

Arguments SemiDec : clear implicits.

Definition SDeventually : forall s : nat -> bool,
  SemiDec (exists k, s k = true).
Proof.
intros. 
refine ( {| decide := fun n =>
  match s n as vl return s n = vl -> option (exists k, s k = true) with
  | true => fun prf => Some (ex_intro (fun x => s x = true) n prf) 
  | false => fun _ => None
  end eq_refl |}).
intros. destruct H.
exists x. eexists. 
Abort.

Record CSemiDec {P : Prop} :=
  { cdecide : nat -> option (~P)
  ; cdecide_ok : (forall n, cdecide n = None) -> P }.

Arguments CSemiDec : clear implicits.