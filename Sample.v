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

(** An n-fold IID product of a given measure. *)
Fixpoint product_n {A : Type} (v : Valuation A)
  (n : nat) : Valuation (Vector.t A n) := match n with
  | 0 => unit (Vector.nil A)
  | S n' => bind v (fun x => map (Vector.cons A x n') (product_n v n'))
  end.

Fixpoint product_n2 {A : Type} (v : Valuation A)
  (n : nat) {struct n} : Valuation (Vector.t A n) := match n with
  | 0 => unit (Vector.nil A)
  | S n' => bind (product_n v n') (fun xs => map (fun x => Vector.shiftin x xs) v)
  end.

Lemma commute_cons_shiftin {A : Type} {n : nat}
  : forall {xs : Vector.t A n} {a z : A},
    Vector.cons A a _ (Vector.shiftin z xs)
  = Vector.shiftin z (Vector.cons A a _ xs).
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
rewrite IHn.
Abort.

Require Streams.

Fixpoint take_n {A : Type} (s : Streams.Stream A) (n : nat)
  : Vector.t A n := match n, s with
  | 0, _ => Vector.nil A
  | S n', Streams.Cons x xs => Vector.cons A x n' (take_n xs n')
end.

(* Restrict a property of streams to a property of vectors of length n.
   The property is true for a vector of length in if the property is
   true for ALL streams which begin with that finite prefix. *)
Definition restrictToVec {A : Type} (P : Streams.Stream A -> Prop)
  (n : nat) (x : Vector.t A n) : Prop :=
  forall (s : Streams.Stream A), take_n s n = x -> P s.

Lemma restrictToVecBot {A : Type} {n : nat}
  (nonempty : (A -> False) -> False)
  : forall xs, ~ (@restrictToVec A (K False) n xs).
Proof. Admitted.

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
  (vIsProb : v (K True) = 1)
  : Valuation (Streams.Stream A).
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
  eapply valPosNonEmpty.
  unfold LPRgt. unfold LPRlt. exists 0%Qnn. split.
  unfold not. simpl. apply Qnnlt_zero_prop.
  instantiate (1 := (K True)).
  instantiate (1 := v).
  rewrite vIsProb. simpl. apply Qnnlt_alt. apply eq_refl.
- apply LPRsup_monotonic.
  intros n. induction n; simpl.
  + apply LPRind_imp.
    unfold restrictToVec. intros H1.
    intros. apply H. apply H1. apply H0.
  + apply int_monotonic. unfold pointwise.
    intros a. apply monotonic. intros.
    eapply restrictToVecMonotonicP. eassumption.
    assumption.
- do 2 (rewrite <- LPRsup_nat_ord; 
  try (apply restrictToVecMonotonicN);
  try assumption).
  (* apply modular. *)
  admit.
Defined.

Lemma streamTl {A : Type} (mu : Valuation A)
  (mu1 : mu (K True) = 1)
  : map (@Streams.tl A) (inf_product mu mu1) = 
    inf_product mu mu1.
Proof.
apply Valeq_compat. unfold Valeq. intros P.
simpl. apply LPReq_compat. 
split; apply LPRsup_le; intros n;
apply LPRsup_ge2. 
- exists (S n). simpl.
  erewrite fubini_no_funext.
    Focus 2. intros. rewrite <- int_indicator. reflexivity. 
    Focus 2. intros. reflexivity.
    Focus 2. intros. simpl. reflexivity.
  erewrite int_pointwise_eq.
    Focus 2. unfold pointwise; intros.
    rewrite int_indicator. reflexivity.
  (*
  apply monotonic.
  apply int_monotonic. unfold pointwise. 
  intros xs. rewrite int_indicator.
*)
admit.
- exists (S n). simpl. admit.
Qed.

Definition streamSampler {A : Type} (mu : Valuation A)
  (mu1 : mu (K True) = 1)
  : Sampler (inf_product mu mu1) mu.
Proof. refine (
  {| sample := fun r => match r with
     | Streams.Cons a r' => (r', a)
     end
  |}
). apply Valeq_compat. unfold Valeq. intros P.
Abort.



(** This is clearly wrong; this is just the zero measure. I even
    prove my wrongness a little bit further down. *)
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

Definition inf_product' {A : Type} (v : Valuation A)
  : Valuation (Streams.Stream A)
  := fixValuation (inf_productFunc v) (inf_productFunc_mono v).

Lemma inf_product'_wrong {A : Type} (v : Valuation A)
  : inf_product' v = zeroVal.
Proof.
apply Valeq_compat. unfold Valeq. intros P.
simpl. apply LPReq_compat. split.
apply LPRsup_le. intros n. generalize dependent P. induction n; intros.
simpl. apply LPRle_refl. simpl.
rewrite <- strict with v.
rewrite <- int_indicator. apply int_monotonic.
unfold pointwise. unfold K.
rewrite LPRind_false by intuition.
intros a. apply IHn. apply LPRzero_min.
Qed.


(** A datatype for partial computations. We will use this
    to allow definitions of measures which might not be guaranteed
    to terminate. For example, consider the geometric distribution,
    where we might worry that we keep getting "heads". *)
CoInductive Partial {A : Type} : Type :=
 | Now : A -> Partial
 | Later : Partial -> Partial.

(** We can use this to loop. *)
CoFixpoint loop {A : Type} := @Later A loop.

Arguments Partial : clear implicits.

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
    in forall mu1 mu2, Valle mu1 mu2 -> Valle (f mu1) (f mu2).
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