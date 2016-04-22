Require Import Qnn LPReal.
Require Import FunctionalExtensionality.

Local Open Scope Qnn.
Local Open Scope LPR.

(** * Valuations *)

(** constant function *)
Definition K {A} (x : A) {B} (y : B) := x.

(** Here's the analogy:
  Valuation : Measure :: constructive logic : classical logic

A good reference:

Claire Jones. Probabilistic Nondeterminism. 1990. Phd Thesis.
https://www.era.lib.ed.ac.uk/handle/1842/413
*)

Record Valuation {A : Type} :=
  { val :> (A -> Prop) -> LPReal
  ; strict : val (K False) = 0
  ; monotonic : forall (U V : A -> Prop), (forall z, U z -> V z)
              -> val U <= val V
  ; modular : forall {U V},
     val U + val V = val (fun z => U z /\ V z) + val (fun z => U z \/ V z)
  ; factorizes : forall {U : A -> Prop} {P : Prop},
     val (fun z => P /\ U z) = LPRindicator P * val U
  }.

Arguments Valuation : clear implicits.

Definition Valle {A : Type} (val1 val2 : Valuation A) : Prop :=
  forall (P : A -> Prop), val1 P <= val2 P.

Lemma Valle_refl {A : Type} (val : Valuation A) : Valle val val.
Proof. unfold Valle. intros. reflexivity. Qed.

Lemma Valle_trans {A : Type} (x y z : Valuation A)
  : Valle x y -> Valle y z -> Valle x z.
Proof. intros. unfold Valle in *. intros P. rewrite H, H0.
reflexivity.
Qed.

Definition Valeq {A : Type} (val1 val2 : Valuation A) : Prop :=
  forall (P : A -> Prop), val1 P = val2 P.

Require Import ProofIrrelevance.

Lemma Valeq_compat { A : Type }
  : forall (mu nu : Valuation A), Valeq mu nu -> mu = nu. 
Proof.
intros.
unfold Valeq in *.
destruct mu, nu. simpl in *.
assert (val0 = val1).
apply functional_extensionality. assumption.
induction H0.
pose proof (proof_irrelevance _ strict0 strict1).
induction H0.
pose proof (proof_irrelevance _ monotonic0 monotonic1).
induction H0.
pose proof (proof_irrelevance _ modular0 modular1).
induction H0.
pose proof (proof_irrelevance _ factorizes0 factorizes1).
induction H0.
reflexivity.
Qed.

Definition Valge {A : Type} (x y : Valuation A)
  := Valle x y.


(** The valuation which is 0 everywhere *)
Definition zeroVal {A : Type} : Valuation A.
Proof. refine (
  {| val := fun P => 0 |}
); intros; try reflexivity.
- abstract ring.
Defined.

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 = (andLq + orLq) + (andRq + orRq).
Proof. intros. ring. Qed.

(** The sum of two valuations *)
Definition add {A : Type} (ValL ValR : Valuation A) : Valuation A.
Proof. refine (
  {| val := fun P => ValL P + ValR P |}
); intros.
- abstract (repeat rewrite strict; ring).
- abstract (apply LPRplus_le_compat; apply monotonic; assumption).
- abstract (
  rewrite qredistribute;
  rewrite (qredistribute (ValL (fun z => U z /\ V z)));
  apply LPRplus_eq_compat; apply modular).
- abstract (repeat rewrite factorizes; ring).
Defined.

(** Scale a valuation by a constant *)
Definition scale {A : Type} (c : LPReal) 
  (Val : Valuation A) : Valuation A.
Proof. refine (
  {| val := fun P => c * Val P |}
); intros.
- abstract (rewrite strict; ring).
- abstract (apply LPRmult_le_compat; 
  [ reflexivity
  | apply monotonic; assumption]).
- abstract (
  replace (c * Val U + c * Val V) with (c * (Val U + Val V)) by ring;
  replace (c * Val _ + c * Val _) 
  with (c * (Val (fun z : A => U z /\ V z) + Val (fun z : A => U z \/ V z))) by ring;
  apply LPRmult_eq_compat;
  [ reflexivity | apply modular ]).
- abstract (rewrite factorizes; ring).
Defined.

Infix "<=" := Valle : Val_scope.
Infix ">=" := Valge : Val_scope.
Infix "==" := Valeq : Val_scope.
Infix "+" := add : Val_scope.
Infix "*" := scale : Val_scope.

Notation "'0'" := zeroVal : Val_scope.

Delimit Scope Val_scope with Val.

Lemma Valle_antisym {A : Type} (x y : Valuation A)
  : (x <= y -> y <= x -> x = y)%Val.
Proof. intros. apply Valeq_compat. unfold Valle, Valeq in *. intros.
apply LPRle_antisym. apply H. apply H0.
Qed.

Lemma Valplus_comm {A : Type} : forall {x y : Valuation A}
  , (x + y = y + x)%Val.
Proof.
intros. apply Valeq_compat.
unfold Valeq. intros. simpl. ring.
Qed.


Lemma Valzero_min {A : Type} : forall v : Valuation A, (0 <= v)%Val.
Proof. intros. unfold Valle. intros. simpl. apply LPRzero_min. Qed.

Lemma val_iff {A : Type} {mu : Valuation A}
  {P Q : A -> Prop} : (forall a, P a <-> Q a) -> mu P = mu Q.
Proof.
intros. apply LPReq_compat. split; apply monotonic; apply H.
Qed.

(** The equivalent of a Dirac delta for a given point.
    Called `unit` because Valuations form a monad, and
    this is the unit. *)
Definition unit {A : Type} (a : A) : Valuation A.
Proof. refine (
 {| val := fun P => LPRindicator (P a) |}
); intros.
- abstract (apply LPRind_false; auto).
- apply LPRind_imp. apply H.
- apply LPRind_modular.
- apply LPRind_mult.
Defined.

Lemma unit_prob {A : Type} {x : A} : unit x (K True) = 1.
Proof. apply LPRind_true. unfold K. constructor. Qed.

Require Import Equalities Coq.Structures.Orders GenericMinMax.

(** Join semi-lattices, or directed sets. Natural numbers are
    one of many examples. We will often generalize sequences, which
    are functions of type (nat -> A), to nets, which are functions of
    type (I -> A), where I is a directed set. *)
Module JoinLat.
  Record t : Type :=
  { ty :> Type 
  ; le : ty -> ty -> Prop
  ; max : ty -> ty -> ty
  ; max_l : forall x y, le x (max x y)
  ; max_r : forall x y, le y (max x y)
  }.
End JoinLat.

Coercion JoinLat.ty : JoinLat.t >-> Sortclass.

Lemma LPRsup_sum_jlat : forall (I : JoinLat.t),
  forall (f g : I -> LPReal) ,
    (forall n m : I, JoinLat.le I n m -> f n <= f m) ->
    (forall n m : I, JoinLat.le I n m -> g n <= g m) ->
    LPRsup (fun x : I => f x + g x) = LPRsup f + LPRsup g.
Proof.
intros. eapply LPRsup_sum_lattice.
apply JoinLat.max_l.
apply JoinLat.max_r.
assumption. assumption.
Qed. 

(** This describes the property of when a valuation is
    _continuous_. This condition is analagous to countable additivity
    in measure theory. Essentially, if I have a sequence of subsets
    which is getting bigger and bigger, then the measure of the union
    of the subsets is the supremum of the measures of each of the
    subsets in the sequence. *)
Definition ContinuousV {A : Type} (mu : Valuation A)
  := forall (I : JoinLat.t) (f : JoinLat.ty I -> (A -> Prop))
       (fmono : forall (m n : JoinLat.ty I), JoinLat.le I m n -> (forall a, f m a -> f n a))
       , mu (fun a => exists n, f n a) = LPRsup (fun n => mu (f n)).

(** All the valuations we have seen so far are continuous in this
    sense. *)
Lemma zero_ContinuousV {A : Type} : ContinuousV (@zeroVal A).
Proof.
unfold ContinuousV. intros. simpl. symmetry.
apply LPRle_antisym.
- unfold LPRle. simpl. intros. destruct H. assumption.
- apply LPRzero_min.
Qed.

Lemma unit_ContinuousV {A : Type} : forall (a : A), ContinuousV (unit a).
Proof.
unfold ContinuousV. intros.
simpl. symmetry. apply LPRle_antisym.
- apply LPRsup_le. intros n. apply LPRind_imp.
  intros. exists n. assumption.
- rewrite LPRind_exists. reflexivity.
Qed.

Lemma add_ContinuousV {A : Type} : forall {mu nu : Valuation A},
  ContinuousV mu -> ContinuousV nu -> ContinuousV (mu + nu)%Val.
Proof.
intros. unfold ContinuousV in *. intros. simpl.
rewrite (LPRsup_sum_jlat I).
apply LPRplus_eq_compat. apply H. assumption.
apply H0. assumption. 
intros. apply monotonic. apply fmono. assumption.
intros. apply monotonic. apply fmono. assumption.
Qed.

Lemma scale_ContinuousV {A : Type} : forall (c : LPReal) (mu : Valuation A),
  ContinuousV mu -> ContinuousV (c * mu)%Val.
Proof.
intros. unfold ContinuousV in *. intros. simpl.
rewrite H by assumption.
apply LPRsup_scales.
Qed.

Definition pointwise {A B : Type} (cmp : B -> B -> Prop)
  (f g : A -> B) : Prop := forall (a : A), cmp (f a) (g a).

(** * Integration *)

(** Definition of integration and way too many facts about integration.
    Many of these facts are admitted, because I am being quite sloppy
    with measurability considerations. *)

(** An inductive definition of simple functions. I hesitate to
    call them functions because they aren't necessarily computable.
    *)
Inductive Simple {A : Type} :=
  | SStep : LPReal -> (A -> Prop) -> Simple
  | SPlus : Simple -> Simple -> Simple.

Arguments Simple : clear implicits.

(** Definition of how to integrate simple functions *)
Fixpoint SimpleIntegral {A : Type} (mu : (A -> Prop) -> LPReal) 
  (s : Simple A) : LPReal := match s with
  | SStep c P => c * mu P
  | SPlus f g => SimpleIntegral mu f + SimpleIntegral mu g
  end.

(** Here we consider a Simple as a pointwise function, in a sense,
    by integrating against a Dirac delta. *)
Definition SimpleEval {A : Type} (f : Simple A) (x : A) : LPReal :=
  SimpleIntegral (unit x) f.

(** To integrate a general function, we take the supremum over the
    integrals of all the simple functions where are no greater than
    the general function. *)
Definition integral {A : Type} (f : A -> LPReal) (mu : Valuation A) :=
  LPRsup (fun (pr : { s | pointwise LPRle (SimpleEval s) f}) =>
      SimpleIntegral mu (proj1_sig pr)).

Lemma int_simple_monotonic {A : Type} {s t : Simple A}
  {mu : Valuation A}
  : pointwise LPRle (SimpleEval s) (SimpleEval t)
  -> SimpleIntegral mu s <= SimpleIntegral mu t.
Proof.
generalize dependent t. unfold pointwise.
induction s; intros; simpl.
- induction t.
  + unfold SimpleEval in H. simpl in H. simpl.
Admitted.

Lemma int_simple_ge {A : Type} {s : Simple A} {f : A -> LPReal} 
  {mu : Valuation A}
  : pointwise LPRle f (SimpleEval s)
  -> integral f mu <= SimpleIntegral mu s.
Proof.
intros. 
unfold integral. apply LPRsup_le.
intros a. destruct a. simpl.
apply int_simple_monotonic.
unfold pointwise in *. intros. rewrite p. apply H.
Qed.

Lemma int_monotonic : forall {A : Type} {f g : A -> LPReal}
     , pointwise LPRle f g -> forall (mu : Valuation A)
     , integral f mu <= integral g mu.
Proof.
intros. unfold integral. apply LPRsup_monotonic_gen.
intros. destruct a. assert (pointwise LPRle (SimpleEval x) g).
unfold pointwise in *. intros. rewrite p. apply H. 
exists (exist _ x H0). simpl. reflexivity.
Qed.

Lemma undo_proj1sig {A : Type} {B : A -> Prop} 
  (a : A) (b : B a) : proj1_sig (exist _ a b) = a.
Proof. reflexivity. Qed.

Lemma int_adds_l {A : Type} : forall {f g : A -> LPReal} {mu : Valuation A}
     , integral f mu + integral g mu <= integral (fun x => f x + g x) mu.
Proof. 
intros. unfold integral. unfold LPRle. simpl. intros. 
destruct H; simpl in *.
- destruct H. destruct x. eexists. rewrite undo_proj1sig.
  simpl in H. eassumption.
- destruct H. destruct x. eexists. rewrite undo_proj1sig.
  simpl in H. eassumption.
- destruct H, H0. destruct x, x0. simpl in H, H0.
  eexists. rewrite undo_proj1sig.
  eapply dclosed. 2:apply H1. instantiate (1 := SPlus x x0).
  simpl. eapply LPRplusB; try eassumption. apply Qnnle_refl.
Grab Existential Variables.
simpl. unfold pointwise. intros. eapply LPRplus_le_compat. 
unfold pointwise in *. unfold LPRle. apply p.
unfold LPRle. apply p0. apply H2.

simpl in *. unfold pointwise. intros. apply LPRplusR. 
apply p. assumption.

simpl in *. unfold pointwise in *. intros. apply LPRplusL.
apply p. assumption.
Qed.

Lemma int_adds {A : Type} : forall {f g : A -> LPReal} {mu : Valuation A}
     , integral f mu + integral g mu = integral (fun x => f x + g x) mu.
Proof.
intros. apply LPRle_antisym.
- apply int_adds_l.
- unfold integral. apply LPRsup_le.
  intros. destruct a. simpl.
Admitted.

Fixpoint scaleSimple {A : Type} (c : LPReal) (s : Simple A) : Simple A
  := match s with
  | SStep x P => SStep (c * x) P
  | SPlus l r => SPlus (scaleSimple c l) (scaleSimple c r)
  end.

Lemma int_simple_scales {A : Type} : 
  forall {c : LPReal} {s : Simple A} { mu : Valuation A}
  , c * SimpleIntegral mu s = SimpleIntegral mu (scaleSimple c s).
Proof.
intros. induction s; simpl.
- ring.
- ring_simplify. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

Lemma int_scales_l {A : Type} : forall {c : LPReal} {f : A -> LPReal} {mu : Valuation A}
     , c * integral f mu <= integral (fun x => c * f x) mu.
Proof.
intros. unfold integral. rewrite LPRsup_scales.
apply LPRsup_monotonic_gen; intros.
destruct a. simpl. eexists. rewrite undo_proj1sig.
rewrite int_simple_scales. reflexivity.
Grab Existential Variables.
simpl. unfold pointwise. intros. unfold SimpleEval.
rewrite <- int_simple_scales. apply LPRmult_le_compat. reflexivity.
apply p.
Qed.

Lemma int_scales {A : Type} : forall {c : LPReal} {f : A -> LPReal} {mu : Valuation A}
     , c * integral f mu = integral (fun x => c * f x) mu.
Proof. 
intros. apply LPRle_antisym. 
- apply int_scales_l. 
- unfold integral. rewrite LPRsup_scales. apply LPRsup_monotonic_gen. intros.
  destruct a. simpl.
Admitted.

Lemma simple_int_monotonic_val {A : Type} {f : Simple A}
  {mu mu' : Valuation A}
  : (mu <= mu')%Val -> SimpleIntegral mu f <= SimpleIntegral mu' f.
Proof. intros. induction f; simpl.
- apply LPRmult_le_compat. reflexivity. apply H.
- simpl. apply LPRplus_le_compat; assumption.
Qed.

Lemma int_monotonic_val {A : Type} {f : A -> LPReal}
  {mu mu' : Valuation A}
  : (mu <= mu')%Val -> integral f mu <= integral f mu'.
Proof. intros.
unfold integral. apply LPRsup_monotonic.
intros. destruct a. simpl. apply simple_int_monotonic_val.
assumption.
Qed.

Lemma simple_int_adds_val {A : Type} {f : Simple A}
  {mu mu' : Valuation A}
  : SimpleIntegral (mu + mu')%Val f 
  = SimpleIntegral mu f + SimpleIntegral mu' f.
Proof.
induction f; simpl.
- ring. 
- simpl in *. rewrite IHf1. rewrite IHf2. ring.
Qed.

Lemma int_adds_val {A : Type} {f : A -> LPReal}
  {mu mu' : Valuation A}
  : integral f (mu + mu')%Val = integral f mu + integral f mu'.
Proof.
Admitted.

Lemma simple_int_scales_val {A : Type} {f : Simple A}
  {mu : Valuation A} {c : LPReal}
  : SimpleIntegral (c * mu)%Val f = c * SimpleIntegral mu f.
Proof. induction f; simpl in *.
- ring. 
- rewrite IHf1. rewrite IHf2. ring. 
Qed.

Lemma int_scales_val {A : Type} {f : A -> LPReal}
  {mu : Valuation A} {c : LPReal}
  : integral f (c * mu)%Val = c * integral f mu.
Proof.
unfold integral. symmetry. 
replace (fun pr : {s : Simple A | pointwise LPRle (SimpleEval s) f} =>
      SimpleIntegral (c * mu)%Val (proj1_sig pr)) with 
  (fun pr : {s : Simple A | pointwise LPRle (SimpleEval s) f} =>
      c * SimpleIntegral mu (proj1_sig pr)).
apply LPRsup_scales.
apply functional_extensionality. intros. 
symmetry. apply simple_int_scales_val.
Qed.

Lemma int_simple_le {A : Type} :
forall {s : Simple A} {f : A -> LPReal} {mu : Valuation A},
      pointwise LPRle (SimpleEval s) f
    ->  SimpleIntegral mu s <= integral f mu.
Proof. intros.
pose (exist (fun s' => pointwise LPRle (SimpleEval s') f) s H).
unfold integral.
erewrite <- LPRsup_ge. 
instantiate (1 := s0).
reflexivity.
Qed.

Lemma int_simple {A : Type} {s : Simple A} {mu : Valuation A}
  : integral (SimpleEval s) mu = SimpleIntegral mu s.
Proof.
apply LPReq_compat.
split; [apply int_simple_ge | apply int_simple_le]
  ; unfold pointwise; intros a; reflexivity.
Qed.

(** If two functions are equal at every point, then
    they integrate to the same thing. *)
Lemma int_pointwise_eq {A : Type} : 
  forall (f g : A -> LPReal), pointwise eq f g ->
  forall (mu : Valuation A),
  integral f mu = integral g mu.
Proof. intros. replace g with f. reflexivity. 
extensionality x. apply H.
Qed.

Theorem int_indicator {A : Type} {P : A -> Prop} {mu : Valuation A}
  : integral (fun x => LPRindicator (P x)) mu = mu P.
Proof.
rewrite int_pointwise_eq with (g := SimpleEval (SStep 1 P)).
rewrite int_simple. simpl. ring.
unfold SimpleEval. simpl. 
unfold pointwise. intros. ring.
Qed.

Lemma int_indicator_funext {A : Type}
  { P : A -> Prop } {mu : Valuation A}
  { f : A -> LPReal }
  : (forall a, LPRindicator (P a) = f a)
  -> integral f mu = mu P.
Proof.
intros.
replace f with (fun a => LPRindicator (P a)) by
  (apply functional_extensionality; intros; apply H).
apply int_indicator.
Qed.

Lemma integral_zero {A : Type} : forall {mu : Valuation A} (c : LPReal)
  , integral (SimpleEval (SStep c (K False))) mu = 0.
Proof.
intros.
rewrite int_simple. simpl. 
replace (mu (K False)) with 0. ring. symmetry. apply strict.
Qed.

Theorem int_dirac_simple {A : Type} {s : Simple A} {a : A} :
 SimpleIntegral (unit a) s = SimpleEval s a.
Proof.
unfold SimpleEval. induction s; simpl; reflexivity.
Qed.

Theorem int_dirac_test {A : Type} {f : A -> LPReal} {a : A}
  (s : Simple A)
  : pointwise LPRle (SimpleEval s) f
  -> integral (SimpleEval s) (unit a) <= f a.
Proof.
intros. rewrite int_simple. rewrite int_dirac_simple. apply H. 
Qed.

(** Integrating a function over a Dirac delta results in
    simply the function value at that point. *)
Theorem int_dirac {A : Type} {f : A -> LPReal} {a : A}
  : integral f (unit a) = f a.
Proof.
intros.
pose (s := SStep (f a) (fun a' => a = a')).
  unfold integral. eapply LPRsup_prop.
- intros pr. destruct pr. simpl. 
  replace (fun P => LPRindicator (P a)) with (val (unit a)) by reflexivity.
  rewrite int_dirac_simple. apply p.
- eexists. rewrite undo_proj1sig.
  instantiate (1 := s).
  rewrite int_dirac_simple. unfold SimpleEval; simpl.
  rewrite LPRind_true by reflexivity.
  replace (f a * 1) with (f a) by ring.
  reflexivity.
  Grab Existential Variables.
  simpl. unfold pointwise. intros. unfold SimpleEval.
  simpl. rewrite (SRmul_comm LPRsrt). apply LPRind_scale_le.
  intros H. induction H. reflexivity.
Qed.

(** Fubini's theorem about iterated integrals. It's likely _wrong_ as stated
    here, but it sure is useful! *)
Lemma fubini {A B : Type} (f : (A * B) -> LPReal)
  (muA : Valuation A) (muB : Valuation B)
 : integral (fun a => integral (fun b => f (a, b)) muB) muA
 = integral (fun b => integral (fun a => f (a, b)) muA) muB.
Proof.
Admitted.

Lemma fubini_curried {A B : Type} (f : A -> B -> LPReal)
  (muA : Valuation A) (muB : Valuation B)
 : integral (fun a => integral (fun b => f a b) muB) muA
 = integral (fun b => integral (fun a => f a b) muA) muB.
Proof.
pose (f' := fun p => f (fst p) (snd p)).
assert (
(fun a : A => integral (fun b : B => f a b) muB)
=
(fun a : A => integral (fun b : B => f' (a, b)) muB)
).
extensionality a.
apply int_pointwise_eq. unfold pointwise; intros b.
reflexivity.
rewrite H. clear H.

assert (
(fun b : B => integral (fun a : A => f a b) muA)
=
(fun b : B => integral (fun a : A => f' (a, b)) muA)
).
apply functional_extensionality. intros b.
apply int_pointwise_eq. unfold pointwise; intros a.
reflexivity.
rewrite H. clear H.
apply fubini.
Qed.

Lemma fubini_no_funext {A B : Type}
  (muA : Valuation A) (muB : Valuation B)
  {fA : A -> LPReal} {fB : B -> LPReal}
  {fAB : A -> B -> LPReal} {fBA : B -> A -> LPReal}
  : (forall a, integral (fAB a) muB = fA a)
  -> (forall b, integral (fBA b) muA = fB b)
  -> (forall a b, fAB a b = fBA b a)
  -> integral fA muA = integral fB muB.
Proof.
intros.
replace fA with (fun a => integral (fAB a) muB)
  by (apply functional_extensionality; assumption).
replace fB with (fun b => integral (fun a => fAB a b) muA).
Focus 2. apply functional_extensionality. 
intros. rewrite <- H0.
replace (fun a => fAB a x) with (fBA x).
Focus 2. apply functional_extensionality.
intros. symmetry. apply H1. 
reflexivity.
apply fubini_curried.
Qed.

(* Theorem 3.13 of Jones 1990 *)
Theorem directed_monotone_convergence {A : Type} :
  forall (mu : Valuation A) (I : JoinLat.t),
  forall (g : I -> (A -> LPReal)),
    ContinuousV mu ->
    integral (fun x => LPRsup (fun i => g i x)) mu
  = LPRsup (fun i => integral (fun x => g i x) mu).
Proof.
Admitted.

(** * Operations on valuations *)

(** Operations for composing valuations from other operations.
    Valuations form a monad, so we have [unit], [bind], [join],
    and [map]. We also have [product], which creates the product
    distribution from two independent distributions. *)

(** The "bind" of our monad. Given a measure over the space A, and a
    function which, given a point in A, returns a measure on B,
    we can produce a measure on B by integrating over A. *)

Lemma bind_modular {A B : Type} (v : Valuation A)
    (f : A -> Valuation B) :
   forall U V : B -> Prop,
   integral (fun x : A => (f x) U) v + integral (fun x : A => (f x) V) v =
   integral (fun x : A => (f x) (fun z : B => U z /\ V z)) v +
   integral (fun x : A => (f x) (fun z : B => U z \/ V z)) v.
  Proof.
  intros. do 2 rewrite int_adds. apply int_pointwise_eq.
  unfold pointwise. intros a.
  assert (
((f a) U + (f a) V) =
((f a) (fun z : B => U z /\ V z) + (f a) (fun z : B => U z \/ V z))
). apply modular. rewrite H. split; reflexivity.
  Qed.

Definition bind {A B : Type}
  (v : Valuation A) (f : A -> Valuation B)
  : Valuation B.
Proof. refine (
  {| val := fun P => integral (fun x => (f x) P) v |}
).
  Lemma bind_strict {A B : Type} (v : Valuation A)
    (f : A -> Valuation B) : integral (fun x : A => (f x) (K False)) v = 0.
  Proof.
  apply LPReq_compat. unfold LPReq. split.
  erewrite <- integral_zero.
  apply int_monotonic.
  unfold pointwise. intros.
  instantiate (1 := 0).
  rewrite strict. apply LPRzero_min.
  apply LPRzero_min.
  Qed.
  apply bind_strict.
- abstract (intros; apply int_monotonic;
  unfold pointwise; intros;
  apply monotonic; assumption).
- apply bind_modular.
- abstract (intros; rewrite int_scales; apply int_pointwise_eq;
  unfold pointwise; intros; apply factorizes).
Defined.

Lemma bind_ContinuousV {A B : Type} : forall (mu : Valuation A)
  (f : A -> Valuation B),
  ContinuousV mu -> (forall a, ContinuousV (f a))
  -> ContinuousV (bind mu f).
Proof.
intros. unfold ContinuousV. intros. simpl.
erewrite (int_pointwise_eq). Focus 2.
unfold pointwise. intros a. apply H0.
assumption.
rewrite directed_monotone_convergence.
reflexivity.
assumption.
Qed.

Lemma bind_prob {A B : Type} {mu : Valuation A}
  {f : A -> Valuation B}
  : mu (K True) = 1
  -> (forall a, (f a) (K True) = 1)
  -> bind mu f (K True) = 1.
Proof.
intros Hmu Hf. simpl.
rewrite <- Hmu. 
rewrite <- int_indicator.
apply int_pointwise_eq. unfold pointwise.
unfold K.
rewrite LPRind_true by trivial.
intros a.
apply Hf.
Qed.

(** The join operation of the Valuation monad. *)
Definition join {A : Type} (mu : Valuation (Valuation A))
  : Valuation A.
Proof. refine (
  {| val := fun P => integral (fun vA => val vA P) mu |}
).
- abstract (replace 0 with (0 * mu (K True)) by ring;
  rewrite <- int_indicator;
  rewrite int_scales;
  apply int_pointwise_eq; unfold pointwise; intros v;
  rewrite strict; ring).
- abstract (intros; apply int_monotonic; unfold pointwise;
  intros; apply monotonic; assumption).
- abstract (intros; repeat rewrite int_adds;
  apply int_pointwise_eq; unfold pointwise; intros;
  apply modular).
- abstract (intros; rewrite int_scales; apply int_pointwise_eq;
  unfold pointwise; intros; apply factorizes).
Defined.

(** Pushforward of a measure, i.e., map a function over a measure *)
Definition map {A B : Type} (f : A -> B) (v : Valuation A)
  : Valuation B.
Proof. refine (
  {| val := fun prop => val v (fun x => prop (f x)) |}
); intros.
- apply strict.
- apply monotonic. auto.
- apply modular; auto.
- apply factorizes.
Defined.

Lemma map_ContinuousV {A B : Type} : forall (mu : Valuation A)
  (f : A -> B), ContinuousV mu -> ContinuousV (map f mu).
Proof.
intros. unfold ContinuousV in *. intros. simpl.
rewrite H. reflexivity.
intros. eapply fmono. eassumption. assumption.
Qed.


Lemma map_compose {A B C : Type} (mu : Valuation A)
  (g : B -> C) (f : A -> B)
  : map (fun x => g (f x)) mu = map g (map f mu).
Proof.
apply Valeq_compat. unfold Valeq. intros P.
simpl. reflexivity.
Qed.

Lemma bind_map_swap {A B C : Type}
  {muA : Valuation A} {muB : Valuation B}
  { f : A -> B -> C }
  : bind muA (fun a => map (f a)         muB)
  = bind muB (fun b => map (fun a => f a b) muA).
Proof. 
apply Valeq_compat. unfold Valeq. intros P.
simpl.
eapply fubini_no_funext.
intros a. rewrite <- int_indicator. reflexivity. 
intros b. rewrite <- int_indicator. reflexivity. 
simpl. reflexivity. 
Qed.

(** The following definitions and lemmas lead up to the
    [change_of_variables] theorem, which gives an easy way
    to integrate over a pushforward measure. *)
Fixpoint map_Simple {A B : Type} 
  (f : A -> B) (s : Simple B) : Simple A
  := match s with
  | SStep c P => SStep c (fun x => P (f x))
  | SPlus l r => SPlus (map_Simple f l) (map_Simple f r)
  end.

Lemma map_SimpleIntegral {A B : Type}
  {s : Simple B} {f : A -> B}
  { mu : Valuation A}
  : SimpleIntegral mu (map_Simple f s) 
  = SimpleIntegral (map f mu) s. 
Proof.
induction s; intros.
- simpl. reflexivity.
- simpl in *. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

Theorem change_of_variables {A B : Type}
  {mu : Valuation A} {f : A -> B} {g : B -> LPReal}
  : integral (fun x => g (f x)) mu
  = integral g (map f mu).
Proof.
unfold integral. apply LPReq_compat. split.
- unfold LPRle. simpl. intros. destruct H. 
  destruct x. simpl in H.
  (* measurability of functions definitely needed here *)
  admit.
- apply LPRsup_le; intros simp;
  destruct simp as [s sle]; simpl.
  apply LPRsup_ge2.
Admitted.

Lemma change_of_variables_val {A B : Type} (mu : Valuation A)
  (f : A -> B) :
  forall (P : A -> Prop) (Q : B -> Prop),
  (forall a : A, P a <-> Q (f a))
  -> mu P = (map f mu) Q.
Proof. intros. simpl. rewrite (val_iff H). reflexivity.
Qed.

(** Product measures. That is, the joint distribute for two
    independent measures. *)
Definition product {A B : Type}
  (muA : Valuation A) (muB : Valuation B)
  : Valuation (A * B) := 
  bind muA (fun a => map (fun b => (a, b)) muB).

(** We get what we would expect if we take the product of a
   Dirac delta with another distribution. *)
Theorem unitProdId {A B : Type}
  (a : A) (muB : Valuation B) (P : (A * B) -> Prop)
  : product (unit a) muB P = muB (fun b => P (a, b)).
Proof. simpl. rewrite int_dirac. reflexivity. Qed.

(** Product measures factor in the expected way. *)
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
apply int_pointwise_eq.
unfold pointwise. intros.
rewrite LPRind_mult. reflexivity.
Qed.

(** Create a "submeasure" by restricting a measure to
    a subset of its domain. The new valuation may only have
    positive measure on subsets which satisfy the predicate. *)
Definition restrict {A : Type} (mu : Valuation A)
  (P : A -> Prop) : Valuation A.
Proof.
refine (
{| val := fun Q => mu (fun x => P x /\ Q x) |}
).
- abstract (simpl; erewrite val_iff; 
  [ apply strict
  | unfold K; intros; intuition ]). 
- abstract (intros; apply monotonic; intros;
  destruct H0; intuition).
- abstract (intros; replace 
  (mu (fun x : A => P x /\ U x /\ V x)) with
  (mu (fun x => (P x /\ U x) /\ (P x /\ V x)))
    by (apply val_iff; intros; intuition); replace 
  (mu (fun x : A => P x /\ (U x \/ V x))) with
  (mu (fun x => (P x /\ U x) \/ (P x /\ V x)))
    by (apply val_iff; intros; intuition);
  apply modular).
- abstract (intros; erewrite val_iff;
    [ eapply factorizes | intuition ]).
Defined.

Lemma restrict_monotonic {A : Type} {mu : Valuation A}
  { P Q : A -> Prop} : (forall a, P a -> Q a) 
  -> (restrict mu P <= restrict mu Q)%Val.
Proof.
intros. unfold Valle. intros p. simpl.
apply monotonic. intros; intuition.
Qed.

Lemma restrict_true {A : Type} {mu : Valuation A}
  { P : A -> Prop } : (forall a, P a)
  -> restrict mu P = mu.
Proof.
intros. apply Valeq_compat. unfold Valeq.
intros Q. simpl. apply val_iff. intros. intuition.
Qed.

Lemma restrict_false {A : Type} {mu : Valuation A}
  {P : A -> Prop} : A -> (forall a, ~ P a)
  -> restrict mu P = 0%Val.
Proof. intros. apply Valeq_compat. unfold Valeq. 
intros Q. simpl. erewrite val_iff. apply strict.
intros; unfold K; intuition. apply (H a). assumption.
Qed.


(** * Measurability *)

(** This is an attempt for me to define measurability properly
    with how I am doing valuations. I'm not sure this is the right
    way to go and haven't really gotten anywhere with this. *)

(** Definition of measurability for functions which output
    lower real numbers. *)
Definition MeasurableR {A : Type} (f : A -> LPReal)
  := forall (eps : Qnn), (eps > 0)%Qnn
   -> exists (s : Simple A)
   , pointwise LPRle (SimpleEval s) f
   /\ pointwise LPRle f (fun x => SimpleEval s x + LPRQnn eps).

(** All simple functions are measurable according to this definition. *)
Lemma MeasurableR_Simple {A : Type} (s : Simple A)
  : MeasurableR (SimpleEval s).
Proof.
unfold MeasurableR. intros. exists s. split; unfold pointwise; intros a.
reflexivity. replace (SimpleEval s a) with (SimpleEval s a + 0)
  at 1 by ring. apply LPRplus_le_compat. reflexivity.
  apply LPRzero_min.
Qed.

(** For functions which do not output lower real numbers, a function
    is measurable if it preservers measurability when pre-composed 
    with any R-measurable function. *)
Definition Measurable {A B : Type} (f : A -> B)
  := forall (g : B -> LPReal), MeasurableR g -> MeasurableR (fun x => g (f x)).

Fixpoint compose_Simple {A : Type} (g : Simple LPReal)
  (f : Simple A) : Simple A := match g with
  | SStep c P => SStep c (fun a => P (SimpleEval f a))
  | SPlus s t => SPlus (compose_Simple s f) (compose_Simple t f)
  end.

Lemma compose_Simple_composes {A : Type} {g : Simple LPReal}
  {f : Simple A}
  : forall a, SimpleEval (compose_Simple g f) a
  = SimpleEval g (SimpleEval f a).
Proof.
induction g; simpl; intros.
- unfold SimpleEval. simpl. reflexivity.
- unfold SimpleEval in *. simpl in *.
  rewrite IHg1. rewrite IHg2. reflexivity.
Qed.

(** Simple functions are also measurable according to this
    more general definition. *)
Lemma Measurable_Simple {A : Type} (s : Simple A)
  : Measurable (SimpleEval s).
Proof.
unfold Measurable. intros. unfold MeasurableR in *.
intros.
specialize (H eps H0).
destruct H as [x [low high]].
pose (compose_Simple x s).
exists s0. unfold pointwise in *. 
split; intros; unfold s0; rewrite compose_Simple_composes.
- apply low.
- apply high.
Qed.

(** Measurable functions form a category. *)
Lemma Measurable_id {A : Type}
  : Measurable (fun x : A => x).
Proof. unfold Measurable. intros.  apply H.
Qed.

Lemma Measurable_compose {A B C : Type}
  {f : A -> B} {g : B -> C}
  : Measurable f -> Measurable g -> Measurable (fun x => g (f x)).
Proof.
intros. unfold Measurable in *. intros.
apply (H (fun x => g0 (g x))).
apply H0. assumption.
Qed.

(** * Supremum and fixpoint valuations. *)

(** Supremum valuations (i.e., taking a limit of "increasing"
    measures, and fixpoint valuations, which are the analog of
    fixpoint functions in functional programming. *)

Definition supValuation {A : Type} (I : JoinLat.t)
  (f : I -> Valuation A)
  (fmono : forall (n m : I), JoinLat.le I n m -> (f n <= f m)%Val)
 : Valuation A.
Proof. refine (
  {| val := fun P => LPRsup (fun i => (f i) P) |}
).
- abstract (apply LPReq_compat; split;
  [ apply LPRsup_le; intros; erewrite <- strict;
    auto using monotonic
  | apply LPRzero_min ]).
- abstract (auto using LPRsup_monotonic, monotonic).
- abstract (intros;
  repeat (rewrite <- (LPRsup_sum_lattice _ _ (JoinLat.le I) (JoinLat.max I));
    try (auto using JoinLat.max_l, JoinLat.max_r))
   ; try (intros; apply fmono; auto);
  apply LPRsup_eq_pointwise; intros;
  apply modular).
- abstract (intros; rewrite LPRsup_scales; apply LPRsup_eq_pointwise;
  intros; apply factorizes).
Defined.

Lemma sup_ContinuousV {A : Type} : forall (I : JoinLat.t) 
  (f : I -> Valuation A)
  (fmono : forall m n : I, JoinLat.le I m n -> (f m <= f n)%Val)
  (fcont : forall n : I, ContinuousV (f n)),
  ContinuousV (supValuation I f fmono).
Proof.
intros. unfold ContinuousV.
intros. simpl.
unfold ContinuousV in fcont.
replace (fun i : JoinLat.ty I =>
      (f i) (fun a : A => exists n : JoinLat.ty I0, f0 n a))
with (fun i : JoinLat.ty I =>
      LPRsup (fun n0 : JoinLat.ty I0 => (f i) (f0 n0))).
apply LPRsup_iterated.
extensionality i. symmetry. apply fcont.
assumption.
Qed. 

Definition natJoinLat : JoinLat.t :=
  {| JoinLat.ty := nat
  ;  JoinLat.le := le
  ;  JoinLat.max := max
  ;  JoinLat.max_l := Max.le_max_l
  ;  JoinLat.max_r := Max.le_max_r
  |}.

(** The nth iteration of the fixpoint of a functional on
    measures *)
Fixpoint fixn {A : Type}
  (f : Valuation A -> Valuation A) (n : nat)
  : Valuation A
  := match n with
  | 0 => 0%Val
  | S n' => f (fixn f n')
  end.

(** If our valuation functional is monotonic, then the
    fixpoint is nondecreasing. *)
Lemma fixnmono {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : forall (n : nat), (fixn f n <= fixn f (S n))%Val.
Proof. intros. induction n.
simpl. unfold Valle; intros. simpl. apply LPRzero_min.
simpl. apply fmono. assumption.
Qed.

Lemma fixnmono2 {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, (u <= v -> f u <=f v)%Val)
  : forall (m n : nat), (m <= n)%nat -> (fixn f m <= fixn f n)%Val.
Proof. intros. induction H. apply Valle_refl. 
eapply Valle_trans. eassumption. apply fixnmono. assumption.
Qed.

(** If we have a valuation functional which is monotonic, we can take
    its fixpoint! *)
Definition fixValuation {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : Valuation A
  := supValuation natJoinLat (fun n => (fixn f n)) 
     (fixnmono2 _ fmono).

Lemma fixValuation_subProb {A : Type}
  (f : Valuation A -> Valuation A)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  (fbounded : forall v, val v (K True) <= 1 -> val (f v) (K True) <= 1)
  : (fixValuation f fmono) (K True) <= 1.
Proof. simpl. apply LPRsup_le.
intros n. induction n. simpl. apply LPRzero_min.
simpl. apply fbounded. assumption.
Qed.

Lemma fix_ContinuousV {A : Type} : forall (f : Valuation A -> Valuation A)
    (fmono : forall u v : Valuation A, (u <= v)%Val -> (f u <= f v)%Val),
  (forall (v : Valuation A), ContinuousV v -> ContinuousV (f v))
  -> ContinuousV (fixValuation f fmono).
Proof.
intros. unfold fixValuation. apply sup_ContinuousV.
intros n. induction n; simpl.
- apply zero_ContinuousV.
- apply H. assumption.
Qed. 

Theorem fixValuation_fixed_u {A : Type} (f : Valuation A -> Valuation A)
  (fmono : forall u v : Valuation A, (u <= v)%Val -> (f u <= f v)%Val)
  : (fixValuation f fmono <= f (fixValuation f fmono))%Val.
Proof.
unfold Valle. intros P. apply LPRsup_le. intros n. destruct n; simpl.
- apply LPRzero_min.
- apply fmono. unfold Valle; intros. simpl.
  apply LPRsup_ge2. exists n. reflexivity.
Qed.

(** Definition of when a functional is continuous. *)
Definition Continuous {A : Type} (f : Valuation A -> Valuation A) 
  := forall (I : JoinLat.t) (nonempty : I) (g : I -> Valuation A)
       (gmono : forall m n : I, JoinLat.le I m n -> (g m <= g n)%Val)
       (P : A -> Prop),
      (f (supValuation I g gmono)) P
    = LPRsup (fun x : I => f (g x) P).

(** If a functional is continuous, then we indeed reach a fixpoint
    when we apply [fixValuation]. *)
Theorem fixValuation_fixed {A : Type} (f : Valuation A -> Valuation A)
  (fmono : forall u v : Valuation A, (u <= v)%Val -> (f u <= f v)%Val)
  : Continuous f
  -> f (fixValuation f fmono) = fixValuation f fmono.
Proof.
intros.
apply Valle_antisym.
- unfold Valle. intros P. unfold Continuous in H.
  unfold fixValuation at 1. rewrite H.
  apply LPRsup_le. intros n.
  simpl. apply LPRsup_ge2. exists (S n). reflexivity. exact 0%nat.
- apply fixValuation_fixed_u.
Qed.

Require Finite.

Module F := Finite.

(** * Reasoning about measures *)

(** A set of techniques for reasoning about measures. *)

(** Binary version of the union bound. *)
Lemma union_bound2 {A : Type} {mu : Valuation A}
  (P Q : A -> Prop)
  : mu (fun z => P z \/ Q z) <= mu P + mu Q.
Proof.
rewrite modular. eapply LPRle_trans.
Focus 2. eapply LPRplus_le_compat.
apply LPRzero_min. reflexivity.
ring_simplify. 
reflexivity.
Qed.

(** Finite version of the union bound. *)
Lemma union_bound {A : Type} {mu : Valuation A}
  (xs : list (A -> Prop))
  : mu (List.fold_right (fun P Q z => P z \/ Q z) (K False) xs) <=
    List.fold_right LPRplus 0 (List.map (val mu) xs).
Proof.
induction xs; simpl.
- rewrite strict. reflexivity.
- rewrite <- IHxs. apply union_bound2.
Qed.

Definition val_destruct {A : Type} (mu : Valuation A)
  (P : A -> Prop) : Valuation A :=
  (restrict mu P + restrict mu (fun a => ~ P a))%Val.

Lemma val_destruct_dec {A : Type} {mu : Valuation A}
  {P : A -> Prop} : (forall a, {P a} + {~ P a})
  -> val_destruct mu P = mu.
Proof.
intros dec_P.
apply Valeq_compat.
unfold Valeq. intros Q. simpl. apply LPReq_compat. split.
- rewrite modular. replace (mu (fun z : A => (P z /\ Q z) /\ ~ P z /\ Q z))
  with 0. rewrite (SRadd_0_l LPRsrt). apply monotonic.
  intuition.
  erewrite val_iff. symmetry. apply strict. unfold K; intros; intuition.
- rewrite <- union_bound2. apply monotonic. intros. 
  destruct (dec_P z); [left | right]; intuition.
Qed.

Lemma val_or_disjoint {A : Type} {mu : Valuation A}
  : forall (U V : A -> Prop), (forall a, U a -> V a -> False)
  -> mu U + mu V = mu (fun a => U a \/ V a).
Proof. intros.
rewrite modular.
replace (mu (fun z : A => U z /\ V z)) with 0.
ring.
erewrite val_iff.
symmetry. apply strict.
unfold K. intros; split; intros; intuition.
apply (H a); assumption.
Qed.

(** [inject] is similar to [restrict]. Recall that [restrict] effectively
    reduced a measure so that it may only be positive in a certain subspace.
    [inject], given an injection from some type A to some type B, converts
    a measure on B into a measure on A: the measure of a subset of A is simply
    the measure of f(A) according to the measure on B. *)
Lemma inject_modular {A B : Type} (f : A -> B)
  (finj : forall (x y : A), f x = f y -> x = y)
  (mu : Valuation B)
  : forall U V : A -> Prop,
   mu (fun b : B => exists a : A, U a /\ f a = b) +
   mu (fun b : B => exists a : A, V a /\ f a = b) =
   mu (fun b : B => exists a : A, (U a /\ V a) /\ f a = b) +
   mu (fun b : B => exists a : A, (U a \/ V a) /\ f a = b).
  Proof.
  intros. 
  remember (fun b : B => exists a : A, U a /\ f a = b) as U'.
  remember (fun b : B => exists a : A, V a /\ f a = b) as V'.
  assert (forall x, (fun b : B => exists a : A, (U a /\ V a) /\ f a = b) x
    <-> (fun b => U' b /\ V' b) x).
  intros. split; intros. rewrite HeqU'. rewrite HeqV'.
  destruct H as [a [[Ua Va] fax]].
  split; exists a; split; try assumption.
  rewrite HeqU' in H. rewrite HeqV' in H.
  destruct H as [[a [Ua fax]] [a' [Va' fa'x]]].
  subst. apply finj in fa'x. subst. exists a. intuition.
  rewrite (val_iff H).
  assert (forall x, (fun b : B => exists a : A, (U a \/ V a) /\ f a = b) x
    <-> (fun b => U' b \/ V' b) x).
  intros; split; intros. destruct H0 as [a [UVa fax]].
  destruct UVa; [left | right].
  rewrite HeqU'. exists a. intuition.
  rewrite HeqV'. exists a. intuition.
  destruct H0. rewrite HeqU' in H0. destruct H0 as [a [Ua fax]].
  exists a. intuition.
  rewrite HeqV' in H0. destruct H0 as [a [Va fax]].
  exists a. intuition.
  rewrite (val_iff H0).
  apply modular.
  Qed.

Definition inject {A B : Type} (f : A -> B)
  (finj : forall (x y : A), f x = f y -> x = y)
  (mu : Valuation B)
  : Valuation A.
Proof.
refine (
  {| val := fun P => mu (fun b => exists a : A, P a /\ f a = b) |}
).
- abstract (erewrite val_iff; 
  [ apply strict
  | unfold K; firstorder ]).
- abstract (intros; apply monotonic; firstorder).
- apply inject_modular; assumption.
- abstract (intros; erewrite val_iff;
  [ apply factorizes | firstorder]).
Defined.

Lemma inl_inj {A B : Type} : forall (a a' : A), inl B a = inl a' -> a = a'.
Proof. congruence. Qed.

Lemma inr_inj {A B : Type} : forall (b b' : B), inr A b = inr b' -> b = b'.
Proof. congruence. Qed.

(** The measure of some subset on a sum type can be computed by
    adding the measure inside each of the two disjuncts. *)
Lemma splitValuation {A B : Type} (mu : Valuation (A + B))
  (P : A + B -> Prop) : mu P = (inject inl inl_inj mu) (fun a => P (inl a))
                          + (inject inr inr_inj mu) (fun b => P (inr b)).
Proof.
pose (fun x : A + B => match x with | inl a => P (inl a) | inr b => False end) as PA.
  pose (fun x : A + B => match x with | inl a => False | inr b => P (inr b) end) as PB.
assert (
  (forall (a : A), ~ PB (inl a)) /\ (forall b : B, ~ PA (inr b)) /\
  (forall x, P x <-> (fun y => PA y \/ PB y) x)) as H.
  intuition.
  destruct H as [PBa [PAb Piff]].
  rewrite (val_iff Piff).
  assert (forall x, PA x -> PB x -> False).
  intros. destruct x. apply (PBa a). assumption.
  apply (PAb b). assumption.
  rewrite <- val_or_disjoint by assumption.

  assert (forall v : Valuation (A + B), v PA = (inject inl inl_inj v) (fun x => P (inl x))) as inlprf. 
  intros. simpl. apply val_iff.
  intros. split; intros. destruct a. exists a. intuition.
  simpl in H0. contradiction.
  destruct H0 as [x [Px inlx]].
  rewrite <- inlx. simpl. assumption.

  assert (forall v : Valuation (A + B), v PB = (inject inr inr_inj v) (fun x => P (inr x))) as inrprf.
  intros. simpl. apply val_iff.
  intros. split; intros. destruct a. simpl in H0. contradiction. 
  exists b. intuition.
  destruct H0 as [x [Px inlx]].
  rewrite <- inlx. simpl. assumption.
  rewrite inlprf. rewrite inrprf. reflexivity.
Qed.

(** If we have finite measures [mu] and [nu],
    we can determine whether they are equivalent measures by checking to see
    whether they agree on the measure of each of the singleton sets.

    [build_finite] allows us to build finite distributions by specifying them
    pointwise, and [fin_dec] allows one to prove equivalence of two finite 
    measures by checking them pointwise. 
*)

Set Asymmetric Patterns.

Fixpoint build_finite {A : Type} (fin : Finite.T A) : (A -> LPReal) -> Valuation A 
  := match fin with
  | F.F0 => fun _ => 0%Val
  | F.FS _ fin' => fun f => 
     (f (inl I) * unit (inl I) + map inr (build_finite fin' (fun x => f (inr x))))%Val
  | F.FIso _ _ fin' t => fun f => 
     map (Iso.to t) (build_finite fin' (fun x => f (Iso.to t x)))
  end.

Lemma fin_char {A : Type} : forall (fin : Finite.T A) (mu : Valuation A),
  mu = build_finite fin (fun a => mu (eq a)).
Proof. 
intros. induction fin; apply Valeq_compat; unfold Valeq; simpl; intros P.
- erewrite val_iff. apply strict. intros. contradiction.
- rewrite splitValuation. apply LPRplus_eq_compat.
  + simpl. rewrite (SRmul_comm LPRsrt). rewrite <- factorizes.
    apply val_iff. intros. split; intros.
    destruct H. destruct x. assumption. exists I. assumption.
  + rewrite (IHfin (inject _ _ _)).
    replace (fun a : A => (inject inr inr_inj mu) (eq a))
    with (fun x : A => mu (eq (inr x))).
    reflexivity.
    extensionality a. simpl. apply val_iff. intros; split; intros.
    destruct a0. congruence. inversion H. subst.
    exists a0. intuition. destruct H as [a1 [aeqa1 ans]].
    subst. reflexivity.
- assert (mu P = (map (Iso.from t) mu) (fun a => P (Iso.to t a))).
  simpl. apply val_iff. intros b. rewrite Iso.to_from. reflexivity.
  rewrite H. rewrite (IHfin (map _ _)).
  replace (fun a : A => (map (Iso.from t) mu) (eq a))
  with (fun x : A => mu (eq (Iso.to t x))). reflexivity.
  extensionality a. simpl. apply val_iff. intros. split; intros.
  rewrite <- H0. symmetry.  apply Iso.from_to. 
  rewrite H0. apply Iso.to_from.
Qed.

Lemma fin_dec {A : Type} : forall (fin : Finite.T A)
  (mu nu : Valuation A)
  , (forall (a : A), mu (eq a) = nu (eq a))
  -> mu = nu.
Proof.
intros. rewrite (fin_char fin mu). rewrite (fin_char fin nu).
replace (fun a => mu (eq a)) with (fun a => nu (eq a))
  by (extensionality x; intuition).
reflexivity.
Qed.

Require Fin. 

(** Now, we will begin to prove a similar principle for countable measures.
    For now, we will stick to measures on [Nat], but this can probably be
    generalized to more general families of types than [Fin] and [Nat].

    At this point, for the theorem to go through, we need the measures to
    be continuous. We then show that they must agree when restricted by
    any finite subset, and then by continuity, they must agree everywhere.
*)
Lemma restrict_fin_monotonic : forall {mu : Valuation nat}
  (m n : nat), (m <= n)%nat 
  -> (restrict mu (fun k => (k < m)%nat) <= restrict mu (fun k => (k < n)%nat))%Val.
Proof. 
intros. unfold Valle; intros. simpl. apply monotonic.
intros. destruct H0. split. eapply Le.le_trans; eassumption. assumption.
Qed.

Lemma continuous_val_fin_nat : forall (mu : Valuation nat),
  ContinuousV mu ->
  mu = supValuation natJoinLat (fun n => restrict mu (fun k => (k < n)%nat)) 
   restrict_fin_monotonic.
Proof. intros. apply Valeq_compat. unfold Valeq. intros. simpl.
unfold ContinuousV in H. specialize (H natJoinLat). rewrite <- H.
apply val_iff. intros k. split; intros. exists (S k). intuition.
destruct H0 as [n [kn Pk]]. assumption.
simpl. intros. destruct H1. split. eapply Le.le_trans; eassumption.
assumption.
Qed.

Definition ftonat {n : nat} (x : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat x).

Lemma ftonat_inj {n : nat} : forall (x y : Fin.t n),
  ftonat x = ftonat y -> x = y.
Proof.
unfold ftonat.
intros.
destruct (Fin.to_nat x) eqn:nx. destruct (Fin.to_nat y) eqn:ny.
simpl in *. subst.
assert (l0 = l). 
admit. (* provable since le_nat has proof irrelevance but 
          can't find a predone proof yet *)
subst. 
rewrite <- (Fin.of_nat_to_nat_inv x).
rewrite <- (Fin.of_nat_to_nat_inv y).
rewrite nx. rewrite ny. reflexivity.
Admitted.

Lemma nat_restrict_inject : forall (mu : Valuation nat) (n : nat) (P : nat -> Prop)
  , restrict mu (fun k => (k < n)%nat) P 
  = (inject ftonat (@ftonat_inj n) mu) (fun x => P (ftonat x)).
Proof.
intros. simpl. apply val_iff. intros; split; intros.
destruct H. exists (Fin.of_nat_lt H).
assert (ftonat (Fin.of_nat_lt H) = a).
admit. split. rewrite H1. assumption. assumption.
destruct H as [fa [Pfa faa]].
rewrite faa in Pfa.
unfold ftonat in faa.
destruct (Fin.to_nat fa). simpl in faa. subst. intuition.
Admitted.

Fixpoint build_nat_fin (f : nat -> LPReal) (lim : nat) : Valuation nat := 
  match lim with
  | 0 => 0%Val
  | S lim' => (build_nat_fin f lim' + f lim' * unit lim')%Val
  end.

Lemma build_nat_fin_mono1 {f : nat -> LPReal} : forall n : nat,
   (build_nat_fin f n <= build_nat_fin f (S n))%Val.
Proof.
intros. simpl. unfold Valle. intros. simpl.
replace ((build_nat_fin f n) P) with ((build_nat_fin f n) P + 0) at 1
  by ring.
apply LPRplus_le_compat. reflexivity. apply LPRzero_min.
Qed.

Lemma build_nat_fin_mono {f : nat -> LPReal} : forall n m : nat, (n <= m)%nat ->
   (build_nat_fin f n <= build_nat_fin f m)%Val.
Proof.
intros. induction H. apply Valle_refl.
eapply Valle_trans. apply IHle. apply build_nat_fin_mono1.
Qed.

Definition build_nat (f : nat -> LPReal) : Valuation nat
  := supValuation natJoinLat (fun n => build_nat_fin f n) build_nat_fin_mono.

Require NPeano.
Lemma nat_char : forall (mu : Valuation nat),
  ContinuousV mu ->
  mu = build_nat (fun n => mu (eq n)).
Proof. 
intros. 
rewrite (continuous_val_fin_nat mu) at 1 by assumption.
unfold build_nat.
apply Valeq_compat; intros P. simpl.
apply LPRsup_eq_pointwise.
intros. induction a.
- simpl. erewrite val_iff. apply strict. unfold K. intuition.
- simpl. rewrite <- IHa. rewrite (SRmul_comm LPRsrt). 
  rewrite <- factorizes.
  rewrite modular.
  replace (mu (fun z : nat => ((z < a)%nat /\ P z) /\ P a /\ a = z))
    with 0.
  ring_simplify. apply val_iff. intros; split; intros.
  destruct H0. inversion H0. subst. right. intuition.
  subst. left. intuition. destruct H0. intuition. intuition.
  subst. assumption.
  erewrite val_iff. symmetry. apply strict.
  unfold K. intros; split; intros. destruct H0 as [[lta p] [p1 eqa]].
  subst. apply NPeano.Nat.lt_neq in lta. apply lta. reflexivity.
  contradiction.
Qed.

(** We can prove that two continuous measures on the natural numbers are 
    equal by proving that they are equal pointwise! *)
Lemma nat_dec : forall {mu nu : Valuation nat}
  , ContinuousV mu -> ContinuousV nu
  -> (forall (n : nat), mu (eq n) = nu (eq n))
  -> mu = nu.
Proof. intros.
rewrite nat_char by assumption.
rewrite (nat_char mu) by assumption.
replace (fun n : nat => mu (eq n)) with (fun n : nat => nu (eq n))
  by (extensionality x; auto).
reflexivity.
Qed.

(** * Examples *)

(** Probabilistic choice. Choose the left distribution with
    probability p, and the right with probability (1 - p).
    Only well-formed if the argument p satisfies p <= 1. *)
Definition pchoice {A : Type} (p : Qnn)
  (mu mu' : Valuation A) : Valuation A
  := (LPRQnn p * mu + LPRQnn (1 - p)%Qnn * mu')%Val.

Lemma pchoice_prob {A : Type} {p : Qnn}
  {mu mu' : Valuation A} :
    (p <= 1)%Qnn -> mu (K True) = 1 -> mu' (K True) = 1
  -> (pchoice p mu mu') (K True) = 1.
Proof.
intros. unfold pchoice. simpl. rewrite H0. rewrite H1.
ring_simplify.
rewrite LPRQnn_plus.
apply LPRQnn_eq.
apply Qnnminus_plus.
assumption.
Qed.

Lemma pchoice_ContinuousV {A : Type} : forall (p : Qnn) (mu nu : Valuation A),
  ContinuousV mu -> ContinuousV nu -> ContinuousV (pchoice p mu nu).
Proof. intros. unfold pchoice.
apply add_ContinuousV; apply scale_ContinuousV; assumption.
Qed.

(** We will now define uniform distributions over finite
    lists of elements. *)
Require Fin Vector.

Fixpoint uniform_helper {A : Type} (p : LPReal) (xs : list A) := match xs with
  | nil => 0%Val
  | (x :: xs')%list => (p * unit x + uniform_helper p xs')%Val
end.

Lemma uniform_helper_weight {A : Type} {p : LPReal} {xs : list A}
  : uniform_helper p xs (K True) = LPRQnn (Qnnnat (length xs)) * p.
Proof.
induction xs. 
- simpl. ring. 
- simpl. rewrite LPRind_true by (unfold K; trivial).
  rewrite IHxs.
  rewrite <- LPRQnn_plus. ring.
Qed.

(** A uniform distribution over a finite, non-empty list
    of elements. *)
Definition uniform {A : Type} {n : nat} (xs : Vector.t A (S n)) :=
  uniform_helper (LPRQnn (Qnnfrac (S n))) (Vector.to_list xs).

Lemma Vector_length {A : Type} {n : nat} {xs : Vector.t A n}
  : length (Vector.to_list xs) = n.
Proof. induction xs.
- reflexivity.
- unfold Vector.to_list in *. simpl. rewrite IHxs. reflexivity.
Qed.

Lemma uniform_prob {A : Type} : forall {n : nat} {xs : Vector.t A (S n)}
  , (uniform xs) (K True) = 1.
Proof.
intros. unfold uniform.
rewrite uniform_helper_weight. rewrite Vector_length.
rewrite LPRQnn_mult. rewrite Qnnnatfrac. reflexivity.
Qed.

Definition bernoulli (p : Qnn) : Valuation bool :=
 pchoice p (unit true) (unit false).

Lemma bernoulli_prob {p : Qnn}
  : (p <= 1)%Qnn -> bernoulli p (K True) = 1.
Proof. 
intros. unfold bernoulli. apply pchoice_prob; try apply unit_prob.
assumption.
Qed.

Lemma bernoulli_ContinuousV : forall (p : Qnn),
  ContinuousV (bernoulli p).
Proof.
intros.  unfold bernoulli. 
apply pchoice_ContinuousV; apply unit_ContinuousV.
Qed.

Fixpoint binomial (p : Qnn) (n : nat)
  : Valuation nat := match n with
  | 0 => unit 0%nat
  | S n' => bind (bernoulli p) (fun b => 
   let inc := if b then S else fun x => x in
  (map inc (binomial p n')))
  end. 

Lemma binomial_prob (p : Qnn) (ple1 : (p <= 1)%Qnn)
  (n : nat) : binomial p n (K True) = 1.
Proof.
induction n; simpl.
- unfold K. apply LPRind_true. constructor.
- unfold K in *. rewrite IHn. 
rewrite <- (LPRind_true True) by trivial. 
rewrite int_indicator.
rewrite LPRind_true by trivial. apply bernoulli_prob.
assumption.
Qed.

Require Import Omega.

Lemma minus_Succ {k n : nat} : (S k <= n -> S (n - S k) = n - k)%nat.
Proof.
omega. 
Qed.

(** The binomial distribution will never return a number of success
    greater than the number of trials. *)
Lemma binomial_bounded {p : Qnn} 
  {n : nat} (k : nat) 
  : (n < k)%nat 
  -> (binomial p n) (eq k) = 0.
Proof.
intros. generalize dependent k. induction n; intros.
- simpl. rewrite LPRind_false. reflexivity.
  unfold not; intros. subst. 
  apply Lt.lt_0_neq in H. apply H. reflexivity.
- simpl. unfold bernoulli, pchoice. rewrite int_adds_val.
  repeat rewrite int_scales_val. repeat rewrite int_dirac.
  rewrite IHn.
  assert ((binomial p n) (fun x : nat => k = S x) = 0).
  pose proof (Lt.S_pred _ _ H).
  rewrite (val_iff (Q:= eq (pred k))).
  apply IHn. unfold Peano.lt in *. rewrite H0 in H. apply le_S_n.
  assumption. 
  intros. split; intros. rewrite H1. simpl. reflexivity.
  rewrite H0. congruence. rewrite H0. ring.
  apply Lt.lt_S_n. apply Lt.lt_S. assumption.
Qed.

Require Import alea.BinCoeff.

(** Characterization of the probability mass function of the [binomial]
    distribution in the usual manner. *)
Theorem binomial_pdf (p : Qnn) 
  (n : nat) (k : nat) :
  (k <= n)%nat -> (p <= 1)%Qnn ->
    (binomial p n) (eq k)
  = LPRQnn (Qnnnat (comb k n)
    * p ^ k * (1 - p) ^ (n - k))%Qnn.
Proof. generalize dependent k.
induction n.
- intros. apply Le.le_n_0_eq in H. subst. simpl.
  rewrite LPRind_true by reflexivity.
  apply LPRQnn_eq. ring.
- intros k. induction k; intros.
  + simpl. specialize (IHn 0%nat (Le.le_0_n _)).
    rewrite comb_0_n in IHn. simpl in IHn.
    rewrite <- Minus.minus_n_O in IHn.
    replace 
     (((1 + 0) * 1 * ((1 - p) * (1 - p) ^ n))%Qnn)
     with
     ((1 - p) * ((1 + 0) * 1 * ((1 - p) ^ n)))%Qnn
     by ring.
    rewrite <- LPRQnn_mult. rewrite <- IHn. unfold bernoulli.
    unfold pchoice.
    rewrite int_adds_val. do 2 rewrite int_scales_val.
    simpl. do 2 rewrite int_dirac.
    replace ((binomial p n) (fun x : nat => 0%nat = S x))
    with 0. replace (fun x : nat => 0%nat = x) with (eq 0%nat)
     by (extensionality a; reflexivity). 
    ring. erewrite val_iff. symmetry. apply strict.
    unfold K. intuition. assumption.
  + simpl. unfold bernoulli. unfold pchoice.
    rewrite int_adds_val. do 2 rewrite int_scales_val. 
    simpl. do 2 rewrite int_dirac. 
    rewrite (val_iff (Q := eq k)).
    specialize (IHk (Le.le_Sn_le _ _ H)).
    pose proof (IHn k (le_S_n _ _ H)).
    rewrite H1 by assumption.
    destruct (Compare_dec.le_dec (S k) n).
    * specialize (IHn (S k) l). 
      replace (fun x : nat => S k = x) with (eq (S k))
       by (extensionality a; reflexivity).
      rewrite IHn. simpl. repeat rewrite LPRQnn_mult.
      rewrite LPRQnn_plus. apply LPRQnn_eq. 
      pose proof (@Qnnminus_plus p 1%Qnn H0).
      rewrite Qnnnat_plus.
      replace ((1 - p) ^ (n - k))%Qnn
      with    ((1 - p) * (1 - p) ^ (n - S k))%Qnn.
      ring.
      rewrite <- (@minus_Succ k n) by assumption.
      simpl. reflexivity. assumption.
    * assert (k = n). apply Le.le_antisym. apply le_S_n. assumption.
      fold (lt k n) in n0. destruct (Lt.le_or_lt n k). assumption.
      contradiction. subst. repeat rewrite comb_n_n.
      repeat rewrite comb_Sn_n.
      replace ((binomial p n) (fun x : nat => S n = x)) with (LPRQnn 0%Qnn).
      repeat rewrite LPRQnn_mult. repeat rewrite LPRQnn_plus.
      apply LPRQnn_eq. simpl. ring.
      symmetry. apply binomial_bounded. apply Lt.lt_n_Sn.
    * intros. split; congruence.
Qed.

(** The functional that generates the geometric distribution. *)
Definition geoFix (p : Qnn) (f : Valuation nat) : Valuation nat 
  := pchoice p (map S f) (unit 0%nat).

Ltac simplVal := repeat 
  (rewrite int_adds_val || rewrite int_scales_val || rewrite int_dirac).

Lemma geoFixmono { p : Qnn } :
  (forall u v : Valuation nat,
      (u <= v)%Val -> (geoFix p u <= geoFix p v)%Val).
Proof. intros.
       unfold Valle. intros P. simpl.
       unfold bernoulli, pchoice. simplVal.
       apply LPRplus_le_compat;
         (apply LPRmult_le_compat; (reflexivity || apply H)).
Qed.

Definition geometric (p : Qnn) : Valuation nat :=
  fixValuation (geoFix p) geoFixmono.

Lemma geoFixContinuous : forall (p : Qnn), Continuous (geoFix p).
Proof.
intros p. unfold Continuous. intros.
simpl. rewrite (LPRsup_sum_jlat I).
repeat (rewrite <- LPRsup_scales).
rewrite LPRsup_constant. ring. assumption. intros.
apply LPRmult_le_compat. reflexivity. apply gmono. assumption.
intros. reflexivity.
Qed.

Lemma geometricInvariant (p : Qnn) :
  geometric p = geoFix p (geometric p).
Proof.
unfold geometric. symmetry.
apply fixValuation_fixed. apply geoFixContinuous.
Qed.

Ltac LPRQnn_simpl := 
  repeat (rewrite LPRQnn_plus || rewrite LPRQnn_mult).

Lemma geoFixMeas' : forall (p : Qnn), (p <= 1)%Qnn -> forall n,
  ((fixn (geoFix p) n) (K True)) = LPRQnn (1 - p ^ n)%Qnn.
Proof.
intros. induction n.
- simpl. apply LPRQnn_eq.  apply Qnneq_prop. reflexivity.
- simpl. rewrite (@val_iff _ _ _ (K True)). rewrite IHn.
  unfold K. rewrite LPRind_true by trivial.
  LPRQnn_simpl. apply LPRQnn_eq. ring_simplify.
  rewrite Qnnminus_mult_distr by (auto using Qnnpow_le).
  replace (p * 1)%Qnn with p by ring.
  admit.
  unfold K. intuition.
Admitted.

Lemma geometric_prob (p : Qnn) : (p < 1)%Qnn -> geometric p (K True) = 1.
Proof.
intros. unfold geometric. simpl. 
rewrite (LPRsup_eq_pointwise _ _ (geoFixMeas' p (Qnnlt_le_weak H))).
apply Qnnpowsup. assumption.
Qed.

Lemma geometric_ContinuousV : forall (p : Qnn),
  ContinuousV (geometric p).
Proof.
intros. unfold geometric. apply fix_ContinuousV.
intros. unfold geoFix. apply pchoice_ContinuousV.
apply map_ContinuousV. assumption. apply unit_ContinuousV.
Qed.

  Ltac indicatorSolve := repeat match goal with
  | [ |- context[LPRindicator (?x = ?y)] ] =>
     rewrite LPRind_true by intuition
  | [ |- context[LPRindicator (?x = ?y)] ] =>
     rewrite LPRind_false by intuition
    || rewrite LPRind_false by congruence
  end.

Lemma geometric_pdf : forall (p : Qnn) (k : nat),
  geometric p (eq k) = LPRQnn ((1 - p) * p ^ k)%Qnn.
Proof.
intros. induction k.
- simpl. apply LPRsup_prop. intros n. induction n.
  + simpl. apply LPRzero_min.
  + simpl. replace ((fixn (geoFix p) n) (fun x : nat => 0%nat = S x))
    with 0. indicatorSolve. LPRQnn_simpl. apply LPRQnn_le.
    ring_simplify. apply Qnnle_refl.
    erewrite val_iff. symmetry. apply strict.
    intros. unfold K. split; congruence || contradiction.
  + exists 1%nat. simpl. indicatorSolve. LPRQnn_simpl. apply LPRQnn_le.
    replace ((p * 0) + _)%Qnn 
      with (1 - p)%Qnn by ring.
    ring_simplify. apply Qnnle_refl.
- remember geometric as geo.  simpl. 
  replace ((1 - p) * (p * p ^ k))%Qnn
    with (p * ((1 - p) * p ^ k))%Qnn by ring.
  rewrite <- LPRQnn_mult. rewrite <- IHk.
  rewrite Heqgeo. 
  rewrite geometricInvariant at 1. unfold geoFix, pchoice.
  simplVal. rewrite <- Heqgeo.
  simpl. indicatorSolve. ring_simplify.
  erewrite val_iff. reflexivity.
  intros; split; congruence.
Qed.

(** * Queues *)
(** The simple example about the Geom/Geom/1 queue from our meeting.
    Discrete-time setting. *)
Section Queues.
  
  (** Probability we add something to the queue in a unit of time. *)
  Variable lambda : Qnn.
  (** Probability we remove something from the queue in a unit of time. *)
  Variable mu : Qnn.
  Hypothesis mule1 : (mu <= 1)%Qnn.
  (** The probability of an addition must be strictly less than the
      probability of removing an item, if we want to reach a steady
      state. *)
  Hypothesis lambdaltmu : (lambda < mu)%Qnn.

  (** If the queue is nonempty, [u] is the probability that the
      queue will be longer (by 1) next time, and [d] is the probability
      that the queue will be shorter (by 1) next time. *)
  Definition u := (lambda * (1 - mu))%Qnn.
  Definition d := (mu * (1 - lambda))%Qnn.

  Lemma lambdale1 : (lambda <= 1)%Qnn.
  Proof. 
    apply Qnnlt_le_weak. eapply Qnnlt_le_trans; eassumption. 
  Qed.

  (** Probability distribution of something added to the queue. True if we
      have a new input, false otherwise. *)
  Definition newInput : Valuation bool := bernoulli lambda.

  (** Probability distribution of removing from the queue. True if we
      have a new output, false otherwise. *)
  Definition newOutput : Valuation bool := bernoulli mu.

  (** If the queue is currently of size [n], gives the probability
      distribution over the size of the queue next time. *)
  Definition transition (n : nat) : Valuation nat := 
  bind newInput (fun inp => 
   let inc := if inp then S else fun x => x in
   map inc (match n with
    | 0 => unit 0%nat
    | S n' => map (fun out : bool => if out then n' else n)
             newOutput
    end)).

  Fixpoint transition_pdf (n m : nat) : Qnn := (match n with
    | 0 => match m with
      | 0 => 1 - lambda
      | 1 => lambda
      | _ => 0
      end
    | 1 => match m with
      | 0 => d
      | 1 => lambda * mu + (1 - mu) * (1 - lambda)
      | 2 => u
      | _ => 0
      end
    | S (S n') => match m with
      | 0 => 0
      | S m' => transition_pdf (S n') m'
      end
    end)%Qnn.

  Ltac indicatorReduce := repeat match goal with
  | [ |- context[LPRindicator (S ?x = S ?y)] ] =>
     rewrite (LPRind_iff _ (x = y)) by intuition
  end.

  Lemma transition_pdf_ok : forall (n k : nat),
    transition n (eq k) = LPRQnn (transition_pdf n k).
  Proof. intros n. destruct n; intros. simpl.
  - destruct k; unfold newInput, bernoulli, pchoice.
    + simpl.
      simplVal. indicatorSolve. ring.
    + destruct k. simpl.
      simplVal. indicatorSolve. ring.
      induction k. simpl.
      simplVal. indicatorSolve. ring. simpl.
      simplVal. indicatorSolve.
      ring.
  - generalize dependent k. induction n.
    + intros k. simpl. unfold newInput, bernoulli, pchoice. destruct k.
      * simpl. simplVal.
        indicatorSolve. ring_simplify. unfold d. LPRQnn_simpl. ring.
      * destruct k. simpl. simplVal.
        indicatorSolve. ring_simplify. LPRQnn_simpl. reflexivity.
        destruct k. simpl. simplVal. indicatorSolve.
        ring_simplify. unfold u. LPRQnn_simpl. reflexivity.
        simpl. simplVal. indicatorSolve. ring.
    + intros k. induction k. 
      * simpl. unfold newInput, bernoulli, pchoice. simplVal.
        indicatorSolve. ring.
      * simpl. rewrite <- IHn. simpl.
        unfold newInput, bernoulli, pchoice. simplVal.
        indicatorReduce.
        rewrite (LPRind_iff (S k = S (S (S n)))  (k = S (S n))) by intuition.
        rewrite (LPRind_iff (S k = S n) (k = n)) by intuition.
        ring.
   Qed.

  Lemma transition_localized : forall (nu : Valuation nat) (k : nat),
    (bind nu transition) (eq k) = (match k with
      | 0 => 0 | S k' => LPRQnn (transition_pdf k' k) * nu (eq k') end) 
      + LPRQnn (transition_pdf k k) * nu (eq k)
      + LPRQnn (transition_pdf (S k) k) * nu (eq (S k)).
  Proof. intros. simpl. erewrite fubini_no_funext.
  Focus 2. reflexivity.
  Focus 3. reflexivity.
  Focus 2. reflexivity.
  unfold newInput, bernoulli, pchoice. simplVal. destruct k.
  - replace 
(fun a : nat =>
      match a with
      | 0 => unit 0%nat
      | S n' => map (fun out : bool => if out then n' else a) newOutput
      end (fun x : nat => 0%nat = S x))
 with (fun _ : nat => 0 * 1).
    rewrite <- int_scales. ring_simplify.
    rewrite (nat_char nu) at 1. simpl. unfold build_nat.
     simpl.
  
simpl. 
  Abort.

  Lemma transition_ContinuousV : forall n : nat,
    ContinuousV (transition n).
  Proof.
  intros. unfold transition, newInput, newOutput. 
  apply bind_ContinuousV. apply bernoulli_ContinuousV.
  intros b. apply map_ContinuousV. destruct n.
  - apply unit_ContinuousV.
  - apply map_ContinuousV. apply bernoulli_ContinuousV.
  Qed.

  (** [rho] is the "workload" of the queue. *)
  Definition rho := (u / d)%Qnn.

  Lemma rholt1 : (rho < 1)%Qnn.
  Proof. 
  Admitted.

  (** From doing the algebra by hand, I think this is what the steady
      state of the queue should be. *)
  Definition steadyState : Valuation nat :=
   pchoice (lambda / mu) (map S (geometric rho)) (unit 0%nat).

  Lemma steadyState_ContinuousV : ContinuousV steadyState.
  Proof. 
  unfold steadyState. apply pchoice_ContinuousV.
  apply map_ContinuousV. apply geometric_ContinuousV.
  apply unit_ContinuousV.
  Qed.

  Ltac condSolve P :=   repeat match goal with
  | [ |- context[LPRindicator (P /\ 0%nat = S ?x) ] ] => 
    rewrite (@LPRind_false (P /\ 0%nat = S x)) by intuition
  | [ |- context[LPRindicator (P /\ 0%nat = 0%nat) ] ] => 
    rewrite (@LPRind_iff (P /\ 0%nat = 0%nat) P) by intuition
  end.

  Lemma rho_mu_lambda :((1 - rho) * mu * (1 - lambda) = mu - lambda)%Qnn.
  Proof. unfold rho, u, d.
  Admitted.

  (** Is my claimed steady state in fact the steady state on queue size?
      This theorem states that taking a [transition] from the [steadyState]
      leaves us in the [steadyState]. *)
  Theorem steadyState_is_steady :
   bind steadyState transition = steadyState.
  Proof.
  apply nat_dec. apply bind_ContinuousV. apply steadyState_ContinuousV.
  apply transition_ContinuousV. apply steadyState_ContinuousV.
  intros. destruct n. 
  remember transition as trns.
  simpl.
  replace (LPRsup
     (fun i : nat => (fixn (geoFix rho) i) (fun x : nat => 0%nat = S x))) with 0.
  ring_simplify.
  unfold steadyState, pchoice. simplVal.
  rewrite <- change_of_variables.
  rewrite geometricInvariant. unfold geoFix. 
  unfold pchoice. simplVal. rewrite <- change_of_variables.
  replace (integral
      (fun x : nat => (trns (S (S x))) (eq 0%nat))
      (geometric rho)) with 0.
  rewrite Heqtrns. simpl.
  unfold newInput, bernoulli, pchoice.
  simplVal. ring_simplify.
  LPRQnn_simpl.
  replace (lambda / mu * (1 - rho) * mu * (1 - lambda))%Qnn
  with (lambda / mu * ((1 - rho) * mu * (1 - lambda)))%Qnn by ring.
  rewrite rho_mu_lambda.
  indicatorSolve. ring_simplify.
  admit.

  replace 0 with (0 * 1). rewrite <- (geometric_prob rho).
  rewrite <- int_indicator.
  rewrite int_scales.
  apply int_pointwise_eq. unfold pointwise.
  intros.
  rewrite Heqtrns.
  simpl. unfold newInput, bernoulli, pchoice. simplVal.
  unfold K. indicatorSolve. ring.
  apply rholt1. ring.
  rewrite (LPRsup_eq_pointwise _ (fun _ => 0)).
  symmetry. apply LPRsup_constant. exact 0%nat.
  intros n. induction n; simpl. reflexivity.
  assert (forall z, (fun x : nat => 0%nat = S (S x)) z <-> (K False) z).
  unfold K. intuition.
  rewrite (val_iff H). rewrite strict. indicatorSolve. ring.


  unfold steadyState. unfold pchoice. remember (geometric rho) as geo.
  remember transition as trns.
  simpl. indicatorSolve. ring_simplify.
  simplVal.
  replace (geo (fun x : nat => S n = S x)) with (geo (eq n)).
  Focus 2. apply val_iff. intros; split; congruence.
  rewrite <- change_of_variables.

  induction n.
  - rewrite Heqgeo. rewrite geometricInvariant.
    unfold geoFix, pchoice. simplVal. rewrite <- Heqgeo. simpl.
    indicatorSolve. ring_simplify.
    rewrite <- change_of_variables.
    replace (geo (fun x : nat => 0%nat = S x)) with 0.
    Focus 2. erewrite val_iff. symmetry. apply strict. unfold K.
      intros; split; congruence || contradiction.
    ring_simplify.
    rewrite Heqgeo. rewrite geometricInvariant.
    unfold geoFix, pchoice. simplVal.
    rewrite <- Heqgeo. rewrite <- change_of_variables.
    replace (integral (fun x : nat => (trns (S (S (S x)))) (eq 1%nat)) geo)
      with 0 by admit.
    ring_simplify.
    admit.
  - admit.
  Abort. 
  

End Queues.