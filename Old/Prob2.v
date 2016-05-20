Require Import Reals.Reals Streams.

(** the Cantor space; an infinite stream of coinflips *)
Definition Dyad := Stream bool.

(** constant zeros *)
CoFixpoint zero : Dyad :=
  Cons false zero.

(** constant ones *)
CoFixpoint one : Dyad :=
  Cons true one.

CoFixpoint split1 (d : Dyad) : Dyad :=
  match d with 
   | Cons b1 (Cons b2 d') => Cons b1 (split1 d')
  end.

CoFixpoint split2 (d : Dyad) : Dyad :=
  match d with 
   | Cons b1 (Cons b2 d') => Cons b2 (split2 d')
  end.

(** split one stream into two by alternation *)
Definition split (d : Dyad) : Dyad * Dyad :=
  (split1 d, split2 d).

(** a probability distribution on the type [A] *)
Definition prob A := Dyad -> A.

(** a single coinflip *)
Definition coinflip : prob bool :=
  fun d => match d with Cons b _ => b end.

(** [prob A] forms a monad in a sense. The laws don't hold "on the nose"; 
    rather, the laws should hold modulo the set of probabilistic
    statements that we can make *)
Definition unit {A} (x : A) : prob A := fun _ => x.

Definition bind {A B} (p : prob A) (f : A -> prob B) : prob B := fun d =>
  let (d1, d2) := split d in
  f (p d1) d2.

Definition bind_dep {A B} (p : prob A) (f : forall (x : A), prob (B x))
  : prob (sigT B) := fun d => let (d1, d2) := split d in let x := p d1 in
  existT B x (f x d2). 

(** map a function over a distribution *)
Definition pmap {A B : Set} (f : A -> B) (p : prob A) : prob B
  := fun d => f (p d).

(** combine two independent distributions *)
Definition ptimes {A B : Set} (pA : prob A) (pB : prob B) : prob (A * B)
  := bind pA (fun a => pmap (fun b => (a, b)) pB).

Example interval : prob Dyad := fun d => d.

Example square : prob (Dyad * Dyad) :=
  bind interval (fun x => bind interval (fun y => unit (x, y))).

(** the coinductive version of natural numbers, meaning that we have infinity
    as the stream of endless [CoS]s. *)
CoInductive CoNat : Set :=
  | Co0 : CoNat
  | CoS : CoNat -> CoNat.

(** The geometric distribution: flip coins until we get heads, and return
    the number of coins it took until we got a heads. It is perfectly natural
    here to use the conatural numbers, since it *could* potentially go on
    forever. *)
CoFixpoint geometric (d : Dyad) : CoNat := 
   match d with
   | Cons true d' => CoS (geometric d')
   | Cons false _ => Co0
   end.

(** A [Partial A] may never actually return a value of type [A], instead
    always choosing [Later] *)
CoInductive Partial {A} : Type :=
  | Later : Partial -> Partial
  | Now   : A -> Partial
.
Arguments Partial : clear implicits.

(** Partial computations form a monad *)
CoFixpoint partialbind {A B} (m : Partial A) (f : A -> Partial B) : Partial B :=
  match m with
  | Now x => f x
  | Later m' => Later (partialbind m' f)
end.

(** If [p] is a number between 0 and 1 represented by its binary expansion,
    then [bernoulli p] is a Bernoulli trial returning [true] with probability
    [p]. Here we need to use [Partial], because if our input random stream [d]
    is exactly our probability [p], we will never decide whether to return
    [true] or [false]. *)
CoFixpoint bernoulli (p : Dyad) : prob (Partial bool) := fun d => match p, d with
  Cons bp p', Cons bd d' => match bp, bd with
    | true , false => Now true
    | false, true  => Now false
    | _, _ => Later (bernoulli p' d')
    end
  end.

(** An example which shows how we can define more complex probability
    distributions using simpler ones. *)
Example conditionalExample : prob (Dyad * Partial bool) :=
  bind interval (fun x => 
  bind (bernoulli x) (fun y => 
  unit (x, y)
  )).

(** If we view a probability distribution on [A] as an infinitely branching
    binary tree, then [go true] descends into one branch, and [go false]
    descends into the other. *)
Definition go {A} (b : bool) (dist : prob A) (d : Dyad) : A := dist (Cons b d).

CoInductive PTree {A} {dist : prob A} {P : A -> Prop} : Type :=
  | LeafNone : PTree
  | LeafUnit : (forall d, P (dist d)) -> PTree
  | Branch   : @PTree _ (go true dist) P -> @PTree _ (go false dist) P
             -> PTree.

Arguments PTree {A} dist P.

CoFixpoint broken {A} {P : A -> Prop} (dist : prob A) :
  PTree dist P := Branch (broken (go true dist)) (broken (go false dist)).

Fixpoint pow2 (e : nat) : positive := match e with
  | 0 => 1%positive
  | S e' => xO (pow2 e')
  end.

Fixpoint measCount {A} {dist : prob A} {P : A -> Prop}
  (tree : PTree dist P) (depth : nat) : N := match depth with
  | 0 => 0%N
  | S depth' => match tree with
    | LeafNone => 0%N
    | LeafUnit _ => Npos (pow2 depth')
    | Branch x y => (measCount x depth' + measCount y depth')%N
    end
  end.

Require Import QArith.
Local Open Scope nat.

(** An increasing sequence of rational numbers for which we know that
    [P] holds with at least that probability. *)
Definition meas {A} {dist : prob A} {P : A -> Prop}
  (tree : PTree dist P) : nat -> Q := fun depth =>
  (NtoZ (measCount tree depth) # pow2 depth).

Inductive Meas {A} (dA : prob A) (P : A -> Prop) (x : Q) :=
  | MkMeas : forall (n : nat) (tree : PTree dA P), (x >= meas tree n)%Q -> Meas dA P x.

Fixpoint toCoNat (n : nat) : CoNat := match n with
  | 0 => Co0
  | S n' => CoS (toCoNat n')
  end.

(** force reduction of [CoNat]s, which is useful for proofs *)
Definition unfold_CoNat (n : CoNat) : n = match n with
  | Co0 => Co0
  | CoS s' => CoS s'
  end := 
  match n as s return (s = match s with | Co0 => Co0 | CoS s' => CoS s' end) with
  | Co0 => eq_refl
  | CoS n' => eq_refl
  end.

(** If, in every possible world, [P] implies [Q], then if we know that
    [P] holds with probability [c], then so does [Q]. *)

CoFixpoint probImpl {A} {dA : prob A} {PA : A -> Prop}
  (tree : PTree dA PA) {B} {dB : prob B} {PB : B -> Prop}
    (impl : forall d, PA (dA d) -> PB (dB d)) : PTree dB PB := match tree with
  | LeafNone => LeafNone
  | LeafUnit f => LeafUnit (fun x => impl x (f x))
  | Branch x y => Branch 
     (probImpl x (fun d => impl (Cons true d))) 
     (probImpl y (fun d => impl (Cons false d)))
  end.

Fixpoint geometricProp' (n : nat) : PTree geometric (fun x => x = toCoNat n).
Proof. induction n.
- apply Branch. apply LeafNone. 
  apply LeafUnit. simpl. intros d. unfold go.
  rewrite (unfold_CoNat (geometric (Cons _ d))). simpl.
  reflexivity.
- apply Branch.
  apply (@probImpl _ geometric (fun x => x = toCoNat n)).
  apply IHn.
  intros d H. unfold go. simpl.
   rewrite (unfold_CoNat (geometric (Cons true d))). simpl.
   rewrite H. reflexivity.
  apply LeafNone.
Qed.

(** An inductive proof of the probability that the geometric distribution
    results in any given natural number. *)
Theorem geometricProp (n : nat) 
  : Meas geometric (fun x => x = toCoNat n) ((1 / 2) ^ (S n)).
Proof.
induction n.
- simpl. eapply MeasCombine.
  + unfold go. apply MeasNone.
  + apply MeasUnit. intro d. unfold go.
    rewrite (unfold_CoNat (geometric (Cons false d))).
    reflexivity.
  + field.
- eapply MeasCombine. eapply probImpl.
  eassumption.
  intro d. destruct d. intro H.
  rewrite (unfold_CoNat (go true geometric (Cons b d))).
  simpl. rewrite H. reflexivity.
  apply MeasNone.
  simpl. field.
Qed. 


Lemma bindGoProp {A B : Set} (pA : prob A) (b c : bool)
  (f : A -> prob B)
  (d : Dyad) :
  bind pA f (Cons b (Cons c d))
  = 
  bind (go b pA) (fun a => go c (f a)) d. 
Proof.
unfold go. unfold bind. simpl.
rewrite (unfold_Stream (split1 (Cons b (Cons c d)))).
simpl.
rewrite (unfold_Stream (split2 (Cons b (Cons c d)))).
simpl.
reflexivity.
Qed.

(* Almost identical proof to the one above; let's fix that eventually. *)
Lemma ptimesProp {A B : Set} (pA : prob A) (pB : prob B) (b c : bool)
  (d : Dyad) :
  ptimes (go b pA) (go c pB) d = go c (go b (ptimes pA pB)) d.
Proof.
unfold go. unfold ptimes. unfold pmap. unfold bind. simpl.
rewrite (unfold_Stream (split1 (Cons b (Cons c d)))).
simpl.
rewrite (unfold_Stream (split2 (Cons b (Cons c d)))).
simpl.
reflexivity.
Qed.


Require Import FunctionalExtensionality.

(** Here we prove that if we combine independent probability distributions,
    the probabilities of the original distributions do not change. *)
Theorem independentP {A : Set} (pA : prob A) {PA : A -> Prop} 
  : forall {c : R}, 
  Meas pA PA c ->
  forall {B : Set} (pB : prob B), Meas (ptimes pA pB) (fun x => PA (fst x)) c.
Proof.
intros c measA.
induction measA; intros B pB. 
- apply MeasNone.
- apply MeasUnit. intro d. 
  simpl. apply H.
- apply MeasCombine with a b;
  [ eapply MeasCombine with a a
  | eapply MeasCombine with b b
  | assumption
  ];
  simpl; try field ||
     (pose proof (ptimesProp dist pB);
      apply functional_extensionality in H0;
      rewrite <- H0
    ); (apply IHmeasA1) || (apply IHmeasA2).
Qed.

Ltac measNone := match goal with
       | [  |- Meas _ _ 0%R ] => apply MeasNone
       | [  |- _ = _ ] => try field
       end.

Example intervalProp : Meas interval (fun d => exists d', d = Cons true (Cons false d')) (1 / 4)%R.
Proof.
apply MeasCombine with (1/2)%R 0%R; try measNone.
apply MeasCombine with 0%R 1%R; try measNone.
apply MeasUnit. intros d. eexists.
match goal with
| [  |- ?x = ?y ] => rewrite (unfold_Stream x)
end.
simpl.
reflexivity.
Qed.

(** It's a work in progress from here on out! *)


(*
Fixpoint interleave {A B pA pB PA PB a b} (x : bool) 
  (mA : Meas pA PA a) (mB : Meas pB PB b) := if x then 
  match mA with
  | MeasNone => MeasNone
  | MeasUnit prop => interleave false (MeasUnit _) mB
  | MeasCombine _ _ _ mA1 mA2 _  => MeasCombine
     (interleave false mA1 mB) (interleave false mA2 mB)
  end
  else
  match mB with
  | MeasNone => MeasNone
  | MeasUnit prop => interleave true mA (MeasUnit _)
  | MeasCombine _ _ _ mB1 mB2 _  => MeasCombine
    (interleave true mA mB1) (interleave true mA mB2)
  end.
*)

Theorem independentP' {A : Set} (pA : prob A) {PA : A -> Prop} 
  : forall {c : R}
  , Meas pA PA c ->
  forall {B : Set} (pB : prob B) (PB : B -> Prop) {c' : R}
  , Meas pB PB c' -> Meas (ptimes pA pB) (fun x => PA (fst x) /\ PB (snd x)) (c * c').
Proof.
intros c measA.
induction measA; intros B pB PB c' measB. 
- assert ((0 * c')%R = 0%R). field. rewrite H. apply MeasNone.
- assert ((1 * c')%R = c'%R). field. rewrite H0.
  induction measB.
  + apply MeasNone.
  + apply MeasUnit. intro d. split. apply H. apply H1.
Abort.

(** Here we begin an example of a very stupid approximate primality test. *)

Fixpoint coNatToNat (max : nat) (n : CoNat) := match max, n with
  | 0, _ => 0
  | _, Co0 => 0
  | S max', CoS n' => S (coNatToNat max' n')
  end.

Definition divide (x y: nat) := exists z, x * z = y.
Definition prime x := forall y, divide y x -> {y = 1} + {y = x}.
Definition notPrime x := exists y, (divide y x * (y <> 1) * (y <> x))%type.

Lemma notPrime_ok : forall (p : nat), notPrime p -> prime p -> False.
Proof. intros. unfold notPrime in *. unfold prime in *.
destruct H. destruct H. destruct p0. 
pose proof (H0 x d).
destruct H; contradiction.
Qed.

Theorem divide_dec (x y : nat) : {divide x y} + {~ (divide x y)}.
Admitted.

Theorem prime_test_helper (p : nat) (k : nat) : option (prime p -> False).
Proof.
refine (
 if divide_dec k p
   then if eq_nat_dec k 1
     then None
     else if eq_nat_dec k p
       then None
       else Some _
   else None
). 
intro isPrime. apply isPrime in _H.
destruct _H; auto.
Defined. 

Fixpoint prime_test (p : nat) (n : nat) : prob (option (prime p -> False)) :=
  match n with
  | 0 => unit None
  | S n' => bind (pmap (coNatToNat p) geometric)
     (fun k => match prime_test_helper p k with
       | None => prime_test p n'
       | Some contra => unit (Some contra)
       end)
  end.

Definition isSome {A} (x : option A) : Prop := match x with
  | Some x' => True
  | None => False
  end.

Theorem probConsistent {A : Set} (dist : prob A)
  (P : A -> Prop)
  : forall {c : R}, Meas dist P c -> (c > 0)%R
  -> exists x, P (dist x).
Proof.
intros c meas cnonzero.
induction meas.
- pose proof (Rgt_asym _ _ cnonzero). contradiction.
- exists zero. apply H.
- assert ((a > 0)%R \/ (b > 0)%R).
  + admit.
  + unfold go in *. destruct H0.
    * apply IHmeas1 in H0. destruct H0. exists (Cons true  x). apply H0.
    * apply IHmeas2 in H0. destruct H0. exists (Cons false x). apply H0.
Qed.

Theorem prime_test_ok (p : nat) :
  prime p -> forall (n : nat) {c : R},
  Meas (prime_test p n) isSome c 
  -> ~ (c > 0)%R.
Proof.
intros. unfold not. intro contra.
pose proof (probConsistent (prime_test p n) _ H0 contra).
destruct H1.
destruct (prime_test p n x); contradiction.
Qed.

Theorem prime_test_productive (p : nat) :
  notPrime p -> p >= 3 -> forall (n : nat), exists (c : R), 
  (Meas (prime_test p (S n)) isSome c /\ (c > 0)%R).
Proof.
intros. destruct H as [H1 [[H2 H3] H4]].
eexists.
Abort.

Theorem bindProp {A B : Set} (dist : prob A) (P : A -> Prop)
  : forall {c : R}, Meas dist P c
  -> forall (f : A -> prob B) (Q : B -> Prop) {c' : R}
  , (forall x, P x -> Meas (f x) Q c')
  -> Meas (bind dist f) Q (c * c')%R.
Proof.
intros c meas.
induction meas; intros.
- assert ((0 * c')%R = 0%R). field. 
  rewrite H0. apply MeasNone.
- assert ((1 * c')%R = c'%R). field.
  rewrite H1. unfold bind. (* apply MeasUnit. *)
Abort.

Inductive Sim {A : Set} : Stream A -> Stream A -> nat -> Prop :=
  | Sim0 : forall {s t}, Sim s t 0
  | SimS : forall {x y} {s t} {n}, x = y -> Sim s t n -> Sim (Cons x s) (Cons y t) (S n).

Definition uniformlyCont {A : Set} (f : prob A) (n : nat) :=
  forall (s t : Dyad), Sim s t n -> f s = f t.

(* This, as stated is wrong *)
Axiom allFuncsContinuous : forall {A : Set} (f : prob A),
  exists (n : nat), uniformlyCont f n.

Lemma lessenCont {A : Set} {f : prob A} {b : bool} {n : nat}
  : uniformlyCont f (S n) -> uniformlyCont (go b f) n.
Proof.
intros H.
unfold uniformlyCont in *.
intros s t simst.
unfold go. simpl.
specialize (H (Cons b s) (Cons b t)).
apply H. constructor. reflexivity. assumption.
Qed.


Lemma splitNull {A B : Set}
  (dA : prob A) (dB : prob B) (P : B -> Prop)
  {c : R}
  :  Meas dB P c
  -> Meas (bind dA (fun _ => dB)) P c.
Proof.
unfold bind. simpl. intros meas.
induction meas.
- apply MeasNone.
- apply MeasCombine with (a := 1%R) (b := 1%R);
    try (apply MeasUnit; intros d; unfold go; destruct d;
     rewrite (unfold_Stream (split2 (Cons _ (Cons _ d))));
     simpl; apply H).
    field.
- eapply MeasCombine with c c;
   [ eapply MeasCombine with a b
   | eapply MeasCombine with a b
   | field ]; try assumption;
   try (clear meas1 meas2;
   match goal with
   | [ IH : Meas ?f P ?a |- Meas ?g P ?a ] => assert (Hfg : f = g);
       [ apply functional_extensionality; intros x;
         unfold go;
         rewrite (unfold_Stream (split2 (Cons _ (Cons _ x))));
         simpl; reflexivity
       | rewrite <- Hfg; assumption ]
   end).
Qed.
  
(*
Lemma continuousProb {A B : Set} (P : B -> Prop)
  {n : nat}
  : forall
  {c : R}
  (dA : prob A)
  (f : A -> prob B)
  (fcont : uniformlyCont (bind dA f) n)
  (H0 : forall (x : A), Meas (f x) P c)
  , Meas (bind dA f) P c.
Proof.
induction n; intros.
- assert (bind dA f = fun _ => f (dA zero) zero).
  apply functional_extensionality. unfold uniformlyCont in fcont.
  intros x. assert (bind dA f zero = f (dA zero) zero). unfold bind.
  simpl. admit.
  rewrite <-  H. apply fcont. constructor. 
  rewrite H. admit.
- apply MeasCombine with c c; try (solve[field]);
   apply MeasCombine with c c; try (solve[field]).
  + match goal with
    | [ |- Meas (go ?b (go ?c (bind dA f))) _ _ ] => 
       assert (Hfe : go b (go c (bind dA f)) = bind (go b dA) (fun a => go c (f a)));
       [ apply functional_extensionality; intros d;
         apply bindGoProp
       | rewrite Hfe
       ]
    end.
   apply IHn. unfold uniformlyCont. intros s t simst.
   unfold go. apply functional_extensionality. intros x.
   assert (f (dA (Cons true s)) = f (dA (Cons true t))).
   unfold uniformlyCont in fcont. apply fcont. constructor.
   reflexivity. assumption. rewrite H. reflexivity. 
   intros x.
   unfold go. simpl.
*)

Theorem bindProp' {A B : Set} (dist : prob A)
  (f : A -> prob B) (P : B -> Prop) {c : R}
  : (forall x, Meas (f x) P c)
  -> Meas (bind dist f) P c.
Proof.
intros.
unfold bind.
pose (contF := fun d => H (dist d)).
(* assert (exists n, UniformCont contF n). *)
Abort.


Theorem condProb : forall {U : Set} {dist : prob U } 
  {A B : U -> Prop} {x y z : R},
    Meas dist A x
  -> Meas dist B y
  -> (forall (u : U),  {~(A u)} + {~(B u)})
  -> (x + y)%R = z
  -> Meas dist (pAnd A B) z.
Proof.
intros. induction H.
Abort.








(*
CoInductive Label : Set :=
 | Zero : Label
 | One : Label
 | Mix : Label -> Label -> Label.

CoInductive CL : Label -> Label -> Set :=
  | CL01 : CL Zero One
  | CL10 : CL One Zero
  | CL0M : forall {x y}, CL x y -> CL Zero (Mix x y)
  | CLM0 : forall {x y}, CL x y -> CL (Mix x y) Zero
  | CL1M : forall {x y}, CL x y -> CL One (Mix x y)
  | CLM1 : forall {x y}, CL x y -> CL (Mix x y) One
  | CLMM : forall {x y a b}, CL x y -> CL a b -> CL (Mix x y) (Mix a b).

Definition frob (l : Label) : Label :=
  match l with
    | Zero => Zero
    | One => One
    | Mix a b => Mix a b
  end.

Theorem frob_eq : forall (l : Label), l = frob l.
  destruct l; reflexivity.
Qed.

CoFixpoint geoL : Label := Mix Zero geoL.

CoFixpoint geoCL : CL Zero geoL. 
Proof. rewrite frob_eq. simpl. apply CL0M. apply geoCL.
Qed.

CoFixpoint loopL : Label := Mix loopL loopL.
CoFixpoint loopCL : CL loopL loopL.
Proof. rewrite (frob_eq loopL). simpl. apply CLMM; assumption.
Qed.
*)