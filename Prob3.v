Require Import QArith.

(** In the comments here, I seem to use the words "measure" and
    "valuation" interchangably. Sorry! *)

Definition konst {A} (x : A) {B} (y : B) := x.

Record Valuation {A : Type} :=
  { val       : (A -> Prop) -> Q -> Prop 
  ; zeroed    : forall P, exists q, val P q /\ q == 0
  ; strict    : forall q, val (konst False) q -> q == 0%Q
  ; monotonic : forall (U : A -> Prop) q, val U q -> forall (V : A -> Prop), (forall z, U z -> V z) 
              -> val V q
  ; modular1  : forall {U V x y}, val U x -> val V y
              -> exists a b, val (fun z => U z /\ V z) a
                     /\ val (fun z => U z \/ V z) b
                     /\ a + b == x + y
  ; modular2  : forall {U V x y}, val (fun z => U z /\ V z) x 
                         -> val (fun z => U z \/ V z) y
              -> exists a b, val U a /\ val V b
                     /\ a + b == x + y
  }.

Arguments Valuation : clear implicits.

(* A Dirac delta measure *)
Inductive unitProb {A} (a : A) (P : A -> Prop) : Q -> Prop :=
  | Unit1 : P a -> unitProb a P 1
  | Unit0 : unitProb a P 0.

Ltac proveUnit := 
match goal with
| [ H: unitProb _ _ _ |- _ ] => induction H
| [ |- unitProb _ _ 0 ] => eapply Unit0
| [ |- unitProb _ _ 1 ] => eapply Unit1
| [ |- _ /\ _ ] => split
| [ H : ?U ?x |- exists a b : Q, unitProb ?x ?U a /\ _ ] => exists 1 
| [ |- _ ] => reflexivity || firstorder
end.

(* The Dirac delta meets all the properties of being a Valuation.
   It will become the unit of our monad! *)
Definition unit {A : Type} (a : A) : Valuation A.
Proof. refine (
  {| val := unitProb a |}
); intros; repeat proveUnit.
exists 0. repeat proveUnit.
exists 1. exists 1. repeat proveUnit.
exists 0. exists 1. repeat proveUnit.
exists 0. exists 1. repeat proveUnit.
exists 0. exists 0. repeat proveUnit.
exists 1. repeat proveUnit.
exists 1. repeat proveUnit.
exists 0. repeat proveUnit.
exists 0. exists 1. repeat proveUnit.
exists 0. repeat proveUnit.
exists 0. exists 0. repeat proveUnit.
Defined.

(* Scale a valuation by a constant *)
Inductive scaledVal (q : Q)
  {A : Type} (Val : (A -> Prop) -> Q -> Prop) (P : A -> Prop) : Q -> Prop :=
  | Scale : forall a, Val P a -> scaledVal q Val P (q * a).

Definition scaled {A : Type} (q : Q) (Val : Valuation A) : Valuation A.
Proof. refine (
  {| val := scaledVal q (val Val) |}
); intros.
- pose proof (zeroed Val P). destruct H. destruct H.
  exists (q * x). split. constructor. assumption. rewrite H0. field.
- induction H. apply strict in H. rewrite H. field.
- induction H. constructor. eapply monotonic; eassumption.
- induction H; induction H0.
  pose proof (modular1 Val H H0).
  destruct H1 as [andq [orq [andp [orp eqs]]]].
  exists (q * andq). exists (q * orq).
  repeat split; try assumption.
  do 2 rewrite <- Qmult_plus_distr_r.
  rewrite eqs. reflexivity.
- induction H; induction H0.
  pose proof (modular2 Val H H0).
  destruct H1 as [Uq [Vq [Up [Vp eqs]]]].
  exists (q * Uq). exists (q * Vq).
  repeat split; try assumption.
  do 2 rewrite <- Qmult_plus_distr_r.
  rewrite eqs.
  reflexivity.
Defined.

(* Add two valuations together *)
Inductive addVal {A : Type}
  (ValL ValR : (A -> Prop) -> Q -> Prop) (P : A -> Prop) : Q -> Prop :=
  | Add : forall a b, ValL P a -> ValR P b -> addVal ValL ValR P (a + b).

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 == (andLq + orLq) + (andRq + orRq).
Proof. intros. field. Qed.


Definition add {A : Type} (ValL ValR : Valuation A) : Valuation A.
Proof. refine (
  {| val := addVal (val ValL) (val ValR) |}
); intros.
- pose proof (zeroed ValL P). pose proof (zeroed ValR P).
  destruct H; destruct H0. destruct H. destruct H0.
  exists (x + x0). split. constructor; assumption. rewrite H1. rewrite H2.
  field.
- induction H. apply strict in H. apply strict in H0.
  rewrite H. rewrite H0. reflexivity.
- induction H. constructor; eapply monotonic; eassumption.
- induction H; induction H0.
  pose proof (modular1 ValL H H0).
  pose proof (modular1 ValR H1 H2).
  destruct H3 as [andLq [orLq [andLp [orLp eqL]]]].
  destruct H4 as [andRq [orRq [andRp [orRp eqR]]]].
  exists (andLq + andRq).
  exists (orLq  + orRq).
  repeat split; try assumption.
  rewrite qredistribute.
  rewrite eqL. rewrite eqR.
  field.
- intros. induction H; induction H0.
  pose proof (modular2 ValL H H0).
  pose proof (modular2 ValR H1 H2).
  destruct H3 as [LUq [LVq [LUp [LVp eqL]]]].
  destruct H4 as [RUq [RVq [RUp [RVp eqR]]]].
  exists (LUq + RUq).
  exists (LVq + RVq).
  repeat split; try eassumption.
  rewrite qredistribute. rewrite eqL. rewrite eqR. field.
Defined.

(* Probabilistic choice. Take [ValL] with probability [p] and
   [ValR] with probability [1 - p] *)
Definition pchoice {A : Type} (p : Q) (ValL ValR : Valuation A) : Valuation A :=
  add (scaled p ValL) (scaled (1 - p) ValR).

Section SillyExample.
  (** This silly example demonstrates a case where measures simply will not do.
      Here we model the fact that there is a 1/2 probability we would like
      to believe in classical logic, and for the other 1/2 probability we make
      no additional assumptions over intuitionistic logic. *)

  Definition classical := forall (P : Prop), ~ ~ P -> P.

  Definition halfClassical : Valuation Prop :=
    pchoice (1 # 2) (unit True) (unit classical).

  Lemma classicalLEM : classical -> forall (P : Prop), P \/ ~ P.
  Proof.
  unfold classical. intros. apply H. firstorder. 
  Qed.

  (* Now, we ask about the probability that we should believe in the 
     limited principle of omniscience? We know we should believe it
     with probability at least 1/2, but don't know what to do with the other
     1/2 of our belief; since LPO is independent of intuitionistic logic,
     we are inevitably stuck with the remaining 1/2 mass in the "middle"!
  *)

  Definition probOmniscience : exists q, val halfClassical 
      (fun p => p -> forall (f : nat -> bool), (forall x, f x = true) \/ (exists x, f x = false)) q
    /\ q == 1 # 2.
  Proof. unfold halfClassical.
  unfold pchoice.
  simpl.
  eexists.
  econstructor. econstructor. econstructor.
  eapply Unit0.
  econstructor. eapply Unit1.
  intros.
  pose proof (classicalLEM H (forall (x : nat), f x = true)).
  destruct H0. left. assumption.
  right. apply H. unfold not. intros.
  apply H0. 
  intros.
  pose proof (classicalLEM H (f x = true)). destruct H2.
  assumption. destruct (f x) eqn:fx. reflexivity.
  apply False_rect. apply H1. exists x. assumption.
  field.
  Qed.

End SillyExample.

Require Import FunctionalExtensionality.


(* Pushforward of a measure, i.e., map a function over a measure *)
Definition map {A B : Type} (f : A -> B) (v : Valuation A)
  : Valuation B.
Proof. refine (
  {| val := fun prop => val v (fun x => prop (f x)) |}
); intros.
- pose proof (zeroed v (fun x => P (f x))). 
  destruct H. exists x. assumption.
- apply (strict v). assert ((fun x => konst False (f x)) = konst False).
  apply functional_extensionality. reflexivity.
  rewrite <- H0. assumption.
- apply (monotonic v) with (fun x => U (f x)). 
  intros. apply H. intros. apply H0. assumption.
- apply (modular1 v); assumption.
- apply (modular2 v); assumption.
Defined.

Require Import Streams.

Definition Cantor := Stream bool.

(** If we view a probability distribution on [A] as an infinitely branching
    binary tree, then [go true] descends into one branch, and [go false]
    descends into the other. *)
Definition go {B : Type} (b : bool) (dist : Cantor -> B) : Cantor -> B := 
  fun d => dist (Cons b d).

Inductive ValCantor : (Cantor -> Prop) -> Q -> Prop :=
  | VCNone : forall {P}, ValCantor P 0
  | VCUnit : forall {P : Cantor -> Prop}, (forall d, P d) -> ValCantor P 1
  | VCCombine : forall {P} {a b} (c : Q),
       ValCantor (go true  P) a
     -> ValCantor (go false P) b
     -> (a + b) == c * (2 # 1)
     -> ValCantor P c.

Lemma goKonst {A b} {x : A} : go b (konst x) = konst x.
Proof. apply functional_extensionality.
intros d. unfold go. reflexivity.
Qed.

Lemma cantorMonotonic : forall (U : Cantor -> Prop) q, ValCantor U q 
 -> forall (V : Cantor -> Prop), (forall z, U z -> V z) -> ValCantor V q.
Proof.
intros U q vc. induction vc; intros. constructor.
  constructor. intros d. apply H0. apply H.
  econstructor.
  apply IHvc1. unfold go. intros z. apply H0.
  apply IHvc2. unfold go. intros z. apply H0. assumption.
Qed.

(* This is supposed to say that the Haar measure on the Cantor space,
   i.e., the infinite sequence of coinflips, is a Valuation. However,
   it seems to be untrue because of the way I defined `ValCantor`.
   I think the definition could be saved if we reequired in `VCUnit`
   that the proof that the property holds for the entire space be
   continuous. *)
Definition cantor : Valuation Cantor.
Proof. refine (
  {| val := ValCantor |}
).
- intros. exists 0. split. constructor. reflexivity.
- intros. generalize H. 
  assert (forall P, P = konst False -> ValCantor P q -> q == 0).
  intros. induction H1. reflexivity.
  rewrite H0 in H1. contradiction (H1 (const true)).
  assert (a == 0). apply IHValCantor1.
  subst. rewrite goKonst in H1_. assumption.
  rewrite H0. rewrite goKonst. reflexivity.
  assert (b == 0). apply IHValCantor2.
  subst. rewrite goKonst in H1_0. assumption.
  rewrite H0. rewrite goKonst. reflexivity.
  rewrite H3 in H1. rewrite H2 in H1.
  eapply Qmult_integral_l.
  Focus 2. symmetry. rewrite Qmult_comm.
  eassumption.
  apply Qnot_eq_sym.
  apply Qlt_not_eq.
  firstorder.
  apply H0. reflexivity.
- apply cantorMonotonic.
- intros U V x y vcU. generalize dependent V. generalize dependent y. 
  induction vcU; intros.
  + exists 0. exists y. split. constructor. split. eapply cantorMonotonic.
  eassumption. firstorder. reflexivity.
  + exists y. exists 1. split. eapply cantorMonotonic. eassumption.
    firstorder. split. constructor. firstorder. field.
  + destruct H0.
    * exists 0. exists c. repeat split. constructor.
      econstructor.  eapply cantorMonotonic. apply vcU1.
      unfold go. intros. firstorder.
      eapply cantorMonotonic. apply vcU2.
      unfold go. intros. firstorder.
      assumption. field.
    * exists c. exists 1. repeat split. econstructor.
      eapply cantorMonotonic. apply vcU1.
      unfold go. intros. firstorder.
      eapply cantorMonotonic. apply vcU2.
      unfold go. intros. firstorder.
      assumption.
      constructor. intros d. right. apply H0.
    * pose proof (IHvcU1 _ _ H0_).
      pose proof (IHvcU2 _ _ H0_0).
      destruct H1 as [tandq [torq [tandp [torp eqt]]]].
      destruct H2 as [fandq [forq [fandp [forp eqf]]]].
      exists ((tandq + fandq) * (1 # 2)).
      exists ((torq + forq) * (1 # 2)).
      repeat split.
      Focus 3.
      rewrite <- Qmult_plus_distr_l. 
      assert (forall (a b c d : Q), 
       a + b + (c + d) == ((a + c) + (b + d))).
      intros. field.
      rewrite H1. rewrite eqt. rewrite eqf.
      rewrite <- H1. rewrite H0. rewrite H.
      rewrite <- Qmult_plus_distr_l.
      rewrite <- Qmult_assoc.
      field.
      econstructor. unfold go in *. eassumption. eassumption. field.
      econstructor. unfold go in *. eassumption. eassumption. field.
- intros U V x y vcAnd. generalize dependent y.
  inversion vcAnd; intros y vcOr.
  + inversion vcOr.
    * exists 0. exists 0. repeat split; constructor.
    * (* This is likely not true. Consider the case where H1 is discontinuous.
         We won't be able to turn H1's decisions into a tree. *)
      admit.
    * admit.
  + admit.
  + admit.
Admitted.

(** * Integration *)

(* Simple functions, though "function" is a poor choice of words since
   we can't evaluate them. *)
Inductive Simple {A : Type} :=
  | SNil : Simple
  | SIndicator : (A -> Prop) -> Simple
  | SAdd : Simple -> Simple -> Simple
  | SScale : forall (q : Q), (q >= 0) -> Simple -> Simple
.

Arguments Simple : clear implicits.

(* Definition of the integral of a simple function against a measure.
   Again, we are lower-bounding the integral (since we use lower bounds
   for the measure).
*)
Inductive SimpleIntegral {A : Type} (mu : (A -> Prop) -> Q -> Prop) 
  : Simple A -> Q -> Prop :=
  | SENil : SimpleIntegral mu SNil 0
  | SEIndicator : forall {P : A -> Prop} {q}, mu P q -> SimpleIntegral mu (SIndicator P) q
  | SEAdd : forall {a b f g}
         , SimpleIntegral mu f a
         -> SimpleIntegral mu g b
         -> SimpleIntegral mu (SAdd f g) (a + b)
  | SEScale : forall {c a ca f} {cpos : c >= 0}, SimpleIntegral mu f a
           -> ca == c * a
           -> SimpleIntegral mu (SScale c cpos f) ca.

(* Here we consider a Simple as a pointwise function, in a sense,
   by integrating against a Dirac delta. *)
Definition SimpleEval {A : Type} (f : Simple A) (x : A) : Q -> Prop :=
  SimpleIntegral (unitProb x) f.

(* If I can give f a certain lower bound, I can give g the same lower bound *)
Definition funcLTE {A : Type} (f : A -> Q -> Prop) (g : A -> Q -> Prop) : Prop :=
  forall (x : A) (q : Q), f x q -> exists q', g x q' /\ q <= q'.

(* We can lower-bound the integral of a general function f against a measure
   by lower-bounding the integral of a simple function which is no larger
   than f. *)
Definition Integral {A : Type} (mu : (A -> Prop) -> Q -> Prop) (f : A -> Q -> Prop) (q : Q)
  : Prop := 
  exists (s : Simple A), funcLTE (SimpleEval s) f
                  /\ SimpleIntegral mu s q.

(** We can now define a product measure using our notion
    of integrals! *)
Inductive ProductVal {A B : Type}
  (ValL : (A -> Prop) -> Q -> Prop)
  (ValR : (B -> Prop) -> Q -> Prop) (P : (A * B) -> Prop) : Q -> Prop :=
  | Prod : forall (f : A -> Q -> Prop)
         , (forall (a : A) (q : Q), f a q -> exists q', ValR (fun b => P (a, b)) q' /\ q' >= q)
         -> forall {res}, Integral ValL f res
         -> ProductVal ValL ValR P res.

(* If we take the product of a dirac delta measure with another measure,
   we have a nice identity property about the produce measure. *)
Theorem unitProdId {A B : Type}
  (a : A) (ValB : Valuation B)
  (P : (A * B) -> Prop)
  (q : Q) (qpos : q >= 0)
  (margB : val ValB (fun b => P (a, b)) q)
  : ProductVal (unitProb a) (val ValB) P q.
Proof.
pose (f := fun a' q0 => (a = a' /\ q0 <= q) \/ q0 == 0).
eapply Prod with f.
intros. unfold f in H. destruct H. destruct H. subst.
exists q. split; assumption.
destruct (zeroed ValB (fun b => P (a0, b))). 
destruct H0.
exists x. split.  assumption. rewrite H. rewrite H1.
apply Qle_refl.
unfold Integral.
exists (SScale q qpos (SIndicator (fun a' => a = a'))).
split. unfold funcLTE.
intros.
inversion H; clear H; subst.
inversion H2; clear H2; subst.
inversion H0; clear H0.
eexists. split. rewrite <- H.
unfold f. left. split. reflexivity. instantiate (1 := q).
apply Qle_refl. rewrite H4. rewrite <- H1. 
rewrite Qmult_1_r. apply Qle_refl.
exists 0. split. unfold f. right. reflexivity.
rewrite H4. rewrite <- H. rewrite Qmult_0_r. apply Qle_refl.
econstructor.
econstructor. econstructor. reflexivity. field.
Qed.