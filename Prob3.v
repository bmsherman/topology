Require Import QArith Qcanon.

(** In the comments here, I seem to use the words "measure" and
    "valuation" interchangably. Sorry! *)

Definition konst {A} (x : A) {B} (y : B) := x.

Record Valuation {A : Type} :=
  { val       : (A -> Prop) -> Qc -> Prop 
  ; zeroed    : forall P, val P 0
  ; strict    : forall q, val (konst False) q -> q = 0
  ; monotonic : forall (U : A -> Prop) q, val U q -> forall (V : A -> Prop), (forall z, U z -> V z) 
              -> val V q
  ; modular1  : forall {U V x y}, val U x -> val V y
              -> exists a b, val (fun z => U z /\ V z) a
                     /\ val (fun z => U z \/ V z) b
                     /\ a + b = x + y
  ; modular2  : forall {U V x y}, val (fun z => U z /\ V z) x 
                         -> val (fun z => U z \/ V z) y
              -> exists a b, val U a /\ val V b
                     /\ a + b = x + y
  ; nonneg    : forall P q, val P q -> q >= 0
  }.

Arguments Valuation : clear implicits.

(* A Dirac delta measure *)
Inductive unitProb {A} (a : A) (P : A -> Prop) : Qc -> Prop :=
  | Unit1 : P a -> unitProb a P 1
  | Unit0 : unitProb a P 0.

Ltac proveUnit := 
match goal with
| [ H: unitProb _ _ _ |- _ ] => induction H
| [ |- unitProb _ _ 0 ] => eapply Unit0
| [ |- unitProb _ _ 1 ] => eapply Unit1
| [ |- _ /\ _ ] => split
| [ H : ?U ?x |- exists a b : Qc, unitProb ?x ?U a /\ _ ] => exists 1 
| [ |- _ ] => reflexivity || firstorder
end.

(* The Dirac delta meets all the properties of being a Valuation.
   It will become the unit of our monad! *)
Definition unit {A : Type} (a : A) : Valuation A.
Proof. refine (
  {| val := unitProb a |}
    ); intros;
    let rec t := repeat match goal with
                       | [  |- exists _, _ ] => exists 0; solve [t]
                       | [  |- exists _, _ ] => exists 1; solve [t]
                       | _ => repeat proveUnit
                       end
    in t.
Defined.

Lemma Qcmult_le_0_compat : forall {x y : Qc},
  x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
intros. replace 0 with (0 * y) by field.
apply Qcmult_le_compat_r; assumption.
Qed.

(* Scale a valuation by a constant *)
Inductive scaledVal (q : Qc)
  {A : Type} (Val : (A -> Prop) -> Qc -> Prop) (P : A -> Prop) : Qc -> Prop :=
  | Scale : forall a, Val P a -> scaledVal q Val P (q * a).

Definition scaled {A : Type} (q : Qc) (qnn : q >= 0) (Val : Valuation A) : Valuation A.
Proof. refine (
  {| val := scaledVal q (val Val) |}
); intros.
- pose proof (zeroed Val P). 
  replace 0 with (q * 0) by field.
  constructor. assumption.
- induction H. apply strict in H. rewrite H. field.
- induction H. constructor. eapply monotonic; eassumption.
- induction H; induction H0.
  pose proof (modular1 Val H H0).
  destruct H1 as [andq [orq [andp [orp eqs]]]].
  exists (q * andq). exists (q * orq).
  repeat split; try assumption.
  do 2 rewrite <- Qcmult_plus_distr_r.
  rewrite eqs. reflexivity.
- induction H; induction H0.
  pose proof (modular2 Val H H0).
  destruct H1 as [Uq [Vq [Up [Vp eqs]]]].
  exists (q * Uq). exists (q * Vq).
  repeat split; try assumption.
  do 2 rewrite <- Qcmult_plus_distr_r.
  rewrite eqs.
  reflexivity.
- inversion H; clear H; subst. pose proof (nonneg Val _ _ H0).
  apply Qcmult_le_0_compat; assumption.
Defined.

(* Add two valuations together *)
Inductive addVal {A : Type}
  (ValL ValR : (A -> Prop) -> Qc -> Prop) (P : A -> Prop) : Qc -> Prop :=
  | Add : forall a b, ValL P a -> ValR P b -> addVal ValL ValR P (a + b).

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 = (andLq + orLq) + (andRq + orRq).
Proof. intros. field. Qed.


Definition add {A : Type} (ValL ValR : Valuation A) : Valuation A.
Proof. refine (
  {| val := addVal (val ValL) (val ValR) |}
); intros.
- pose proof (zeroed ValL P). pose proof (zeroed ValR P).
  replace 0 with (0 + 0) by field.
  constructor; assumption.
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
- induction H. replace 0 with (0 + 0). apply Qcplus_le_compat.
  apply (nonneg _ _ _ H).
  apply (nonneg _ _ _ H0).
  reflexivity.
Defined.

(* Probabilistic choice. Take [ValL] with probability [p] and
   [ValR] with probability [1 - p] *)
Definition pchoice {A : Type} (p : Qc) 
  (pge : p >= 0) (ple : p <= 1)
  (ValL ValR : Valuation A) : Valuation A.
Proof.
refine (
  add (scaled p pge ValL) (scaled (1 - p) _ ValR)
).
apply -> Qcle_minus_iff. apply ple.
Defined.

Section SillyExample.
  (** This silly example demonstrates a case where measures simply will not do.
      Here we model the fact that there is a 1/2 probability we would like
      to believe in classical logic, and for the other 1/2 probability we make
      no additional assumptions over intuitionistic logic. *)

  Definition classical := forall (P : Prop), ~ ~ P -> P.

  Let oneHalf := Qcmake (1 # 2) eq_refl.

  Definition halfClassical : Valuation Prop.
  Proof. refine (
    pchoice oneHalf _ _ (unit True) (unit classical)
  ). unfold Qle. simpl. apply Zle_succ. unfold Qle. simpl. apply Zle_succ.
  Defined.

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

  Definition probOmniscience : val halfClassical 
      (fun p => p -> forall (f : nat -> bool), (forall x, f x = true) \/ (exists x, f x = false)) oneHalf.
  Proof. unfold halfClassical.
  unfold pchoice.
  simpl.
  replace oneHalf with (0 + oneHalf) at 3 by field.
  econstructor. 
  - replace 0 with (oneHalf * 0) by field.
    repeat constructor.
  - replace oneHalf with ((1 - oneHalf) * 1) at 2.
    constructor. constructor.
    intros.
    pose proof (classicalLEM H (forall (x : nat), f x = true)).
    destruct H0. left. assumption.
    right. apply H. unfold not. intros.
    apply H0. 
    intros.
    pose proof (classicalLEM H (f x = true)). destruct H2.
    assumption. destruct (f x) eqn:fx. reflexivity.
    apply False_rect. apply H1. exists x. assumption.
    apply Qc_is_canon.
    reflexivity.
  Qed.

End SillyExample.

Require Import FunctionalExtensionality.


(* Pushforward of a measure, i.e., map a function over a measure *)
Definition map {A B : Type} (f : A -> B) (v : Valuation A)
  : Valuation B.
Proof. refine (
  {| val := fun prop => val v (fun x => prop (f x)) |}
); intros.
- apply (zeroed v (fun x => P (f x))). 
- apply (strict v). assert ((fun x => konst False (f x)) = konst False).
  apply functional_extensionality. reflexivity.
  rewrite <- H0. assumption.
- apply (monotonic v) with (fun x => U (f x)). 
  intros. apply H. intros. apply H0. assumption.
- apply (modular1 v); assumption.
- apply (modular2 v); assumption.
- apply (nonneg _ _ _ H).
Defined.

Require Import Coq.Lists.Streams.

Definition Cantor := Stream bool.

(** If we view a probability distribution on [A] as an infinitely branching
    binary tree, then [go true] descends into one branch, and [go false]
    descends into the other. *)
Definition go {B : Type} (b : bool) (dist : Cantor -> B) : Cantor -> B := 
  fun d => dist (Cons b d).

Inductive ValCantor : (Cantor -> Prop) -> Qc -> Prop :=
  | VCNone : forall {P}, ValCantor P 0
  | VCUnit : forall {P : Cantor -> Prop}, (forall d, P d) -> ValCantor P 1
  | VCCombine : forall {P} {a b} (c : Qc),
       ValCantor (go true  P) a
     -> ValCantor (go false P) b
     -> (a + b) = c / (Qcmake (2 # 1) eq_refl)
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
- intros. constructor.
- intros. generalize H. 
(*
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
*)
Abort.

(** * Integration *)

(* Simple functions, though "function" is a poor choice of words since
   we can't evaluate them. *)
Inductive Simple {A : Type} :=
  | SIndicator : (A -> Prop) -> Simple
  | SAdd : Simple -> Simple -> Simple
  | SScale : forall (q : Qc), (q >= 0) -> Simple -> Simple
.

Arguments Simple : clear implicits.

(* Definition of the integral of a simple function against a measure.
   Again, we are lower-bounding the integral (since we use lower bounds
   for the measure).
*)
Inductive SimpleIntegral {A : Type} (mu : (A -> Prop) -> Qc -> Prop) 
  : Simple A -> Qc -> Prop :=
  | SEIndicator1 : forall {P : A -> Prop} {q}, mu P q -> SimpleIntegral mu (SIndicator P) q
  | SEIndicator0 : forall {P : A -> Prop}, SimpleIntegral mu (SIndicator P) 0
  | SEAdd : forall {a b f g}
         , SimpleIntegral mu f a
         -> SimpleIntegral mu g b
         -> SimpleIntegral mu (SAdd f g) (a + b)
  | SEScale : forall {c a ca f} {cpos : c >= 0}, SimpleIntegral mu f a
           -> ca = c * a
           -> SimpleIntegral mu (SScale c cpos f) ca.

(* Here we consider a Simple as a pointwise function, in a sense,
   by integrating against a Dirac delta. *)
Definition SimpleEval {A : Type} (f : Simple A) (x : A) : Qc -> Prop :=
  SimpleIntegral (unitProb x) f.

(* If I can give f a certain lower bound, I can give g the same lower bound *)
Definition funcLTE {A : Type} (f g : A -> Qc -> Prop) : Prop :=
  forall (x : A) (q : Qc), f x q -> g x q.

Definition simpleLTE {A : Type} (f g : Simple A) : Prop :=
  forall (m : Valuation A) (q : Qc)
    , SimpleIntegral (val m) f q 
    -> SimpleIntegral (val m) g q.

Definition simpleLTEFunc {A : Type} {f g : Simple A}
  (lte : simpleLTE f g) : funcLTE (SimpleEval f) (SimpleEval g) :=
  fun x => lte (unit x).

Ltac inv H := inversion H; clear H; subst.

Lemma indicatorMonotonic {A : Type} : forall {P Q : A -> Prop},
  funcLTE (SimpleEval (SIndicator P)) (SimpleEval (SIndicator Q))
  -> forall x, P x -> Q x.
Proof.
intros. unfold funcLTE in H.
assert (SimpleEval (SIndicator P) x 1).
unfold SimpleEval. constructor. constructor. assumption.
pose proof (H x 1 H1).
inv H2. inv H4. assumption.
Qed.

(* funcLTESimple MAY NOT BE TRUE!!!
   We are in trouble if the function giving evidence of 
   funcLTE is not continuous.

   Consider a proof which uses LEM:
   indicator True  <= (indicator rational) + (indicator irrational)

   And consider a measure `m` which is uniform over the interval
   [0, 1]. Then we can produce this integral continuously:
   SimpleIntegral (U[0,1]) (indicator True) 1

   meas (U[0,1]) (indicator True) 1
   --> monotonicity
   meas (U[0,1]) (indicator rational + indicator irrational) 1
   --> modularity
   exists a b,
        meas(U[0,1]) (indicator   rational) a
    /\  meas(U[0,1]) (indicator irrational) b
    /\ a + b = 1

   How do we combine this with our funcLTE proof to create a
   SimpleIntegral (U[0,1]) (indicator rational + indicator irrational) 1
   ? It seems impossible.
*)

Lemma funcLTESimple {A : Type} {f g : Simple A}
  : funcLTE (SimpleEval f) (SimpleEval g)
  -> simpleLTE f g.
Proof.
intros lte.
unfold funcLTE in *.
unfold simpleLTE.
intros m q si.
pose proof (monotonic m (fun z => forall q', SimpleEval f z q') q
  ).
assert (val m
        (fun x : A => forall q : Qc, SimpleEval f x q -> SimpleEval g x q)
        1).
(*
generalize dependent g.
induction f; intros g.
- induction g; intros lte.
  + pose proof (indicatorMonotonic lte).
    unfold simpleLTE.
    intros. inv H0. constructor. apply monotonic with (U := P); assumption.
    apply SEIndicator0.
  + 
Abort.
*)
Abort.

(* We can lower-bound the integral of a general function f against a measure
   by lower-bounding the integral of a simple function which is no larger
   than f. *)
Definition Integral {A : Type} (mu : (A -> Prop) -> Qc -> Prop) (f : A -> Qc -> Prop) (q : Qc)
  : Prop := 
  exists (s : Simple A), funcLTE (SimpleEval s) f
                  /\ SimpleIntegral mu s q.

(** We can now define a product measure using our notion
    of integrals! *)
Inductive ProductVal {A B : Type}
  (ValL : (A -> Prop) -> Qc -> Prop)
  (ValR : (B -> Prop) -> Qc -> Prop) (P : (A * B) -> Prop) : Qc -> Prop :=
  | Prod : forall {res}
         , Integral ValL (fun (a : A) => ValR (fun b => P (a, b))) res
         -> ProductVal ValL ValR P res.

(** And why not make things more general? A dependent product
    valuation! *)
Inductive DepProductVal {A : Type} {B : A -> Type}
  (ValL : (A -> Prop) -> Qc -> Prop)
  (ValR : forall (a : A), (B a -> Prop) -> Qc -> Prop) (P : sigT B -> Prop) : Qc -> Prop :=
  | DepProd : forall {res}
         , Integral ValL (fun (a : A) => ValR a (fun b => P (existT B a b))) res
         -> DepProductVal ValL ValR P res.

(** Another variation on the theme : this one should represent
    the monadic bind *)
Inductive BindVal {A B : Type}
  (ValL : (A -> Prop) -> Qc -> Prop)
  (ValR : A -> (B -> Prop) -> Qc -> Prop) (P : B -> Prop) : Qc -> Prop :=
  | Bind : forall {res}
         , Integral ValL (fun (a : A) => ValR a P) res
         -> BindVal ValL ValR P res.


(* If we take the product of a dirac delta measure with another measure,
   we have a nice identity property about the product measure. *)
Theorem unitProdId {A B : Type}
  (a : A) (ValB : Valuation B)
  (P : (A * B) -> Prop)
  (q : Qc) (qpos : q >= 0)
  (margB : val ValB (fun b => P (a, b)) q)
  : ProductVal (unitProb a) (val ValB) P q.
Proof.
constructor.
unfold Integral. 
exists (SScale q qpos (SIndicator (fun a' => a = a'))).
split. unfold funcLTE.
intros.
inv H. inv H2. inv H0.
replace (q * 1) with q by field.
assumption.
replace (q * 0) with 0 by field.
apply zeroed.
replace (q * 0) with 0 by field.
apply zeroed.
eapply SEScale.
constructor.
constructor.
reflexivity.
field.
Qed.

Lemma funcLTERefl {A : Type} {f : A -> Qc -> Prop} : funcLTE f f.
Proof.
unfold funcLTE. intros. assumption.
Qed.

Lemma funcLTETrans {A : Type} {f g h : A -> Qc -> Prop}
  : funcLTE f g -> funcLTE g h -> funcLTE f h.
Proof.
intros fg gh.
unfold funcLTE in *.
intros.
apply gh. apply fg. assumption.
Qed.


Lemma simpleIntegralZeroed {A : Type}
  : forall (s : Simple A) (f : (A -> Prop) -> Qc -> Prop), SimpleIntegral f s 0.
Proof.
intros. induction s.
- apply SEIndicator0.
- replace 0 with (0 + 0) by field.
  constructor; assumption.
- econstructor. eassumption. field.
Qed.


Require Import ClassicalFacts.
Axiom prop_ext : prop_extensionality.

Lemma funcLTEMin {A : Type} {s : Simple A} 
  : funcLTE (SimpleEval s) (SimpleEval (SIndicator (konst False)))
  -> SimpleEval s = SimpleEval (SIndicator (konst False)).
Proof.
intros lte.
apply functional_extensionality.
intros a.
apply functional_extensionality.
intros q.
apply prop_ext.
split; intros.
- apply lte. assumption. 
- inv H. inv H1. unfold konst in H. contradiction.
  apply simpleIntegralZeroed.
  apply simpleIntegralZeroed.
Qed.

Axiom simpleExtensionality : forall {A : Type} {f g : Simple A}
  , SimpleEval f = SimpleEval g -> f = g.

Lemma simpleIntegralStrict {A : Type}
  : forall (m : Valuation A) (q : Qc)
  , SimpleIntegral (val m) (SIndicator (konst False)) q
  -> q = 0.
Proof.
intros. inversion H; clear H; subst. 
  apply (strict _ _ H1). reflexivity.
Qed.

Lemma simpleIntegralNonnegative {A : Type} {f : Simple A}
  {m : Valuation A} {q : Qc}
  : SimpleIntegral (val m) f q -> q >= 0.
Proof.
intros int.
induction int. 
- apply (nonneg _ _ _ H).
- apply Qcle_refl. 
- replace 0 with (0 + 0). apply Qcplus_le_compat; assumption. reflexivity.
- rewrite H. apply Qcmult_le_0_compat; assumption.
Qed.

Lemma Qc1notle0 : ~ (1%Qc <= 0).
Proof. unfold not. intros.
apply Qcle_not_lt in H. apply H.
unfold Qclt. simpl. unfold Qlt. simpl. constructor.
Qed.

Lemma lteIntegralMonotonic {A : Type} {f g : A -> Qc -> Prop}
  : funcLTE f g -> forall (m : Valuation A) (q : Qc)
  , Integral (val m) f q
  -> Integral (val m) g q.
Proof.
intros.
unfold Integral in *.
destruct H0.
exists x. destruct H0.
split. 2:assumption.
eapply funcLTETrans; eassumption.
Qed.

Definition addFunc {A : Type} (f g : A -> Qc -> Prop) (x : A) (q : Qc) :=
  exists a b, f x a /\ g x b /\ a + b = q.

Lemma ltePlus {A : Type} {f g : Simple A}
  {U V : A -> Qc -> Prop}
  : funcLTE (SimpleEval f) U
  -> funcLTE (SimpleEval g) V
  -> funcLTE (SimpleEval (SAdd f g)) (addFunc U V).
Proof.
intros ltef lteg.
unfold funcLTE in *.
intros x q seadd.
unfold addFunc.
inv seadd. exists a. exists b. 
split. apply ltef. apply H1.
split. apply lteg. apply H3. reflexivity.
Qed.

Definition bind {A B : Type}
  (m : Valuation A) (f : A -> Valuation B) : Valuation B.
Proof.
refine (
  {| val := BindVal (val m) (fun a => val (f a)) |}
); intros.
- split. econstructor. split.
  Focus 2. apply (@SEIndicator0 _ _ (konst False)). unfold funcLTE. intros.
  pose proof (zeroed (f x) P).
  unfold SimpleEval in H.
  replace (unitProb x) with (val (unit x)) in H by reflexivity.
  apply simpleIntegralStrict in H. subst.
  apply zeroed.
- inv H. inv H0.
  destruct H.
  assert (Integral (val m) (SimpleEval x) q).
  unfold Integral. exists x. split.
  apply funcLTERefl. assumption.
  assert (funcLTE (fun a => val (f a) (konst False)) (SimpleEval (SIndicator (konst False)))).
  unfold funcLTE.
  intros x' q' meas.
  apply strict in meas.
  subst.
  constructor. constructor.
  pose proof (funcLTETrans H H2).
  apply funcLTEMin in H3.
  apply simpleExtensionality in H3.
  subst.
  eapply simpleIntegralStrict. eassumption.
- constructor.
  inv H. 
  eapply lteIntegralMonotonic. Focus 2. eassumption.
  unfold funcLTE.
  intros a q' meas.
  eapply monotonic. eassumption.
  assumption.
- inv H. inv H0.
  destruct H1. destruct H. destruct H0. destruct H.
  assert (Integral (val m) (addFunc (fun a : A => val (f a) U) (fun a : A => val (f a) V)) (x + y)).
  unfold Integral. exists (SAdd x0 x1). split.
  apply ltePlus; assumption. constructor; assumption.

do 2 eexists. split.
  econstructor.
Abort.
