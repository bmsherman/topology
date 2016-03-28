Require Import FunctionalExtensionality.

Set Asymmetric Patterns.


(** Isomorphisms between types. *)
Record T { A B : Type } : Type :=
  { to      : A -> B
  ; from    : B -> A
  ; from_to : forall (a : A), from (to a) = a
  ; to_from : forall (b : B), to (from b) = b
  }.

Arguments T : clear implicits.

(** Isomorphisms form an equivalence relation: they are reflexivity,
    symmetric, and transitive. *)
Theorem Refl (A : Type) : T A A.
Proof.
refine (
  {| to   := fun x => x
   ; from := fun x => x |});
reflexivity.
Defined.

Definition Sym {A B : Type} (iso : T A B) : T B A :=
  {| to := from iso
   ; from := to iso
   ; from_to := to_from iso
   ; to_from := from_to iso
  |}.

Theorem Trans { A B C : Type } :
  T A B -> T B C -> T A C.
Proof.
intros AB BC.
refine (
{| to   := fun x => to   BC (to   AB x)
 ; from := fun y => from AB (from BC y)
|}); intros.
- rewrite (from_to BC).
  rewrite (from_to AB).
  reflexivity.
- rewrite (to_from AB).
  rewrite (to_from BC).
  reflexivity.
Defined.

(** * Sigma type isomorphisms *)
(** Isomorphisms between Sigma types with different indexing types. *)

Definition FSig {B : False -> Type} : T (sigT B) False.
Proof. refine (
{| to := @projT1 _ B
 ; from := False_rect (sigT B) |}).
intros. destruct a. contradiction. 
intros. contradiction.
Defined.

Definition TSig {B : True -> Type} : T (sigT B) (B I).
Proof. refine (
{| to := fun x => match x with existT I p => p end
 ; from := existT _ I
|}).
Proof. 
intros x. destruct x. destruct x. reflexivity.
intros b. reflexivity.
Defined.

Definition PlusSig {A1 A2 : Type}
  {B : (A1 + A2)%type -> Type}
  {B1 B2 : Type }
  (iso1 : T (sigT (fun x => B (inl x))) B1)
  (iso2 : T (sigT (fun x => B (inr x))) B2)
  :       T (sigT B)                 (B1 + B2)%type.
Proof.
refine (
{| to := fun x : sigT B => match x with
   | existT (inl a1) pa1 => inl (to iso1 (existT (fun x => B (inl x)) a1 pa1))
   | existT (inr a2) pa2 => inr (to iso2 (existT (fun x => B (inr x)) a2 pa2))
   end
; from := fun x => match x with
   | inl b1 => match from iso1 b1 with
     | existT a1 pa1 => existT B (inl a1) pa1
     end
   | inr b2 => match from iso2 b2 with
     | existT a2 pa2 => existT B (inr a2) pa2
     end
   end
|}).
intros a; destruct a; simpl; destruct x; simpl; rewrite from_to; reflexivity.
intros b. destruct b; simpl.
destruct (from iso1 b) eqn:beqn.
rewrite <- beqn. rewrite to_from; reflexivity.
destruct (from iso2 b) eqn:beqn.
rewrite <- beqn. rewrite to_from; reflexivity.
Defined.

(* This is in fact "true" but, without Axiom K, the construction is a little
   bit convoluted. It is proved in the HoTT library by transferring
   isomorphisms to equivalences. *)
Lemma sigmaProp {A A' : Type} {B : A -> Type}
  (iso : T A A') 
  : T (sigT B) (sigT (fun a' => B (from iso a'))).
Proof.
Abort.

Lemma sigTimes {A B : Type} : T (A * B) (sigT (fun _ : A => B)).
Proof.
refine (
{| to  := fun p => match p with (x, y) => existT (fun _ : A => B) x y end
; from := fun p => match p with existT x y => (x, y) end
|} ).
Proof.
intros. destruct a. reflexivity.
intros. destruct b. reflexivity.
Defined. 

(** * Function type isomorphisms *)
(** Isomorphisms between function types with different argument types. *)

Lemma FFunc {B : Type} : T (False -> B) True.
Proof.
refine (
{| to   := fun _ => I
 ; from := fun _ => False_rect B |}); intros.
apply functional_extensionality. intros. inversion x.
destruct b. reflexivity.
Defined.

Lemma TFunc {B : Type} : T (True -> B) B.
Proof.
refine (
{| to   := fun f => f I
 ; from := fun b _ => b |}); intros.
apply functional_extensionality. intros. destruct x. reflexivity.
reflexivity.
Defined.

Lemma PlusFunc {A1 A2 B T1 T2 : Type} : 
   T (A1 -> B) T1
 -> T (A2 -> B) T2
 -> T ((A1 + A2)%type -> B) (T1 * T2).
Proof.
intros I1 I2.
refine (
{| to := fun f => ( to I1 (fun a1 => f (inl a1))
                 , to I2 (fun a2 => f (inr a2)) )
 ; from := fun p => match p with
   | (x, y) => fun v => match v with
     | inl a1 => from I1 x a1
     | inr a2 => from I2 y a2
     end
   end |}); intros.
+ apply functional_extensionality; intros. 
  destruct x.
   - rewrite (from_to I1). reflexivity.
   - rewrite (from_to I2). reflexivity.
+ destruct b. f_equal. 
  - rewrite (@to_from _ _ I1). reflexivity.
  - rewrite (@to_from _ _ I2). reflexivity.
Defined.

Lemma TimesFunc { A1 A2 B X Y : Type } : 
    T (A2 -> B) X
  -> T (A1 -> X) Y
  -> T ((A1 * A2)%type -> B) Y.
Proof.
intros IX IY.
refine (
{| to := fun f => to IY (fun a1 =>
                 to IX (fun a2 => f (a1, a2)))
 ; from := fun u p => match p with
   | (a1, a2) => let t := (from IY u) a1
                in       (from IX t) a2
   end
|}); intros.
apply functional_extensionality; intros.
destruct x.
simpl. rewrite (from_to IY). rewrite (from_to IX). reflexivity.
simpl.
assert (
(fun a1 : A1 => to IX (fun a2 : A2 => from IX (from IY b a1) a2))
 = 
(fun a1 : A1 => to IX             (from IX (from IY b a1)))
).
reflexivity.
rewrite H. 
assert (
(fun a1 : A1 => to IX (from IX (from IY b a1)))
=
(fun a1 : A1 =>                (from IY b a1))
).
apply functional_extensionality; intros.
rewrite (to_from IX). reflexivity.
rewrite H0.
rewrite (to_from IY).
reflexivity.
Defined.

(** * Congruences *)
(** Isomorphism is a congruence over the type forming operations
    for sums, products, and functions. *)

Theorem PlusCong {A B A' B' : Type}
 (IA : T A A')
 (IB : T B B')
 : T (A + B)%type (A' + B')%type.
Proof.
refine (
{| to := fun x => match x with
   | inl a => inl (to IA a)
   | inr b => inr (to IB b)
   end
 ; from := fun x => match x with
   | inl a' => inl (from IA a')
   | inr b' => inr (from IB b')
   end
|}).
intros x; destruct x.
rewrite (from_to IA). reflexivity.
rewrite (from_to IB). reflexivity.
intros x; destruct x.
rewrite (to_from IA). reflexivity.
rewrite (to_from IB). reflexivity.
Defined.

Theorem TimesCong {A B A' B' : Type}
 (IA : T A A')
 (IB : T B B')
 : T (A * B)%type (A' * B') %type.
Proof.
refine (
{| to := fun p => match p with | (x, y) => (to IA x, to IB y) end
 ; from := fun p => match p with | (x, y) => (from IA x, from IB y) end
|}); intros p; destruct p; f_equal.
apply (from_to IA).
apply (from_to IB).
apply (to_from IA).
apply (to_from IB).
Defined.

Theorem FuncCong { A A' B B' : Type } :
  T A A' -> T B B' -> T (A -> B) (A' -> B').
Proof.
intros IA IB.
refine (
  {| to   := fun f a' => to   IB (f (from IA a'))
   ; from := fun f a  => from IB (f (to   IA a )) |});
intros; apply functional_extensionality; intro x; simpl;
  repeat rewrite (from_to IA);
  repeat rewrite (to_from IA);
  repeat rewrite (from_to IB);
  repeat rewrite (to_from IB);
  reflexivity.
Defined.

Definition PlusComm {A B} : T (A + B) (B + A).
Proof. refine (
  {| to := fun x => match x with
  | inl a => inr a
  | inr b => inl b
  end
  ; from := fun y => match y with
  | inl b => inr b
  | inr a => inl a
  end
  |}); intros.
- destruct a; reflexivity.
- destruct b; reflexivity.
Defined.

Theorem eq_dec {A B : Type} : (forall x y : A, {x = y} + {x <> y})
  -> T A B -> forall x y : B, {x = y} + {x <> y}.
Proof.
intros dec t x y.
destruct (dec (from t x) (from t y)).
  + left. 
    replace x with (to t (from t x)) by apply to_from.
    replace y with (to t (from t y)) by apply to_from.
    f_equal. assumption.
  + right. congruence.
Qed.

(** * Infinite *)
(** Cantor's diagonal arguments, which says that there is no bijection
    between natural numbers and sequences of natural numbers. *)
Theorem Cantor : T nat (nat -> nat) -> False.
Proof.
intros iso.
destruct iso.
pose (f := fun n => S (to0 n n)).
assert (forall (n : nat), f <> to0 n).
- intros n. assert (to0 n n <> f n).
  unfold f. simpl. apply n_Sn.
  intros contra. apply H. rewrite contra. reflexivity.
- pose proof (to_from0 f).
  rewrite <- H0 in H.
  apply (H (from0 f)). reflexivity.
Qed.

(** * Subsets *)

Lemma sig_eq (A : Type) (P : A -> Prop) (Pirrel : forall a (p q : P a), p = q)
  : forall (x y : sig P), projT1 x = projT1 y -> x = y.
Proof.
intros. destruct x, y. simpl in *.
induction H. rewrite (Pirrel x p p0).
reflexivity.
Qed.

Theorem subset {A B : Type} (P : A -> Prop) (Q : B -> Prop)
  (i : T A B)
  : (forall a, P a -> Q (to i a))
  -> (forall b, Q b -> P (from i b))
  -> (forall a (p q : P a), p = q)
  -> (forall b (p q : Q b), p = q)
  -> T (sig P) (sig Q).
Proof.
intros PimpQ QimpP Pirrel Qirrel.
refine (
  {| to := fun sa => match sa with
    | exist a pa => exist Q (to i a) (PimpQ a pa)
    end
  ;  from := fun sb => match sb with
    | exist b pb => exist P (from i b) (QimpP b pb)
    end
  |}
); intros inp; destruct inp; simpl;
  apply sig_eq; try assumption; simpl.
  apply from_to. apply to_from.
Defined.

Theorem subsetSelf {A : Type} (P Q : A -> Prop)
  : (forall a, P a <-> Q a)
  -> (forall a (p q : P a), p = q)
  -> (forall b (p q : Q b), p = q)
  -> T (sig P) (sig Q).
Proof.
intros. apply (subset _ _ (Refl A)); try assumption; 
 intros; simpl; firstorder.
Defined.
