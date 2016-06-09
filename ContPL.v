Require Import Coq.Lists.List.

Import ListNotations.

(** Heterogenous lists *)
Fixpoint hlist {A} (xs : list A) (B : A -> Type) : Type := match xs with
  | nil => True
  | x :: xs' => (B x * hlist xs' B)%type
  end.

(** Map a function over a heterogenous list *)
Fixpoint hmap {A B C} (f : forall a, B a -> C a) {xs : list A} : hlist xs B -> hlist xs C
  := match xs with| nil => fun ys => ys
  | x :: xs' => fun ys => let (y, ys') := ys in (f _ y, hmap f ys')
  end.

(** Create a variadic function using heterogenous lists *)
Fixpoint hsplay {A} (xs : list A) (B : A -> Type) (result : Type) : Type := match xs with
  | nil => result
  | x :: xs' => B x -> hsplay xs' B result
  end.

(** Map a function over the result of a "splayed" construction *)
Fixpoint splaymap {A R1 R2} (f : R1 -> R2) {xs : list A} {B : A -> Type}
 : hsplay xs B R1 -> hsplay xs B R2 := match xs with
  | nil => f
  | y :: ys => fun g x => splaymap f (g x)
  end.

(** Build a heterogenous list in a variadic fashion *)
Fixpoint Bhlist {A} (xs : list A) (B : A -> Type) : hsplay xs B (hlist xs B) :=
  match xs with
  | nil => I
  | y :: ys => fun x => splaymap (fun zs => (x, zs)) (Bhlist ys B)
  end. 

(** Apply a "splayed" function to its arguments given as a heterogenous list *)
Fixpoint unsplay {A} (xs : list A) 
  {B : A -> Type} {R : Type} 
  : hsplay xs B R -> hlist xs B -> R 
  := match xs as xs' return hsplay xs' B R -> hlist xs' B -> R with
  | nil => fun f _ => f
  | x :: xs' => fun f ys => let (y, ys') := ys in unsplay _ (f y) ys'
  end.
  

Require Import Spec.Category.
Import Category.
Local Open Scope morph.
Local Open Scope obj.

Section ContPL.

Context {U : Type} `{CMC U}.

Fixpoint nprod (xs : list U) : U := match xs with
  | nil => unit
  | x :: xs' => x * nprod xs'
  end.

Definition Map (As : list U) (B : U) : Type := nprod As ~~> B.
Local Infix "~>" := Map (at level 80) : obj_scope.

(** Convert a list of maps from Γ to different objects
    into a single map from Γ to the product of the objects *)
Fixpoint parprod {Γ : U} {As : list U}
  : (hlist As (fun A => Γ ~~> A)) -> Γ ~~> nprod As :=
  match As as As' return (hlist As' (fun A => Γ ~~> A)) -> Γ ~~> nprod As' with
  | nil => fun _ => tt
  | _ => fun xs => let (y, ys) := xs in 
        (y ⊗ parprod ys) ∘ diagonal
  end.


Definition splay (Γ : U) (A : list U) (B : U) := hsplay A (fun t => Γ ~~> t) (Γ ~~> B).

Definition prodsplay (Γ : U) (As : list U)
  : splay Γ As (nprod As) := splaymap parprod (Bhlist As (fun t => Γ ~~> t)).

Definition Call {Γ : U} {A : list U} {B : U} (f : A ~> B) : splay Γ A B := 
  splaymap (compose f) (prodsplay Γ A).

Fixpoint instantiateContext (As : list U)
  : hlist As (fun t => nprod As ~~> t) := 
  match As as As' return hlist As' (fun t => nprod As' ~~> t) with
  | nil => I
  | A :: As' => (fst, hmap (fun _ f => f ∘ snd) 
     (instantiateContext As'))
  end.

(** Define a function using expressions *)
Definition makeFun (args : list U) {ret : U}
  (f : forall Γ, splay Γ args ret) : args ~> ret
  := unsplay args (f (nprod args)) (instantiateContext args).

Definition makeFun1 {arg ret : U} (f : forall Γ, Γ ~~> arg -> Γ ~~> ret) : arg ~~> ret
  := f arg id.

Context {M : U -> U} {MC : SMonad U M}.

Definition bind {Γ} {A B} (m : Γ ~~> M A) (f : A ~~> M B) : Γ ~~> M B :=
  join ∘ map f ∘ m.

Definition Bind {Γ} {A B} (m : Γ ~~> M A) (f : (Γ * A) ~~> M B) : Γ ~~> M B :=
 bind (strong ∘ (id ⊗ m) ∘ diagonal) f.

Definition Ret {Γ A} (x : Γ ~~> A) : Γ ~~> M A := ret ∘ x.

Definition addContext {Γ ret : U} (f : Γ ~~> M ret)
  : (Γ ~~> M (Γ * ret)) 
  := strong ∘ (id ⊗ f) ∘ diagonal.

Class Extend {Γ Δ : U} : Type := extend : Δ ~~> Γ .

Arguments Extend : clear implicits.

Global Instance Extend_Refl {Γ : U} : Extend Γ Γ := id.

Global Instance Extend_Prod {Γ Δ A : U} `{f : Extend Γ Δ}
  : Extend Γ (Δ * A) := f ∘ fst.

Definition Lift {Γ Δ A} `{f : Extend Γ Δ} (x : Γ ~~> A) 
  : Δ ~~> A := x ∘ f.

Definition makeFun1E {Γ arg ret : U} 
  (f : (Γ * arg) ~~> arg -> (Γ * arg) ~~> ret)
  : (Γ * arg) ~~> ret := f snd.

End ContPL.

Arguments Extend : clear implicits.

Notation "'FUN' x .. y => t " :=
        (fun _ => fun x => .. (fun y => t%morph) .. )
        (x binder, y binder, at level 200, right associativity)
        : contExp_scope.

Notation "! x" := (Lift x) (at level 20) : morph_scope.

Infix "~>" := Map (at level 80) : obj_scope.

Notation "x <- e ; f" := (Bind e (makeFun1E (fun x => f))) 
  (at level 120, right associativity) : morph_scope.

Notation "'LAM' x => f" := (makeFun1E (fun x => f)) 
  (at level 120, right associativity) : morph_scope.

Section LangExample.

Require Import Spec.Real Spec.Sierpinski Spec.Prob Spec.Sum.

Import Prob.
Import Real.
Import Sum.
Context {U : Type}.
Context `{mops : MeasOps U}.
Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) U 
   (LRnn := LRnn)}.
Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (R := R)
  (Σ := Σ)}.
Context {sumops : SumOps}.
Import Sierp.
Context `{sigmaops : ΣOps (U := U) (ccat := ccat) (cmc := cmc)
  (Σ := Σ)}.


Definition sum_match {Γ A B C}
  (e : Γ ~~> A + B)
  (l : Γ * A ~~> C) (r : Γ * B ~~> C) : Γ ~~> C :=
  sum_elim l r ∘ (id ⊗ e) ∘ diagonal.

Notation "'If' cond 'Then' thenExp 'Else' elseExp" :=
  (sum_match (cond)%morph (LAM _ => thenExp ∘ fst)%morph (LAM _ => elseExp ∘ fst)%morph) (at level 160) : morph_scope.

Definition bool := unit + unit.
Definition btrue : unit ~~> bool := inl ∘ tt.
Definition bfalse : unit ~~> bool := inr ∘ tt.
Definition band : bool * bool ~~> bool :=
  sum_elim (inl ∘ tt) fst.

Infix "&&" := (ap2 band).

Infix "+" := (ap2 (Rplus R)) : morph_scope.
Infix "*" := (ap2 (Rmult R)) : morph_scope.
Notation "0" := (ap0 (Rzero R)) : morph_scope.
Notation "1" := (ap0 (Rone R)) : morph_scope.

Fixpoint constR {Γ} (n : nat) : Γ ~~> R := match n with
  | 0%nat => 0
  | S n' => (1 + constR n')%morph
  end.

Definition exampleFun : [bool; R; R] ~> R :=
  makeFun [bool; R; R] (fun Γ b x y => 
   let z := (x * x)%morph in 
   If b && b
     Then z + constR 3
     Else x + (x * y) + z).

Definition example2 : [R] ~> R :=
  makeFun [R] (fun Γ x => let f := Call exampleFun (ap0 btrue) x in
      f (constR 5) + f x)%morph.

Definition squareAndAdd : R ~~> R := makeFun1 (fun _ x => x * x + x)%morph.

Local Instance smd : SMonad U Prob := ProbMonad.

Definition exampleProgram {Γ} : Γ ~~> Prob R :=
  x <- ap0 normal;
  b <- ap0 coinflip;
  If b
    Then Ret (!x)
    Else
      y <- ap0 normal;
      Ret (!x + !y).

Require Import Spec.Stream.
Import Stream.

Context `{StreamOps (U := U) (ccat := ccat) (Stream := Stream)}.

Infix "-" := (ap2 (Rsub R)) : morph_scope.

Definition ornstein : [R; R] ~> Prob (Stream R) :=
  makeFun [R; R] (fun _ θ σ => let σ2 := σ * σ in
     pstream (MeasOps := mops) (Ret 0) (LAM x =>
        (z <- ap0 normal 
        ; Ret ( (1 - !θ) * !x + !σ2 * !z))))%morph.

Definition peval {A} : Prob A * Open A ~~> LRnn :=
  MeasEval ∘ ((SubProb_to_Meas ∘ Prob_to_SubProb) ⊗ id).

Context `{OpenOps (U := U) (ccat := ccat) (Σ := Σ) (Open := Open)}.

Infix "<" := (ap2 (Rlt R)).
Infix "/\" := (ap2 and).

(** This seems to cause a Coq bug in v8.5...
Definition ornstein_prob : [R; R] ~> LRnn :=
  makeFun [R; R] (fun _ θ σ =>
  ap2 peval (Call ornstein θ σ)
     (open_abstract (LAM x => ap1 hd x < 0  /\  1 < ap1 hd (ap1 tl x))))%morph.
*)

End LangExample.