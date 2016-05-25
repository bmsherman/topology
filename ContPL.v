Require Import Lists.List.

(** A category, with its type of morphisms, and a product operation *)
Class CCat {U : Type} : Type := 
  { CMap : U -> U -> Type
  ; product : U -> U -> U
  }.

Arguments CCat : clear implicits.

Delimit Scope contTy_scope with cTy.
Local Open Scope cTy.
Infix "~~>" := CMap (at level 75) : contTy_scope.
Infix "*" := product : contTy_scope.


(** Cartesian monoidal categories *)
Class CMC {U : Type} `{CCat U} : Type :=
  { identity : forall {A}, A ~~> A
  ; compose : forall {A B C}, B ~~> C -> A ~~> B -> A ~~> C
 
  ; top : U
  ; top_intro : forall A : U, A ~~> top

  ; proj1 : forall {A B}, A * B ~~> A
  ; proj2 : forall {A B}, A * B ~~> B

  ; diagonal : forall {A}, A ~~> A * A
  ; parallel : forall {A B X Y}, A ~~> X -> B ~~> Y -> A * B ~~> X * Y

  }.

Arguments CMC U {_} : clear implicits.

Infix "∘" := compose (at level 30) : contTy_scope.

(** Strong monads for cartesian monoidal categories *)
Class MonadCat {U : Type} `{CMC U} {M : U -> U} : Type :=
  { ret  : forall {A}, A ~~> M A
  ; map : forall {A B}, (A ~~> B) -> M A ~~> M B
  ; strong : forall {A B}, A * M B ~~> M (A * B)
  ; join : forall {A}, M (M A) ~~> M A
  }.

Import ListNotations.
Section ContPL.

Context {U : Type} `{CMC U}.


Fixpoint nprod (xs : list U) : U := match xs with
  | nil => top
  | x :: xs' => x * nprod xs'
  end.

Definition Map (As : list U) (B : U) : Type := nprod As ~~> B.
Infix "~>" := Map (at level 80) : contTy_scope.

(** Heterogenous lists *)
Fixpoint hlist {A} (xs : list A) (B : A -> Type) : Type := match xs with
  | nil => True
  | x :: xs' => (B x * hlist xs' B)%type
  end.

(** Map a function over a heterogenous list *)
Fixpoint hmap {A B C} (f : forall a, B a -> C a) {xs : list A} : hlist xs B -> hlist xs C
  := match xs with
  | nil => fun ys => ys
  | x :: xs' => fun ys => let (y, ys') := ys in (f _ y, hmap f ys')
  end.

(** Convert a list of maps from Γ to different objects
    into a single map from Γ to the product of the objects *)
Fixpoint parprod {Γ : U} {As : list U}
  : (hlist As (fun A => Γ ~~> A)) -> Γ ~~> nprod As :=
  match As as As' return (hlist As' (fun A => Γ ~~> A)) -> Γ ~~> nprod As' with
  | nil => fun _ => top_intro Γ
  | _ => fun xs => let (y, ys) := xs in 
        parallel y (parprod ys) ∘ diagonal
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
  

Definition splay (Γ : U) (A : list U) (B : U) := hsplay A (fun t => Γ ~~> t) (Γ ~~> B).

Definition prodsplay (Γ : U) (As : list U)
  : splay Γ As (nprod As) := splaymap parprod (Bhlist As (fun t => Γ ~~> t)).

Definition Call {Γ : U} {A : list U} {B : U} (f : A ~> B) : splay Γ A B := 
  splaymap (compose f) (prodsplay Γ A).

Fixpoint instantiateContext (As : list U)
  : hlist As (fun t => nprod As ~~> t) := 
  match As as As' return hlist As' (fun t => nprod As' ~~> t) with
  | nil => I
  | A :: As' => (proj1, hmap (fun _ f => f ∘ proj2) 
     (instantiateContext As'))
  end.

(** Define a function using expressions *)
Definition makeFun (args : list U) {ret : U}
  (f : forall Γ, splay Γ args ret) : args ~> ret
  := unsplay args (f (nprod args)) (instantiateContext args).


Definition undefined A : A.
Admitted.

Variable R : U.
Definition constR {Γ} : nat -> Γ ~~> R := undefined _.
Variable plus : [R; R] ~> R.
Variable times : [R; R] ~> R.

Delimit Scope contExp_scope with cExp.
Local Open Scope cExp.
Infix "+" := (Call plus) : contExp_scope.
Infix "*" := (Call times) : contExp_scope.

Variable B : U.
Definition constB {Γ} : bool -> Γ ~~> B := undefined _.
Definition andB : [B; B] ~> B := undefined _. 
Infix "&&" := (Call andB) : contExp_scope.
Definition if_then_else {A} : [B; A; A] ~> A := undefined _.
Notation "'If' cond 'Then' thenExp 'Else' elseExp" :=
  (Call if_then_else (cond) (thenExp) (elseExp)) (at level 160) : contExp_scope.



Definition test {Γ : U} : Γ ~~> R
 := constR 2 + constR 3.


Notation "'FUN' x .. y => t " :=
        (fun _ => fun x => .. (fun y => t%cExp) .. )
        (x binder, y binder, at level 200, right associativity)
        : contExp_scope.

Definition exampleFun : [B; R; R] ~> R :=
  makeFun [B; R; R] (fun _ b x y => 
   let z := x * x in 
   If b && b
     Then z + constR 3
     Else x + (x * y) + z).

Definition example2 : [R] ~> R :=
  makeFun [R] (FUN x => let f := Call exampleFun (constB true) x in
      f (constR 5) + f x).

Definition makeFun1 {arg ret : U} (f : forall Γ, Γ ~~> arg -> Γ ~~> ret) : arg ~~> ret
  := f arg identity.

Definition squareAndAdd : R ~~> R := makeFun1 (FUN x => x * x + x).

Context {M : U -> U} {MC : MonadCat (M := M)}.

Definition bind {Γ} {A B} (m : Γ ~~> M A) (f : A ~~> M B) : Γ ~~> M B :=
  join ∘ map f ∘ m.

Definition Bind {Γ} {A B} (m : Γ ~~> M A) (f : (Γ * A)%cTy ~~> M B) : Γ ~~> M B :=
 bind (strong ∘ parallel identity m ∘ diagonal) f.

Definition Ret {Γ A} (x : Γ ~~> A) : Γ ~~> M A := ret ∘ x.

Definition addContext {Γ ret : U} (f : Γ ~~> M ret)
  : (Γ ~~> M (Γ * ret))%cTy 
  := strong ∘ parallel identity f ∘ diagonal.

Definition coinflip : forall {Γ}, Γ ~~> M B := undefined _.
Definition normal : forall {Γ}, Γ ~~> M R := undefined _.


Class Extend {Γ Δ : U} : Type := extend : Δ ~~> Γ .

Arguments Extend : clear implicits.

Instance Extend_Refl {Γ : U} : Extend Γ Γ := identity.

Instance Extend_Prod {Γ Δ A : U} `{f : Extend Γ Δ}
  : Extend Γ (Δ * A)%cTy := f ∘ proj1.

Definition Lift {Γ Δ A} `{f : Extend Γ Δ} (x : Γ ~~> A) 
  : Δ ~~> A := x ∘ f.

Definition makeFun1E {Γ arg ret : U} 
  (f : (Γ * arg)%cTy ~~> arg -> (Γ * arg)%cTy ~~> ret)
  : (Γ * arg)%cTy ~~> ret := f proj2.

Notation "! x" := (Lift x) (at level 20) : contExp_scope.

Notation "x <- e ; f" := (Bind e (makeFun1E (fun x => f))) 
  (at level 120, right associativity) : contExp_scope.

Definition exampleProgram {Γ} : Γ ~~> M R :=
  x <- normal;
  b <- coinflip;
  If b
    Then Ret (! x)
    Else
      y <- normal;
      Ret (! x + ! y).

End ContPL.