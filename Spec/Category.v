(** I will try to use the same names for the operations
    that there are in Coq *)

Module Category.

(** A category, with its type of morphisms, and a product operation *)
Class CCat {U : Type} : Type := 
  { arrow : U -> U -> Type
  ; prod : U -> U -> U
  ; eq : forall {A B}, arrow A B -> arrow A B -> Prop
  }.

Arguments CCat : clear implicits.

(** Notation for objects of categories *)
Delimit Scope obj_scope with obj.
Local Open Scope obj.
Infix "~~>" := arrow (at level 75) : obj_scope.
Infix "*" := prod : obj_scope.

Delimit Scope morph_scope with morph.
Local Open Scope morph.
Infix "==" := eq (at level 70, no associativity) : morph_scope.

(** Cartesian monoidal categories *)

Class CMC {U : Type} `{CCat U} : Type :=
  { id : forall {A}, A ~~> A
  ; compose : forall {A B C}, B ~~> C -> A ~~> B -> A ~~> C
 
  ; unit : U
  ; tt : forall {Γ}, Γ ~~> unit

  ; fst : forall {A B}, A * B ~~> A
  ; snd : forall {A B}, A * B ~~> B

  ; diagonal : forall {A}, A ~~> A * A
  ; parallel : forall {A B X Y}, A ~~> X -> B ~~> Y -> A * B ~~> X * Y

  }.

Arguments CMC U {_} : clear implicits.

Infix "∘" := compose (at level 30) : morph_scope.
Infix "⊗" := parallel (at level 25) : morph_scope.

Require Import Coq.Program.Combinators Coq.Program.Equality.

Definition add_unit_left {U} `{CMC U} {A : U} : A ~~> unit * A
  := tt ⊗ id ∘ diagonal.

Definition add_unit_right {U} `{CMC U} {A : U} : A ~~> A * unit
  := id ⊗ tt ∘ diagonal.

Class CMC_Props {U : Type} `{CMC U} : Prop :=
  { compose_id_left : forall {A B} (f : A ~~> B), id ∘ f == f
  ; compose_id_right : forall {A B} (f : A ~~> B), f ∘ id == f
  ; compose_assoc : forall {A B C D} (f : A ~~> B) (g : B ~~> C)
      (h : C ~~> D), (h ∘ g) ∘ f == h ∘ (g ∘ f)
  ; diag_fst : forall {A}, fst ∘ add_unit_right == id (A := A)
  ; diag_snd : forall {A}, snd ∘ add_unit_left == id (A := A)
  }.

Arguments CMC_Props U {_ _} : clear implicits.

(** Strong monads for cartesian monoidal categories *)
Class SMonad {U : Type} `{CMC U} {M : U -> U} : Type :=
  { ret  : forall {A}, A ~~> M A
  ; map : forall {A B}, (A ~~> B) -> M A ~~> M B
  ; strong : forall {A B}, A * M B ~~> M (A * B)
  ; join : forall {A}, M (M A) ~~> M A
  }.

Arguments SMonad U {_ _} M : clear implicits.

Notation "A -[ f ]-> B" := (f%morph : (arrow A%obj B%obj)) (at level 60)
  : morph_scope.

Definition prod_assoc_left {U} `{CMC U} {A B C : U} 
  : A * (B * C) ~~> (A * B) * C := 
  (id ⊗ fst) ⊗ (snd ∘ snd) ∘ diagonal.

Definition prod_assoc_right {U} `{CMC U} {A B C : U} 
  : (A * B) * C ~~> A * (B * C) := 
  (fst ∘ fst) ⊗ (snd ⊗ id) ∘ diagonal.

(** See https://ncatlab.org/nlab/show/strong+monad#alternative_definition
*)
Class SMonad_Props {U} {M : U -> U} `{SMonad U M} : Prop :=
  { strength_unit : forall {A},
     (unit * M A) -[ strong ]-> M (unit * A)
      == map add_unit_left ∘ snd
  ; strength_compose : forall {A B C},
   (A * (B * M C)) -[strong ∘ (id ⊗ strong)]-> (M (A * (B * C)))
   == map prod_assoc_right ∘ strong ∘ prod_assoc_left
  ; strength_ret : forall {A B},
    (A * B) -[ ret ]-> (M (A * B)) ==
    strong ∘ (id ⊗ ret)
  ; strength_join : forall {A B},
    strong ∘ ((A * M (M B)) -[ id ⊗ join ]-> (A * M B))
    == 
    join ∘ map strong ∘ strong
  }.

End Category.