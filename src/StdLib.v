Set Universe Polymorphism.

(** Some useful tactics. *)

Ltac inv H := inversion H; clear H; subst.

(** The template-polymorphic 'prod' from the standard
    library just ain't good enough! *)
Inductive prod {A B : Type} : Type :=
  pair : A -> B -> prod.

Arguments prod : clear implicits.

Infix "*" := prod : type_scope.

Definition fst {A B} (p : A * B) := let (x, _) := p in x.
Definition snd {A B} (p : A * B) := let (_, y) := p in y.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z)
                      : core_scope.

Inductive sum {A B : Type} : Type :=
  | inl : A -> sum
  | inr : B -> sum.

Arguments sum : clear implicits.

Infix "+" := sum : type_scope.

Hint Resolve pair inl inr : core v62.



(*
(* Universe-polymorphic versions of things from
   CRelationClasses and CMorphisms. *)

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Typeclasses Opaque iffT.

Require Import CRelationClasses.

Instance iffT_Reflexive : Reflexive iffT.
Proof. firstorder. Qed.

Instance iffT_Symmetric : Symmetric iffT.
Proof. firstorder. Qed.

Instance iffT_Transitive : Transitive iffT.
Proof. firstorder. Qed.

Instance iffT_arrow_subrelation : subrelation iffT arrow | 2.
Proof. firstorder. Qed.

Instance iffT_flip_arrow_subrelation : subrelation iffT (flip arrow) | 2.
Proof. firstorder. Qed.
*)