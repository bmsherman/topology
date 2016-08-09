Set Universe Polymorphism.
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

Hint Resolve pair : core v62.