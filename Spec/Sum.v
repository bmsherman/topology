Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Sum.
Section Sum.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Class SumTys : Type :=
  { False : U
  ; sum : U -> U -> U }.

Infix "+" := sum : obj_scope.

Context `{sts : SumTys}.

(** Does sum_elim need to have the context Γ? It seems
    like it may *)
Class SumOps : Type :=
  { False_elim : forall {A}, False ~~> A
  ; inl : forall {A B}, A ~~> A + B
  ; inr : forall {A B}, B ~~> A + B
  ; sum_elim : forall {Γ A B C}, Γ * A ~~> C -> Γ * B ~~> C 
     -> Γ * (A + B) ~~> C
  }.

Context `{SumOps}.

Class SumProps : Type :=
  { False_elim_unique : forall {A} (x y : False ~~> A), x == y
  ; sum_elim_inl : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inl) == f
  ; sum_elim_inr : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inr) == g
  ; sum_determines : forall {Γ A B C} (f f' : Γ * (A + B) ~~> C),
      f ∘ (id ⊗ inl) == f' ∘ (id ⊗ inl) ->  f ∘ (id ⊗ inr) == f' ∘ (id ⊗ inr) -> f == f'
  }.

Definition sum_match {Γ A B C}
  (e : Γ ~~> A + B)
  (l : Γ * A ~~> C) (r : Γ * B ~~> C) : Γ ~~> C :=
  sum_elim l r ∘ ⟨ id , e ⟩.

Definition copair {A B C} : (A ~~> C) -> (B ~~> C) -> (A + B ~~> C) :=
  fun f g =>
    sum_elim (Γ := unit) (f ∘ snd) (g ∘ snd) ∘ add_unit_left.

Definition sum_comm {A B} : A + B ~~> B + A :=
  copair inr inl.

Context {sps : SumProps} {cps : CMC_Props U}.
Lemma sum_elim_duple : forall {Γ A B C : U} (f : Γ ~~> C),
    sum_elim (A:=A) (B:=B) (f ∘ fst) (f ∘ fst) == f ∘ fst.
Proof. intros.
       apply sum_determines.
       - rewrite sum_elim_inl.
         rewrite <- compose_assoc, parallel_fst, compose_id_left.
         reflexivity.
       - rewrite sum_elim_inr.
         rewrite <- compose_assoc, parallel_fst, compose_id_left.
         reflexivity.
Qed.


End Sum.

Infix "+" := sum : obj_scope.

End Sum.