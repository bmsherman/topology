Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Discrete.
Section Defn.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Variable D : Type -> U.

(** 'pt' is the introduction rule for maps to discrete spaces,
    'func' is the introduction rule for maps from discrete spaces,
    and 'pt_elim' is the elimination rule
*)
Class DiscreteOps : Type :=
  { discrete_pt: forall {A}, A -> unit ~~> D A
  ; discrete_pt_elim : forall {A}, unit ~~> D A -> A
  ; discrete_func : forall {A B}, (A -> unit ~~> B) -> D A ~~> B
  }.

Context `{DiscreteOps}.

Require Import Morphisms.
Class DiscreteProps : Type :=
  { unit_discrete : unit ≅ D True
  ; discrete_pt_elim_Proper :> forall A,
     Proper (eq ==> Logic.eq) (discrete_pt_elim (A := A))
  ; prod_discrete : forall {A B}, D A * D B ≅ D (A * B)
  ; pt_beta : forall {A} (x : A),
     discrete_pt_elim (discrete_pt x) = x
  ; pt_eta : forall {A} (x : unit ~~> D A),
     discrete_pt (discrete_pt_elim x) == x
  ; func_pt : forall {A B} (x : A) (f : A -> unit ~~> B),
     discrete_func f ∘ discrete_pt x == f x
  }.

Require Import Spec.CCC.Presheaf.
Import Presheaf.
Context {cmcprops : CMC_Props U}.

Definition discrete_pt_CCC {A} (x : A) : Const (Y (D A))
  := pt_to_presheaf (discrete_pt x).

Definition discrete_pt_elim_CCC {A} (x : Const (Y (D A)))
  : A
  := discrete_pt_elim (pt_from_presheaf x).

Context `{DiscreteProps}.

Lemma pt_beta_CCC : forall {A} (x : A),
  discrete_pt_elim_CCC (discrete_pt_CCC x) = x.
Proof.
intros. unfold discrete_pt_elim_CCC, discrete_pt_CCC,
  pt_from_presheaf, pt_to_presheaf.
simpl. 
rewrite <- (unit_uniq id). rewrite compose_id_right.
apply pt_beta.
Qed.


End Defn.
End Discrete.