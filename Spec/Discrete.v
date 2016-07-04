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
Require Import Spec.CCC.CCC.
Import CCC.
Context {cmcprops : CMC_Props U}.

Let Y := Y (cmcprops := cmcprops).

Definition discrete_pt_CCC {A} (x : A) : Const (Y (D A))
  := pt_to_presheaf (discrete_pt x).

Definition discrete_pt_elim_CCC {A} (x : Const (Y (D A)))
  : A
  := discrete_pt_elim (pt_from_presheaf x).

Hint Constructors FirstOrder Basic : FO_DB.


Existing Instances CCat_PSh CMC_Psh CMCProps_PSh CCCOps_PSh.

Definition discrete_func_CCC {A B} (f : A -> Const (Y B))
  : Const (Y (D A) ==> Y B).
Proof.
eapply to_presheaf. econstructor 2. econstructor. econstructor. 
econstructor.
refine (_ ∘ fst). apply discrete_func.
intros. eapply from_presheaf. eauto with FO_DB.
apply f. assumption.
Defined.

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

Lemma pt_eta_CCC : forall {A} (x : Const (Y (D A))),
  discrete_pt_CCC (discrete_pt_elim_CCC x) == x.
Proof.
intros. simpl. unfold eq_map. simpl.
intros. unfold discrete_pt_elim_CCC, pt_from_presheaf.
rewrite pt_eta. apply (nattrns_ok _ _ x). simpl.
constructor.
Qed.

(* Need a definition of "ap"!
Lemma func_pt_CCC {A : Type} {B : U} (x : A) (f : A -> Const (Y B))
  : ap (discrete_func_CCC f) (discrete_pt_CCC x) == f x.
*)

End Defn.
End Discrete.