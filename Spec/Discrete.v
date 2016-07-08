Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Discrete.
Section Defn.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Variable D : Type -> U. (* D X ~~> B ≃ X -> (unit ~~> B) *)
Variable power : Type -> U -> U. (* CF https://ncatlab.org/nlab/show/power *)
Infix "~>" := power (at level 30). 
Notation "| A |" := (unit ~~> A) (at level 90).

(* To minimize confusion: Γ, A, B, etc = objects; X, Y, Z etc = types. *)

(** 'pt' is the introduction rule for maps to discrete spaces,
    'func' is the introduction rule for maps from discrete spaces,
    and 'pt_elim' is the elimination rule
 *)

Class DiscreteOps : Type :=
  { discrete_pt: forall {X}, X -> |D X|
  ; discrete_pt_elim : forall {X}, |D X| -> X
  ; discrete_func :  forall {A}, D (|A|) ~~> A
  ; dmap : forall {X Y}, (X -> Y) -> (D X ~~> D Y)
  ; pow_app1 : forall {X A}, X -> ((X ~> A) ~~> A)
  ; pow_app2 : forall {A B}, A ~~> ((A ~~> B) ~> B)
  ; pmap : forall {X Y} {A B}, (X -> Y) -> (A ~~> B) -> (Y ~> A) ~~> (X ~> B)
  }.

(* One ought to have Γ ~~> (X ~> B) ≃ X -> (Γ ~~> B).
 In case Γ = unit this says precisely that unit ~~> (A ~> B) ≃ A -> (unit ~~> B), and this latter ≃
 D A ~~> B by previous. *)

Context `{DiscreteOps}.

Definition discrete_pt' : forall {A B}, (D A ~~> B) -> (A -> |B|) :=
  fun _ _ F a => F ∘ (discrete_pt a).

Definition discrete_func' : forall {A B}, (A -> |B|) -> D A ~~> B :=
  fun _ _ F => discrete_func ∘ (dmap F).

Definition pow_app1' : forall {A X B}, A ~~> (X ~> B) -> (X -> (A ~~> B)) :=
  fun _ _ _ f x => (pow_app1 x) ∘ f.

Definition pow_app2' : forall {X A B}, (X -> (A ~~> B)) -> A ~~> (X ~> B) :=
  fun _ _ _ f => (pmap f id) ∘ pow_app2.

Definition dfs_to : forall {X A}, |X ~> A| -> (D X ~~> A) :=
  (fun X A (F : |X ~> A|) =>
     let  F' := pow_app1' F : X -> |A|
     in   discrete_func' F').

Definition dfs_fro : forall {X A}, (D X ~~> A) -> |X ~> A| :=
  (fun X A (F : D X ~~> A) =>
     let  F' := discrete_pt' F : X -> |A|
     in   pow_app2' F').


Require Import Morphisms.
Class DiscreteProps : Type :=
  { unit_discrete : unit ≅ D True
  ; discrete_pt_elim_Proper :> forall X,
      Proper (eq ==> Logic.eq) (discrete_pt_elim (X := X))
  ; dmap_Proper : forall X Y, Proper (Logic.eq ==> eq) (dmap (X:=X)(Y:=Y))
  ; prod_discrete : forall {X Y}, D X * D Y ≅ D (X * Y)
  ; pt_beta : forall {X} (x : X),
     discrete_pt_elim (discrete_pt x) = x
  ; pt_eta : forall {X} (x : unit ~~> D X),
      discrete_pt (discrete_pt_elim x) == x
(*  ; func_pt : forall {X A} {f : D X ~~> A}, (discrete_func' (discrete_pt' f)) == f
  ; pt_func : forall {X A} {f : X -> |A| }, (discrete_pt' (discrete_func' f)) = f
  ; app21 : forall {A X B} {f : A ~~> (X ~> B)}, pow_app2' (pow_app1' f) == f
  ; app12 : forall {A X B} {f : X  -> (A ~~> B)}, pow_app1' (pow_app2' f) = f
  ; dpt_nat : forall {X Y} {h : X -> Y} {x : X}, discrete_pt (h x) == (dmap h) ∘ discrete_pt x 
   Axioms that might come in handy later but I don't know if are useful now ^*)
  ; func_pt : forall {A B} (x : A) (f : A -> unit ~~> B),
     discrete_func' f ∘ discrete_pt x == f x
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
refine (_ ∘ fst). apply discrete_func'.
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