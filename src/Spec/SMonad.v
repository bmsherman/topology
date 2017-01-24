Require Import Spec.Category
  Spec.CCC.Presheaf
  Spec.CCC.CCC.

Import Category.
Import CCC.
Import Presheaf.

Local Open Scope obj.
Local Open Scope morph.

Existing Instances CCat_PSh CMC_Psh CMCProps_PSh CCCOps_PSh.

(** Strong monads for cartesian monoidal categories *)
Class SMonad {U : Type} {ccat : CCat U} {cmc : CMC U}
  { cmcprops : CMC_Props U } {M : U -> U} : Type :=
  { ret  : forall {A}, A ~~> M A
  ; map : forall {A B}, (A ~~> B) -> M A ~~> M B
  ; strong : forall {A B}, A * M B ~~> M (A * B)
  ; join : forall {A}, M (M A) ~~> M A

  ; PRet : forall {A}, unit ~~> Y A ==> Y (M A)
  ; PMap : forall {A B}, unit ~~> (Y A ==> Y B) ==> Y (M A) ==> Y (M B)
  ; PStrong : forall {A B}, unit ~~> Y A ==> Y (M B) ==> Y (M (A * B))
  ; PJoin : forall {A}, unit ~~> Y (M (M A)) ==> Y (M A)
  }.

Arguments SMonad U {_ _ _} M.

Notation "A -[ f ]-> B" := (f%morph : (arrow A%obj B%obj)) (at level 60)
  : morph_scope.

(** See https://ncatlab.org/nlab/show/strong+monad#alternative_definition
*)
Class SMonad_Props {U} {M : U -> U} {ccat : CCat U} {cmc : CMC U} 
  {cmcprops : CMC_Props U}
  {smd : SMonad U M} : Prop :=
  { map_proper : forall {A B} (f g : A ~~> B),
      f == g -> map f == map g
    ; map_compose : forall {A B C} (f : A ~~> B) (g : B ~~> C), map (g ∘ f) == (map g) ∘ (map f)
    ; map_id : forall {A},  map (id (A := A)) == id (A := (M A))
    ; ret_nat : forall {A B : U} (f : A ~~> B), ret ∘ f == (map f) ∘ ret
    ; join_nat : forall {A B : U} (f : A ~~> B), (map f) ∘ join == join ∘ (map (map f))
    ; join_map_ret : forall {A : U}, join ∘ (map (ret(A:=A))) = id
    ; join_ret : forall {A : U}, join ∘ (ret(A:=(M A))) = id
    ; join_join : forall {A : U}, join (A:=A) ∘ map join == join ∘ join
    ; strength_unit : forall {A},
     (unit * M A) -[ strong ]-> M (unit * A)
      == map add_unit_left ∘ snd
    ; strength_compose : forall {A B C},
   (A * (B * M C)) -[strong ∘ (id ⊗ strong)]-> (M (A * (B * C)))
   == map prod_assoc_right ∘ strong ∘ prod_assoc_left
    ; strength_ret : forall {A B},
        strong ∘ (id ⊗ ret) ==
        (A * B) -[ ret ]-> (M (A * B))
  ; strength_join : forall {A B},
    strong ∘ ((A * M (M B)) -[ id ⊗ join ]-> (A * M B))
    == 
    join ∘ map strong ∘ strong
  ; strong_nat : forall {A A' B B'} (f : A ~~> A') (g : B ~~> B'), strong ∘ (f ⊗ (map g)) == map (f ⊗ g) ∘ strong
  ; snd_strong : forall {A B}, (map snd) ∘ (strong (A:=A)(B:=B)) == snd (* Maybe provable from other axioms? *)
  }.

Require Import Morphisms.
Global Instance map_Proper `{SMonad_Props} : forall A B : U,
  Proper (eq (A := A) (B := B) ==> eq) map.
Proof. 
intros. unfold Proper, respectful.
intros. apply map_proper; assumption.
Qed.

Section Basic_SMonad_Props.
  Require Coq.Setoids.Setoid.
  Context {U} {ccat : CCat U} {cmc : CMC U} {cmcprops : CMC_Props U}
   {M : U -> U} {smd : SMonad U M} {smp : @SMonad_Props U M ccat cmc cmcprops smd}.

  Theorem M_iso : forall {A B : U}, (A ≅ B) -> ((M A) ≅ (M B)).
  Proof. intros A B s. refine (@Build_Iso U ccat cmc (M A) (M B) (map (to s)) (map (from s)) _ _).
         - rewrite <- map_compose. rewrite (to_from s). rewrite map_id. reflexivity.
         - rewrite <- map_compose. rewrite (from_to s). rewrite map_id. reflexivity.
  Defined.

  
 Definition emap {Γ A B : U} (f : Γ * A ~~> B) : Γ * (M A) ~~> M B :=
   (map f) ∘ strong.
 
Global Instance emap_Proper : forall Γ A B : U,
  Proper (eq (A := Γ * A) (B := B) ==> eq) emap.
Proof. 
unfold emap. prove_map_Proper.
Qed.
  
End Basic_SMonad_Props.