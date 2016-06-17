(** I will try to use the same names for the operations
    that there are in Coq *)
Require Import RelationClasses Morphisms.
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

Class CMC {U : Type} {ccat : CCat U} : Type :=
  { id : forall {A}, A ~~> A
  ; compose : forall {A B C}, B ~~> C -> A ~~> B -> A ~~> C
 
  ; unit : U
  ; tt : forall {Γ}, Γ ~~> unit

  ; fst : forall {A B}, A * B ~~> A
  ; snd : forall {A B}, A * B ~~> B

  ; pair : forall {Γ A B}, (Γ ~~> A) -> (Γ ~~> B) -> (Γ ~~> A * B)

  ; eq_Equivalence :> forall A B, Equivalence (eq (A := A) (B := B))
  ; compose_proper : forall {A B C} (f f' : A ~~> B) (g g' : B ~~> C),
      f == f' -> g == g' -> compose g f == compose g' f'
  ; pair_proper : forall {Γ A B} (f f' : Γ ~~> A) (g g' : Γ ~~> B),
      f == f' -> g == g' -> pair f g == pair f' g'
  }.

Definition parallel {U} `{CMC U} {A B C D : U} (f : A ~~> B) (g : C ~~> D) : A * C ~~> B * D :=
  pair (compose f fst) (compose g snd).

Theorem parallel_proper `{CMC} : forall {A B C D} (f f' : A ~~> B) (g g' : C ~~> D),
    f == f' -> g == g' -> parallel f g == parallel f' g'.
Proof. intros A B C D f f' g g' ff' gg'.
 unfold parallel. apply pair_proper.
       - apply compose_proper.
         + apply Equivalence_Reflexive.
         + apply ff'.
       - apply compose_proper.
         + apply Equivalence_Reflexive.
         + apply gg'.
Defined.           

Definition diagonal {U} `{CMC U} {A : U} : A ~~> A * A :=
  pair id id.

Global Instance compose_Proper `{CMC} : forall A B C : U,
  Proper (eq (A := B) (B := C) ==> eq ==> eq (A := A)) compose.
Proof. 
intros. unfold Proper, respectful.
intros. apply compose_proper; assumption.
Qed.

Global Instance pair_Proper `{CMC} : forall A B C : U,
  Proper (eq (A := A) (B := B) ==> eq (A := A) (B := C) ==> eq) pair.
Proof. 
intros. unfold Proper, respectful.
intros. apply pair_proper; assumption.
Qed.

Global Instance parallel_Proper `{CMC} : forall A B C D : U,
  Proper (eq (A := A) (B := B) ==> eq (A := C) (B := D) ==> eq) parallel.
Proof. 
intros. unfold Proper, respectful.
intros. apply parallel_proper; assumption.
Qed.

Arguments CMC U {_} : clear implicits.

Infix "∘" := compose (at level 40, left associativity) : morph_scope.
 Notation "⟨ f , g ⟩" := (pair f g) : morph_scope.
Infix "⊗" := parallel (at level 25) : morph_scope.

Definition Mono {U} `{CMC U} {A B : U} (f : A ~~> B) :=
  forall X (g1 g2 : X ~~> A), f ∘ g1 == f ∘ g2 -> g1 == g2.

Record Iso {U} `{CMC U} {A B : U} : Type :=
  { to   : A ~~> B
  ; from : B ~~> A
  ; to_from : to ∘ from == id
  ; from_to : from ∘ to == id
  }.

Arguments Iso {_ _ _} A B : clear implicits.

Infix "≅" := Iso (at level 70, no associativity) : obj_scope.

Section BasicOps. 
Context {U} `{CMC U}.

Definition ap0 {Γ A : U} (f : unit ~~> A)
  : Γ ~~> A := f ∘ tt.

Definition ap1 {Γ A B : U} (f : A ~~> B) (x : Γ ~~> A)
  : Γ ~~> B := f ∘ x.

Definition ap2 {Γ A B C : U} 
  (f : A * B ~~> C) (x : Γ ~~> A) (y : Γ ~~> B) : Γ ~~> C := 
  f ∘ ⟨x, y⟩.

Definition add_unit_left {A : U} : A ~~> unit * A
  := ⟨tt, id⟩.

Definition add_unit_right {A : U} : A ~~> A * unit
  := ⟨id, tt⟩.

End BasicOps.

Class CMC_Props {U : Type} {ccat : CCat U} {cmc : CMC U} : Prop :=
  { compose_id_left : forall {A B} (f : A ~~> B), id ∘ f == f
  ; compose_id_right : forall {A B} (f : A ~~> B), f ∘ id == f
  ; compose_assoc : forall {A B C D} (f : A ~~> B) (g : B ~~> C) (h : C ~~> D), h ∘ (g ∘ f) == (h ∘ g) ∘ f
  ; pair_uniq : forall {A B C} (h : A ~~> B * C), h == ⟨fst ∘ h, snd ∘ h⟩
  ; pair_fst : forall {A B C} (f : A ~~> B) (g : A ~~> C), fst ∘ ⟨f, g⟩ == f
  ; pair_snd : forall {A B C} (f : A ~~> B) (g : A ~~> C), snd ∘ ⟨f, g⟩ == g
  ; unit_uniq : forall {A} (h : A ~~> unit), h == tt
  }.

Arguments CMC_Props U {_ _} : clear implicits.

Section BasicProps.
  Require Coq.Setoids.Setoid.
  Context {U} {ccat : CCat U} {cmc : CMC U} {cmp : @CMC_Props U ccat cmc}.

  Theorem isom_eq_left : forall {A B C : U} (f f' : A ~~> B) (s : B ≅ C), (to s) ∘ f == (to s) ∘ f' -> f == f'.
  Proof. intros. assert ((from s) ∘ ((to s) ∘ f) == (from s) ∘ ((to s) ∘ f')).
         { rewrite H. reflexivity.
         }
         rewrite -> compose_assoc in H0, H0.
         rewrite (from_to s) in H0.
         rewrite compose_id_left in H0, H0.
         apply H0.
  Defined.


  Theorem isom_eq_right : forall {A B C : U} (f f' : B ~~> C) (s : A ≅ B), f ∘ (to s) == f' ∘ (to s) -> f == f'.
  Proof. intros. assert ((f ∘ (to s)) ∘ (from s) == (f' ∘ (to s)) ∘ (from s)).
         { rewrite H. reflexivity.
         }
         rewrite <- compose_assoc in H0, H0.
         rewrite (to_from s) in H0.
         rewrite compose_id_right in H0, H0.
         apply H0.
  Defined.
  
  Theorem proj_eq : forall {A B C : U} {f f' : A ~~> B * C}, (fst ∘ f) == (fst ∘ f') -> (snd ∘ f == snd ∘ f') -> f == f'.
  Proof. intros A B C f f' Hfst Hsnd. rewrite (pair_uniq f). rewrite (pair_uniq f').
         rewrite Hfst, Hsnd. reflexivity.
  Defined.
  

  Theorem unit_isom_left : forall {A : U}, (unit * A) ≅ A.
  Proof. intros A. refine (@Build_Iso U ccat cmc (unit * A) A snd ⟨tt, id⟩ _ _).
         - rewrite pair_snd. reflexivity.
         - apply proj_eq.
           + rewrite unit_uniq. symmetry. apply unit_uniq.
           + rewrite compose_id_right. rewrite compose_assoc. rewrite pair_snd. rewrite compose_id_left.
             reflexivity.
  Defined.

  Theorem unit_isom_right : forall {A : U}, (A * unit) ≅ A.
  Proof. intros A. refine (@Build_Iso U ccat cmc (A * unit) A fst ⟨id, tt⟩ _ _).
         - rewrite pair_fst. reflexivity.
         - apply proj_eq.
           + rewrite compose_id_right. rewrite compose_assoc. rewrite pair_fst. rewrite compose_id_left.
             reflexivity.
           + rewrite unit_uniq. symmetry. apply unit_uniq.            
  Defined.

  
  Lemma parallel_pair : forall {A B C D E : U} (f : A ~~> B) (g : A ~~> C) (h : B ~~> D) (k : C ~~> E), (h ⊗ k) ∘ ⟨f, g⟩ == ⟨h ∘ f, k ∘ g⟩.
  Proof. intros A B C D E f g h k.
         unfold parallel. apply proj_eq.
         - rewrite compose_assoc. rewrite pair_fst, pair_fst.
           rewrite <- compose_assoc. rewrite pair_fst. reflexivity.
         - rewrite compose_assoc. rewrite pair_snd, pair_snd.
           rewrite <- compose_assoc. rewrite pair_snd. reflexivity.
  Defined.

  Lemma pair_f : forall {A B C D : U} (f : A ~~> B) (h : B ~~> C) (k : B ~~> D),
      ⟨h, k⟩ ∘ f == ⟨h ∘ f, k ∘ f⟩.
  Proof. intros A B C D f h k. apply proj_eq.
         - rewrite pair_fst, compose_assoc, pair_fst. reflexivity.
         - rewrite pair_snd, compose_assoc, pair_snd. reflexivity.
  Defined.

           

  
End BasicProps.

(** Strong monads for cartesian monoidal categories *)
Class SMonad {U : Type} {ccat : CCat U} {cmc : CMC U} {M : U -> U} : Type :=
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
  ⟨id ⊗ fst, snd ∘ snd⟩.

Definition prod_assoc_right {U} `{CMC U} {A B C : U} 
  : (A * B) * C ~~> A * (B * C) := 
  ⟨fst ∘ fst, snd ⊗ id⟩.

(** See https://ncatlab.org/nlab/show/strong+monad#alternative_definition
*)
Class SMonad_Props {U} {M : U -> U} {ccat : CCat U} {cmc : CMC U} {smd : SMonad U M} : Prop :=
  { map_proper : forall {A B} (f g : A ~~> B),
      f == g -> map f == map g
    ; map_compose : forall {A B C} (f : A ~~> B) (g : B ~~> C), (map g) ∘ (map f) == map (g ∘ f)                      ; map_id : forall {A},  map (id (A := A)) == id (A := (M A))
    ; ret_nat : forall {A B : U} (f : A ~~> B), ret ∘ f == (map f) ∘ ret
    ; join_nat : forall {A B : U} (f : A ~~> B), (map f) ∘ join == join ∘ (map (map f))
    ; join_map_ret : forall {A : U}, join ∘ (map (ret(A:=A))) = id
    ; join_ret : forall {A : U}, join ∘ (ret(A:=(M A))) = id
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


Global Instance map_Proper `{SMonad_Props} : forall A B : U,
  Proper (eq (A := A) (B := B) ==> eq) map.
Proof. 
intros. unfold Proper, respectful.
intros. apply map_proper; assumption.
Qed.


Section Basic_SMonad_Props.
  Require Coq.Setoids.Setoid.
  Context {U} {ccat : CCat U} {cmc : CMC U} {M : U -> U} {smd : SMonad U M} {smp : @SMonad_Props U M ccat cmc smd}.

  Theorem M_iso : forall {A B : U}, (A ≅ B) -> ((M A) ≅ (M B)).
  Proof. intros A B s. refine (@Build_Iso U ccat cmc (M A) (M B) (map (to s)) (map (from s)) _ _).
         - rewrite map_compose. rewrite (to_from s). rewrite map_id. reflexivity.
         - rewrite map_compose. rewrite (from_to s). rewrite map_id. reflexivity.
  Defined.

  
 Definition emap {Γ A B : U} (f : Γ * A ~~> B) : Γ * (M A) ~~> M B :=
   (map f) ∘ strong.

 (*
 Lemma emap_compose : forall {Γ Δ A B C : U} (f : Γ * A ~~> Δ * B)(g : Δ * B ~~> C), (emap (g ∘ f)) == (emap g) ∘ ⟨fst ∘ emap f, map (snd ∘ f)⟩.
 Proof. intros Γ Δ A B C f g.
        Check (emap (g ∘ f)).
        Check (emap g).
        Check ⟨fst ∘ f, map (snd ∘ f) ∘ ret⟩.
   (emap (g ∘ f)) == (emap g) ∘ ⟨fst ∘ f, emap (snd ∘ f)⟩.
*)
 
Global Instance emap_Proper : forall Γ A B : U,
  Proper (eq (A := Γ * A) (B := B) ==> eq) emap.
Proof. 
intros. unfold Proper, respectful.
intros. unfold emap. apply compose_proper. apply Equivalence_Reflexive. apply map_proper. assumption.
Qed.
         
  
End Basic_SMonad_Props.

End Category.