Set Universe Polymorphism.

Require Import Spec.Category.
Import Category.

Local Open Scope obj.
Local Open Scope morph.

Require Import Morphisms.

Section Functor. 

Context {C D : Type} `{cmcc : CMC C} `{cmcd : CMC D}.

Record Functor : Type := Build_Functor
  { fobj :> C -> D
  ; fmap : forall {A B : C}, A ~~> B -> fobj A ~~> fobj B
  ; fmap_Proper : forall {A B : C}, Proper (eq ==> eq) (@fmap A B)
  ; fmap_id : forall {A : C}, fmap (id : A ~~> A) == id
  ; fmap_compose : forall {X Y Z : C} (f : X ~~> Y) (g : Y ~~> Z),
      fmap (g ∘ f) == fmap g ∘ fmap f
  }.

Global Instance fmap_ProperI (F : Functor) A B : Proper (eq ==> eq) (@fmap F A B)
  := fmap_Proper F.

Record NatTrans (F G : Functor) :=
  { nattrans :> forall (A : C), F A ~~> G A
  ; nattrans_ok : forall A B (ext : A ~~> B),
      fmap G ext ∘ nattrans A == nattrans B ∘ fmap F ext
  }.

End Functor.

Arguments Functor C D {_ _ _ _}.

Definition id_Functor {C : Type} `{cmcc : CMC C} : Functor C C.
Proof.
unshelve econstructor.
- exact (fun x => x).
- simpl. intros. assumption.
- prove_map_Proper.
- simpl. intros; reflexivity.
- simpl. intros; reflexivity.
Defined.


Delimit Scope cat_scope with cat.
Local Open Scope cat.

Infix "==>" := Functor (at level 55, right associativity) : cat_scope.

Delimit Scope functor_scope with functor.
Local Open Scope functor.

Definition compose_Functor {C D E : Type} `{cmcc : CMC C} `{cmcd : CMC D}
  `{cmce : CMC E} (G : D ==> E) (F : C ==> D)
  : C ==> E.
Proof.
unshelve (eapply Build_Functor).
- exact (fun x => G (F x)).
- intros. simpl. repeat apply fmap; assumption.
- prove_map_Proper. 
- intros. simpl. rewrite !fmap_id. reflexivity.
- simpl. intros. rewrite !fmap_compose. reflexivity.
Defined. 

Infix "∘" := compose_Functor : functor_scope.


Require Import Types.Setoid.

Section Adjunction.
Context {C D : Type} `{cmcc : CMC C} `{cmcd : CMC D}.

(** Probably not strong enough *)
Record Adjunction
  (F : Functor C D) (G : Functor D C) : Type :=
  { Adj_Hom_Iso : forall A B, (Hom_Setoid A (G B) ≅ Hom_Setoid (F A) B)%setoid
  ; commutes :
     forall {A A' B B'} (f : A' ~~> A) (g : B ~~> B')
      (x : F A ~~> B),
    (from (Adj_Hom_Iso _ _) (g ∘ x ∘ fmap F f)
   == fmap G g ∘ from (Adj_Hom_Iso _ _) x ∘ f)%morph
  }.

End Adjunction.

Infix "-|" := Adjunction (at level 30) : functor_scope.

Lemma compose_Adjunction 
  {C D E : Type} `{cmcc : CMC C} `{cmcd : CMC D}
  `{cmce : CMC E}
  {F : Functor C D} {G : Functor D C}
  {F' : Functor D E} {G' : Functor E D}
  : F -| G -> F' -| G' -> (F' ∘ F) -| (G ∘ G').
Proof.
intros. unshelve econstructor. 
- intros. eapply Iso_Trans. simpl in *.
eapply X. simpl. eapply X0.
- simpl. intros. etransitivity.
  Focus 2. apply commutes. 
  eapply (from_Proper (Adj_Hom_Iso F G X A' (G' B'))).
  apply commutes.
Defined.
