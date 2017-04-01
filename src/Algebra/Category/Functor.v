Require Import 
  Types.Setoid
  Algebra.Category.

Set Universe Polymorphism.

Local Open Scope obj.
Local Open Scope morph.
Local Open Scope setoid.

Require Import Morphisms.

Section Functor. 

Context {C D : Category}.

Record Functor : Type := Build_Functor
  { fobj :> C -> D
  ; fmap : forall {A B : C}, function (A ~~> B) (fobj A ~~> fobj B)
  ; fmap_id : forall {A : C}, fmap (id : A ~~> A) == id
  ; fmap_compose : forall {X Y Z : C} (f : X ~~> Y) (g : Y ~~> Z),
      fmap (g ∘ f) == fmap g ∘ fmap f
  }.

Record NatTrans (F G : Functor) :=
  { nattrans :> forall (A : C), F A ~~> G A
  ; nattrans_ok : forall A B (ext : A ~~> B),
      fmap G ext ∘ nattrans A == nattrans B ∘ fmap F ext
  }.

End Functor.

Arguments Functor C D : clear implicits.

Definition id_Functor {C : Category} : Functor C C.
Proof.
unshelve econstructor.
- exact (fun x => x).
- simpl. intros. apply Setoid.id.
- simpl. intros; reflexivity.
- simpl. intros; reflexivity.
Defined.

Delimit Scope cat_scope with cat.
Local Open Scope cat.

Infix "==>" := Functor (at level 55, right associativity) : cat_scope.

Delimit Scope functor_scope with functor.
Local Open Scope functor.

Definition compose_Functor {C D E : Category}
  (G : D ==> E) (F : C ==> D)
  : C ==> E.
Proof.
unshelve econstructor.
- exact (fun x => G (F x)).
- intros. apply (fmap G ∘ fmap F)%setoidc.
- intros. simpl. rewrite !fmap_id. reflexivity.
- simpl. intros. rewrite !fmap_compose. reflexivity.
Defined. 

Infix "∘" := compose_Functor : functor_scope.

Definition Faithful {C D} (F : C ==> D) :=
  forall (A B : C) (f g : A ~~> B), fmap F f == fmap F g -> f == g.

Definition Full {C D} (F : C ==> D) :=
  forall (A B : C) (f : F A ~~> F B), 
     sigT (fun f' : A ~~> B => f == fmap F f').

(** Probably not strong enough *)
Record Adjunction {C D : Category}
  {F : Functor C D} {G : Functor D C} : Type :=
  { Adj_Hom_Iso : forall A B, ((A ~~> G B)%obj ≅ (F A ~~> B)%obj)%setoidc
  ; commutes :
     forall {A A' B B'} (f : A' ~~> A) (g : B ~~> B')
      (x : F A ~~> B),
    (Setoid.from (Adj_Hom_Iso _ _) (g ∘ x ∘ fmap F f)
   == fmap G g ∘ Setoid.from (Adj_Hom_Iso _ _) x ∘ f)%morph
  }.

Arguments Adjunction {C D} F G.

Infix "-|" := Adjunction (at level 30) : functor_scope.

Lemma compose_Adjunction 
  {C D E : Category}
  {F : Functor C D} {G : Functor D C}
  {F' : Functor D E} {G' : Functor E D}
  : F -| G -> F' -| G' -> (F' ∘ F) -| (G ∘ G').
Proof.
intros. unshelve econstructor. 
- intros. eapply Setoid.Iso_Trans. simpl in *.
eapply X. simpl. eapply X0.
- simpl. intros. etransitivity.
  Focus 2. apply commutes.
  apply sf_proper. apply commutes.
Defined.