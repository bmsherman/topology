Set Universe Polymorphism. 

(** I will try to use the same names for the operations
    that there are in Coq *)
Require Import 
  CRelationClasses 
  CMorphisms
  Types.Setoid.

Reserved Notation "a ~~> b" (at level 75).
Reserved Notation "a == b" (at level 70, no associativity).
Reserved Notation "g ∘ f" (at level 40, left associativity).

Local Open Scope setoid.

Record Category@{Ob Arr P} :=
  { Ob :> Type@{Ob}
  ; arrow : Ob -> Ob -> Setoid@{Arr P} where "a ~~> b" := (arrow a b)
  ; id : forall {A}, A ~~> A
  ; compose : forall {A B C}, B ~~> C -> A ~~> B -> A ~~> C where "g ∘ f" := (compose g f)
  ; compose_proper : forall {A B C} (f f' : A ~~> B) (g g' : B ~~> C),
       g == g' -> f == f'-> g ∘ f == g' ∘ f'
  ; compose_id_left : forall {A B} (f : A ~~> B), id ∘ f == f
  ; compose_id_right : forall {A B} (f : A ~~> B), f ∘ id == f
  ; compose_assoc : forall {A B C D} (f : A ~~> B) (g : B ~~> C) (h : C ~~> D), h ∘ (g ∘ f) == (h ∘ g) ∘ f
  }.

Arguments arrow {c} A B : clear implicits.
Arguments id {c A} : clear implicits.
Arguments compose {c A B C} f g : clear implicits.
Arguments compose_id_left {c A B} f : clear implicits.
Arguments compose_id_right {c A B} f : clear implicits.

(** Notation for objects of categories *)
Delimit Scope obj_scope with obj.
Local Open Scope obj.
Infix "~~>" := (arrow) (at level 75) : obj_scope.
Notation "a ~~>[ X ] b" := (arrow (c := X) a b) (at level 75, format "a  ~~>[ X ]  b") : obj_scope.

Delimit Scope morph_scope with morph.
Local Open Scope morph.

Infix "∘" := (compose) (at level 40, left associativity) : morph_scope.


Ltac prove_map_Proper := unfold Proper, respectful; intros;
  repeat match goal with
  | [ H : (_ == _)%morph |- (_ == _)%morph ] => rewrite H; clear H
  end; try reflexivity.

Require Coq.Setoids.Setoid.
Global Instance compose_Proper {U : Category} : forall A B C : U,
  Proper (seq (B ~~> C) ==> seq (A ~~> B) ==> seq (A ~~> C)) compose.
Proof. 
intros. unfold Proper, respectful.
intros. apply compose_proper; assumption.
Qed.

Section Defns.
Context {U : Category}.

Definition Mono {A B : U} (f : A ~~> B) :=
  forall X (g1 g2 : X ~~> A), f ∘ g1 == f ∘ g2 -> g1 == g2.

Definition Epi {A B : U} (f : B ~~> A) :=
  forall X (g1 g2 : A ~~> X), g1 ∘ f == g2 ∘ f -> g1 == g2.

Lemma Mono_Proper : forall {A B}, Proper (seq _ ==> iffT) (Mono (A:=A) (B:=B)).
Proof. 
intros. unfold Proper, respectful. intros.
split.
- intros Mx. unfold Mono; intros.
  apply Mx. rewrite X. assumption.
- intros My.
  unfold Mono; intros. apply My. rewrite <- X. assumption.
Qed.

Lemma Mono_Compose : forall {A B C} {f : A ~~> B} {g : B ~~> C},
  Mono f -> Mono g -> Mono (g ∘ f).
Proof.
intros A B C f g Mf Mg.
unfold Mono; intros X h1 h2 H.
rewrite <- !compose_assoc in H.
apply Mg in H. apply Mf in H. exact H.
Qed.

Record Iso {A B : U} : Type :=
  { to   : A ~~> B
  ; from : B ~~> A
  ; to_from : to ∘ from == id
  ; from_to : from ∘ to == id
  }.

End Defns.

Arguments Iso {U} A B : clear implicits.

Infix "≅" := Iso (at level 70, no associativity) : obj_scope.

Ltac remove_eq_left :=
  repeat rewrite <- compose_assoc; repeat (apply compose_Proper; try reflexivity).
Ltac remove_eq_right :=
  repeat rewrite compose_assoc; repeat (apply compose_Proper; try reflexivity).

Section Iso_Props.

Universes Ob Arr P.
Context {U : Category@{Ob Arr P}}.
  
Lemma Iso_Mono : forall {A B : U} (x : A ≅ B), Mono (to x).
Proof. 
intros A B x. destruct x as [f g fg gf].
simpl. unfold Mono.
intros X h k fhfk.
rewrite <- (compose_id_left h), <- (compose_id_left k).
rewrite <- !gf.
rewrite <- !compose_assoc.
apply compose_Proper; try reflexivity; try assumption.
Qed.
  
Lemma Iso_Epi : forall {A B : U} (x : A ≅ B), Epi (to x).
Proof.
intros A B x. destruct x as [f g fg gf].
simpl. unfold Epi.
intros X h k fhfk.
rewrite <- (compose_id_right h), <- (compose_id_right k).
rewrite <- !fg.
rewrite -> !compose_assoc.
apply compose_Proper; try reflexivity; try assumption.
Qed.

Lemma Iso_Refl {A : U} : A ≅ A.
Proof.
refine ( {| to := id ; from := id |});
apply compose_id_left.
Defined.

Definition Iso_Sym {A B : U} (i : A ≅ B) : B ≅ A :=
  {| to := from i
     ; from := to i
     ; to_from := from_to i
     ; from_to := to_from i
  |}.

Axiom undefined : forall A, A.

Lemma Iso_Trans {A B C : U} (ab : A ≅ B) (bc : B ≅ C) : A ≅ C.
Proof.
refine ({| to := to bc ∘ to ab
           ; from := from ab ∘ from bc |}).
(*
etransitivity. symmetry. apply compose_assoc.
etransitivity. apply compose_proper. reflexivity. 
apply (compose_assoc _ (from bc)). 
etransitivity. apply compose_proper. reflexivity.
apply compose_proper. apply to_from. reflexivity.
etransitivity. apply compose_proper. reflexivity.
apply compose_id_left. apply to_from.
*)

- rewrite <- compose_assoc.
  rewrite (compose_assoc _ (from bc)).
  rewrite to_from. rewrite compose_id_left.
  apply to_from.
- rewrite <- compose_assoc.
  rewrite (compose_assoc _ (to ab)).
  rewrite from_to. rewrite compose_id_left.
  apply from_to.
Defined.

Definition Hom_Setoid (A B : U) :=
  {| Setoid.sty := A ~~> B
   ; Setoid.seq := eq
  |}.

Lemma Hom_Setoid_Iso {A A' B B' : U}
      (a : A ≅ A') (b : B ≅ B')
  : ((A ~~> B) ≅ (A' ~~> B'))%setoid.
Proof.
unshelve econstructor; simpl.
- exact (fun f => to b ∘ f ∘ from a).
- exact (fun f => from b ∘ f ∘ to a).
- unfold Proper, respectful. intros x y H.
  rewrite H; reflexivity.
- unfold Proper, respectful. intros x y H.
  rewrite H; reflexivity.
- simpl. intros. rewrite !compose_assoc.
  rewrite (to_from b). rewrite compose_id_left.
  rewrite <- compose_assoc. rewrite to_from.
  apply compose_id_right.
- simpl. intros. rewrite !compose_assoc.
  rewrite from_to. rewrite compose_id_left.
  rewrite <- compose_assoc. rewrite from_to.
  apply compose_id_right.
Defined.

End Iso_Props.
