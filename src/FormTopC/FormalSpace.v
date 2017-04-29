Require Import
  Prob.StdLib
  Algebra.Category
  CMorphisms
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  Types.Setoid
  FormTopC.FormTop
  FormTopC.Cont.

Set Universe Polymorphism.

(** Bundle the definitions together *)
(* Inductively generated formal topology *)
Record IGt@{A P I API} : Type :=
  { IGS :> PreISpace.t@{A P I}
  ; IGPO : PreO.t (le IGS)
    (** the proof that [le] is a preorder *)
 (* ; IGpos : FormTop.gtPos@{A P I API} IGS
    (** The space must have a positivity predicate. *) *)
  }.

Global Instance IGT_PreO@{A P I API} 
  (X : IGt@{A P I API}) : PreO.t (le X) := IGPO X.
Global Instance IGTFT@{A P I API API'} (X : IGt@{A P I API}) : 
  FormTop.t (toPSL (IGS X)) :=
  FormTop.GCovL_formtop@{A P I API API'} _.


Record t@{A P I} : Type :=
  { S :> PreSpace.t@{A P I}
  ; PO : PreO.t@{A P} (le S)
  ; isFT : FormTop.t S
  }.

Local Open Scope FT.

Delimit Scope loc_scope with loc.
Local Open Scope loc.

Definition fromIGt@{A P I API API'} (A : IGt@{A P I API}) : t@{A P I} :=
  {| S := toPSL (IGS A)
   ; isFT := IGTFT@{A P I API API'} A|}.

Coercion fromIGt : IGt >-> t.

Local Instance FT (A : t) : FormTop.t A := isFT A.
Local Instance PreO (X : t) : PreO.t (le (PreSpace.S X)) := PO X.

Section Properness.
Require Import CMorphisms.
Context {A : t}.

Definition refl a U : In U a -> a <|[A] U.
Proof.
intros. apply FormTop.refl. assumption.
Qed.

Definition le_left (a b : S A) (U : Open A)
  : a <=[PreSpace.S A] b -> b <|[A] U -> a <|[A] U.
Proof.
intros; eapply FormTop.le_left; eassumption.
Qed.

Definition trans {a U} :
  a <|[A] U -> forall V, U <<|[A] V -> a <|[A] V.
Proof.
intros. eapply FormTop.trans; eassumption.
Qed.

Local Open Scope Subset.

Definition le_right {a U V} :
  a <|[A] U -> a <|[A] V ->
  a <|[A] U ↓ V.
Proof.
auto using @FormTop.le_right with typeclass_instances.
Qed.

Definition monotone (U V : Subset (S A))
  : U ⊆ V -> forall a : S A, a <|[A] U -> a <|[A] V.
Proof.
apply FormTop.monotone.
Qed.

Instance Cov_Proper :
  Proper (le (PreSpace.S A) --> Included ==> Basics.arrow) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper.
Qed.

(** This is just a flipped version of what's above. It
    shouldn't be needed. *)

Instance Cov_Proper3  :
  Proper (le (PreSpace.S A) ==> Included --> flip Basics.arrow) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper3.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper2.
Qed.

End Properness.

Ltac trans H := apply (trans H); let T := type of H in 
  match constr:(T) with
  | _ _ ?a _ => clear a H; intros a H
  end.

Ltac etrans := match goal with
     | [ H : ?Cov ?X ?a _  |- ?Cov ?X ?a _ ] => try (trans H)
     end.

Ltac join H1 H2 := let H := fresh H1 in
  pose proof (le_right H1 H2) as H; clear H1 H2.

Ltac ejoin := repeat match goal with
  | [ H1 : ?Cov ?A ?a _, H2 : ?Cov ?A ?a _  |- ?Cov ?A ?a _ ] => join H1 H2
  end.

Record cmap_car {LA LB : t} : Type :=
  { mp : Cont.map LA LB
  ; mp_ok : Cont.t LA LB mp
  }.

Arguments cmap_car LA LB : clear implicits.

Require Import Types.Setoid.

Lemma Equivalence_on {A B} 
  {R : crelation B}
  {H : Equivalence R}
  (f : A -> B)
  : Equivalence (fun x y => R (f x) (f y)).
Proof.
econstructor; unfold Reflexive, Symmetric, Transitive; intros.
- reflexivity.
- symmetry; assumption.
- etransitivity; eassumption.
Qed.

Definition cmap (LA LB : t) : Setoid.
Proof.
unshelve eapply (
  {| sty := cmap_car LA LB
   ; seq := fun f g => Cont.func_EQ (mp f) (mp g)
  |}).
apply Equivalence_on. 
Defined.

Infix "~~>" := cmap (at level 75) : loc_scope.

Definition id {LA : t} : LA ~~> LA := 
  {| mp := Cont.id
  ; mp_ok := Cont.t_id |}.

Definition comp {LA LB LD : t} 
  (f : LB ~~> LD) (g : LA ~~> LB) : LA ~~> LD :=
  {| mp := SetsC.compose (mp f) (mp g) 
  ; mp_ok := Cont.t_compose (mp g) (mp f) (mp_ok g) (mp_ok f)
  |}.

Infix "∘" := comp (at level 40, left associativity) : loc_scope.

Definition LE_map {A B : t} (f g : A ~~> B)
  := Cont.func_LE (S := A) (mp f) (mp g).

Local Open Scope setoid.

Lemma LE_map_antisym {A B : t} (f g : A ~~> B)
  : LE_map f g -> LE_map g f -> f == g.
Proof.
unfold LE_map. intros.
apply Cont.func_LE_antisym; assumption.
Qed.

Lemma EQ_map_LE {A B : t} (f g : A ~~> B)
  : f == g -> LE_map f g.
Proof.
unfold LE_map. intros.
apply Cont.func_EQ_LE. assumption.
Qed.

Require Import CRelationClasses.

Instance LE_map_PreOrder {A B} : PreOrder (@LE_map A B).
Proof.
constructor; unfold Reflexive, Transitive, LE_map;
  intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Lemma LE_map_compose {A B C} {f f' : A ~~> B}
  {g g' : B ~~> C}
  : LE_map f f' -> LE_map g g'
  -> LE_map (g ∘ f) (g' ∘ f').
Proof.
unfold LE_map in *.
intros. apply Cont.compose_proper_LE;
  try assumption. apply f'.
Qed.

Lemma EQ_map_compose {A B C} {f f' : A ~~> B}
  {g g' : B ~~> C}
  : f == f' -> g == g'
  -> g ∘ f == g' ∘ f'.
Proof.
intros. apply Cont.compose_proper;
  (apply mp_ok || assumption).
Qed.

Definition map_Sat {A B : t} (f : A ~~> B)
  : A ~~> B.
Proof.
unshelve eapply (
  {| mp := Cont.Sat (S := A) (mp f) |}).
apply Cont.t_Sat. apply mp_ok.
Defined.

Lemma map_Sat_EQ {A B : t} (f : A ~~> B)
  : f == map_Sat f.
Proof.
apply Cont.Sat_idempotent.
Qed.

Lemma EQ_map_Sat {A B : t} {f g : A ~~> B}
  : f == g 
  -> map_Sat f == map_Sat g.
Proof.
eapply Cont.func_EQ_Sat.
Qed.

Local Open Scope Subset.

Lemma Sat_Proper {A B : PreSpace.t}
 `{FTA : FormTop.t A} {F_ G_ : Cont.map A B}
  : F_ ==== G_ -> Cont.Sat F_ ==== Cont.Sat G_.
Proof.
intros H.
apply RelIncl_RelSame; apply Cont.Sat_mono;
  apply RelSame_RelIncl. assumption.
symmetry. assumption.
Qed.

Definition t_Cat : Category.
Proof.
unshelve eapply (
  {| Ob := t
  ; Category.arrow := cmap
  ; Category.id := @id
  ; Category.compose := @comp |}); intros.
- apply EQ_map_compose; assumption.
- simpl. unfold Cont.id.
  unfold Cont.func_EQ, Cont.Sat.
  intros b a. split; intros H.
  + FormTop.etrans. destruct H as (x & l & m).
    apply cov_singleton in l.
    pose proof (Cont.cov (mp_ok f) (eq b) m l).
    clear m l x.
    eapply FormTop.monotone. 2: eassumption.
    apply union_eq.
  + eapply FormTop.monotone. 2: eassumption.
    intros x fx.
    unfold compose. exists b. split. reflexivity.
    assumption.
- apply Sat_Proper. simpl. intros b a.
  split; intros H.
  + destruct H as (? & ? & ?).
    unfold Cont.id in *.
    eapply (Cont.le_left (mp_ok f)); eassumption.
  + exists a. split. assumption. unfold Cont.id. reflexivity.
- simpl. unfold Cont.func_EQ.
  apply Sat_Proper. apply compose_assoc.
Defined.

Require Import CRelationClasses.
Lemma truncate_Equiv A (f : crelation A) :
  Equivalence f -> RelationClasses.Equivalence (fun x y => inhabited (f x y)).
Proof.
intros H. constructor;
  unfold RelationClasses.Reflexive,
         RelationClasses.Symmetric,
         RelationClasses.Transitive; intros.
- constructor. reflexivity.
- destruct H0. constructor. symmetry. assumption.
- destruct H0, H1. constructor. etransitivity; eassumption.
Qed.

Section IGProps.

Context {A : IGt}.

Lemma igl_ax_cov {a b : A}
  (H : a <=[A] b) (ix : PreISpace.Ix A b)
  : a <|[A] eq a ↓ PreISpace.C A b ix.
Proof.
apply FormTop.gle_infinity with b ix. 
assumption.
intros. eapply (FormTop.refl (A := A)). assumption.
Qed.

Lemma ig_ax_cov (a : A)
  (ix : PreISpace.Ix A a) :
  a <|[A] PreISpace.C A a ix.
Proof.
pose proof (@igl_ax_cov a a (PreO.le_refl a) ix) as X.
apply cov_downset.
eapply FormTop.gmonotoneL. 
eapply Intersection_Included_r.
apply X.
Qed.


End IGProps.