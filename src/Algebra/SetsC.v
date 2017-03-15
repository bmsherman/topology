Require Import Prob.StdLib Coq.Classes.CRelationClasses.

Set Universe Polymorphism.

Delimit Scope Subset_scope with Subset.
Local Open Scope Subset.

Infix "<-->" := iffT (at level 75) : Subset_scope.

Definition Subset@{A P} (A : Type@{A}) := A -> Type@{P}.

Section Defns.
Universes A.
Context {A : Type@{A}}.

Definition In@{P} (U : Subset@{A P} A) (x : A) := U x. 

Definition pointwise_op@{P Q PQ} (f : Type@{P} -> Type@{Q} -> Type@{PQ}) 
  (U : Subset@{A P} A) (V : Subset@{A Q} A) : Subset@{A PQ} A
  := fun a : A => f (U a) (V a).

Definition pointwise_rel@{P Q PQ} (f : Type@{P} -> Type@{Q} -> Type@{PQ}) 
  (U : Subset@{A P} A) (V : Subset@{A Q} A) : Type@{PQ}
  := forall a : A, f (U a) (V a).

Set Printing Universes.
Definition Intersection@{P Q PQ} : Subset@{A P} A -> Subset@{A Q} A -> Subset@{A PQ} A := pointwise_op prod.
Definition Union@{P Q PQ} : Subset@{A P} A -> Subset@{A Q} A -> Subset@{A PQ} A := pointwise_op sum.

Inductive Inhabited@{P} {U : Subset@{A P} A} :=
  Inhabited_intro : forall a : A, In U a -> Inhabited.
End Defns.

Axiom undefined : forall A, A.

Definition Included@{A P} {A} : 
  Subset@{A P} A -> Subset@{A P} A -> Type@{max(A,P)} := 
  fun U V => forall a : A, U a -> V a.

Definition Same_set@{A P AP} {A} : 
  Subset@{A P} A -> Subset@{A P} A -> Type@{AP} := 
  fun U V => forall a : A, U a <--> V a.

Arguments Inhabited {A} U.


Infix "⊆" := Included (at level 60) : Subset_scope.
Infix "∩" := Intersection (at level 50) : Subset_scope.
Infix "∪" := Union (at level 55) : Subset_scope.
Infix "===" := Same_set (at level 70) : Subset_scope.

Definition RelIncl@{A B P ABP} 
  {A : Type@{A}} {B : Type@{B}} : 
  (A -> B -> Type@{P}) -> (A -> B -> Type@{P}) -> Type@{ABP} := 
  fun F G => forall a : A, Included@{B P} (F a) (G a).

Definition RelSame@{A B P ABP} 
  {A : Type@{A}} {B : Type@{B}} : 
  (A -> B -> Type@{P}) -> (A -> B -> Type@{P}) -> Type@{ABP} :=
  fun F G => forall a : A, Same_set@{B P ABP} (F a) (G a).

Infix "⊑" := RelIncl (at level 60) : Subset_scope.
Infix "====" := RelSame (at level 70) : Subset_scope.

Definition compose {S T U} (F : S -> T -> Type)
  (G : T -> U -> Type) (s : S) (u : U) : Type :=
    { t : T & (F s t * G t u)%type }.

Theorem Included_impl@{A P AP} {A} (U V : Subset@{A P} A) :
  (forall x : A, U x -> V x) <--> (U ⊆ V : Type@{AP}).
Proof. firstorder. Qed.

Theorem Same_set_iff@{A P AP} A (U V : Subset@{A P} A) :
  (forall x, U x <--> V x) <--> (Same_set@{A P AP} U V).
Proof.
firstorder.
Qed.

Inductive union@{S T PS PT} {S T} (U : Subset@{S PS} S) 
  (f : S -> Subset@{T PT} T) (b : T) : Type@{PT} :=
  union_intro : forall a, In U a -> f a b -> In (union U f) b.

Theorem Union_union : forall (A B : Type) (a b : Subset A) (f : A -> Subset B),
  union a f ∪ union b f === union (a ∪ b) f.
Proof.
intros. constructor; unfold Included; intros X.
- destruct X; destruct u; econstructor; eauto; firstorder.
- destruct X; destruct i; [ left | right]; econstructor; eauto.
Qed.

Theorem union_Intersection : 
  forall (A B : Type) (a b : Subset A) (f : A -> Subset B),
  union (a ∩ b) f ⊆ union a f ∩ union b f.
Proof.
intros. apply Included_impl; intros. 
destruct X. destruct i. constructor; econstructor; eassumption.
Qed.

Lemma union_eq A B (x: A) (f : A -> Subset B) :
  union (eq x) f ⊆ f x.
Proof.
apply Included_impl; intros.
destruct X. induction i. assumption.
Qed.


Theorem Intersection_Included_l : forall A (U V : Subset A),
  U ∩ V ⊆ U.
Proof.
firstorder.
Qed.

Theorem Intersection_Included_r : forall A (U V : Subset A),
  U ∩ V ⊆ V.
Proof.
firstorder.
Qed.

Lemma Intersection_Included {T} {A B C : Subset T} :
  A ⊆ B -> A ⊆ C -> A ⊆ B ∩ C.
Proof.
firstorder.
Qed.

Lemma Intersection_assoc {T} {A B C : Subset T} :
  A ∩ (B ∩ C) === (A ∩ B) ∩ C.
Proof.
firstorder.
Qed.

Lemma Intersection_comm {T} {A B : Subset T} :
  A ∩ B === B ∩ A.
Proof.
firstorder.
Qed.

Theorem Union_Included_l : forall A (U V : Subset A),
  U ⊆ U ∪ V.
Proof.
firstorder.
Qed.

Theorem Union_Included_r : forall A (U V : Subset A),
  V ⊆ U ∪ V.
Proof.
firstorder.
Qed.

Require Import CMorphisms.

Instance Intersection_Proper_le : forall U,
  Proper (Included ==> Included ==> Included) (@Intersection U).
Proof.
intros. unfold Proper, respectful.
firstorder.
Qed.

Instance Intersection_Proper : forall U,
  Proper (Same_set ==> Same_set ==> Same_set) (@Intersection U).
Proof.
intros. unfold Proper, respectful.
firstorder.
Qed.

Instance Union_Proper_le : forall U,
  Proper (Included ==> Included ==> Included) (@Union U).
Proof.
intros. unfold Proper, respectful.
firstorder.
Qed.

Instance Included_Reflexive@{A P} : forall U, Reflexive (@Included@{A P} U).
Proof.
intros. unfold Reflexive. firstorder.
Qed.

Instance Included_Transitive@{A P} : forall U, Transitive (@Included@{A P} U).
Proof.
intros. unfold Transitive. firstorder.
Qed.

Instance Included_subrelation : forall U, subrelation (@Same_set U) (@Included U).
Proof.
intros. unfold subrelation. firstorder.
Qed.

Instance Included_Proper : forall U, Proper (@Same_set U ==> @Same_set U ==> iffT)
  (@Included U).
Proof.
intros. unfold Proper, respectful. firstorder.
Qed.

Require RelationClasses.
Instance RelIncl_PreOrder : forall A B, PreOrder (@RelIncl A B).
Proof.
intros. constructor; unfold Reflexive, Transitive, RelIncl; intros.
- reflexivity. 
- transitivity (y a); auto.
Qed.

Instance Same_set_Equivalence@{A P AP} : forall U, Equivalence (@Same_set@{A P AP} U).
Proof. intros. unfold Same_set. constructor;
  unfold Reflexive, Symmetric, Transitive; firstorder.
Qed.


Instance RelSame_Equivalence : forall A B, Equivalence (@RelSame A B).
Proof. intros. unfold RelSame. constructor;
  unfold Reflexive, Symmetric, Transitive; intros.
- reflexivity.
- symmetry. auto.
- transitivity (y a); auto.
Qed.

Require Coq.Setoids.Setoid.
Instance RelIncl_Proper : forall A B, Proper (RelSame ==> RelSame ==> iffT)
  (@RelIncl A B).
Proof.
intros. unfold Proper, respectful, RelIncl, RelSame. intros. 
  split; intros; apply Included_impl; intros.
- apply X0. apply X1. apply X. assumption. 
- apply X0. apply X1. apply X. assumption.
Qed.

Lemma Included_Same_set@{A P AP} : forall A (U V : Subset@{A P} A),
  U ⊆ V -> V ⊆ U -> Same_set@{A P AP} U V.
Proof.
  firstorder.
Qed.

Lemma Same_set_Included@{A P AP} {A} (U V : Subset@{A P} A) : 
  Same_set@{A P AP} U V -> ((U ⊆ V) * (V ⊆ U))%type.
Proof.
intros H. unfold Same_set, pointwise_rel, iffT in H.
unfold Included, pointwise_rel, arrow.
split; apply H.
Qed.

Lemma RelIncl_RelSame : forall A B (F G : A -> B -> Type),
  F ⊑ G -> G ⊑ F -> F ==== G.
Proof.
unfold RelIncl, RelSame; intros. apply Included_Same_set; auto.
Qed.

Lemma RelSame_RelIncl@{A B P ABP} (A : Type@{A}) B (F F' : A -> Subset@{B P} B) :
  RelSame@{A B P ABP} F F' -> F ⊑ F'.
Proof.
unfold RelSame, RelIncl.
intros. unfold Included, pointwise_rel, arrow; intros. 
apply X. assumption.
Qed.

Lemma RelSame_iffT {A B} (R S : A -> B -> Type) :
  (forall a b, R a b <--> S a b) <--> (R ==== S).
Proof.
firstorder.
Qed.

Instance RelSame_Proper : forall A B, Proper (RelSame ==> RelSame ==> iffT)
  (@RelSame A B).
Proof.
intros. unfold Proper, respectful, RelSame. intros. split; intros.
- rewrite <- X, <- X0. auto.
- rewrite X, X0. auto.
Qed.

Lemma union_compose : forall A B C (H : Subset A) (G : A -> Subset B) 
  (F : B -> Subset C),
  union (union H G) F === union H (compose G F).
Proof.
intros. apply Same_set_iff. intros; split; intros.
- destruct X. destruct i. repeat (econstructor || eauto).
- destruct X. destruct c. destruct p.
  repeat (econstructor || eauto).
Qed.

Lemma union_idx_monotone : forall A B (U V : Subset A) (F : A -> B -> Type),
  U ⊆ V -> union U F ⊆ union V F.
Proof.
intros. apply Included_impl; intros.
destruct X0. econstructor; eauto.
apply X. assumption.
Qed.

Lemma union_monotone : forall A B (U : Subset A) (F G : A -> B -> Type),
  F ⊑ G -> union U F ⊆ union U G.
Proof.
intros. apply Included_impl; intros.
destruct X0. econstructor. eassumption. apply X. assumption.
Qed.

Local Instance union_Proper : forall A B, 
  Proper (Included ==> RelIncl ==> Included) (@union A B).
Proof.
intros. unfold Proper, respectful.
intros. etransitivity. apply union_idx_monotone. eassumption. 
apply union_monotone. assumption.
Qed.

Local Instance Union_Proper_eq : forall A, 
  Proper (Same_set ==> Same_set ==> Same_set) (@Union A).
Proof.
  firstorder.
Qed.

Instance Union_Proper_le_flip : forall A,
  Proper (Included --> Included --> flip Included) (@Union A).
Proof.
  firstorder.
Qed.

Lemma Same_set_iff_In:
  forall (A : Type) (U V : Subset A),
  (forall x : A, In U x <--> In V x) -> U === V.
Proof.
apply Same_set_iff.
Qed.

Instance In_Proper : forall A,
  Proper (Included ==> eq ==> arrow) (@In A).
Proof.
unfold Proper, respectful, arrow. intros.
subst.  apply X. assumption.
Qed.

Instance In_Proper2 : forall A, 
  Proper (Included --> eq --> flip arrow) (@In A).
Proof.
unfold Proper, respectful, flip, arrow. intros.
subst.  apply X. assumption.
Qed.

Lemma Inhabited_mono {A} {U V : Subset A} : U ⊆ V -> Inhabited U -> Inhabited V.
Proof.
intros. destruct X0. exists a.  apply X. assumption.
Qed.

Instance Inhabited_Proper_le {A} : Proper (Included ==> arrow) (@Inhabited A).
Proof.
unfold Proper, respectful, arrow. intros. eapply Inhabited_mono; eassumption.
Qed.