Require Import 
  Algebra.SetsC
  Algebra.OrderC
  CMorphisms
  Prob.StdLib
  Types.UIP.

Set Universe Polymorphism.

Local Open Scope Subset.

Record PreOrder :=
  { PO_car :> Type
    (** The type of basic opens, i.e., observable property *)
  ; le : crelation PO_car
    (** a preorder on [S] which indicates when one basic open lies in another,
       i.e., one observable property implies another *)
   }.

Infix "<=" := (le _) : FT_scope.
Notation "a <=[ X ] b" := (le X a b) (at level 40, format "a  <=[ X ]  b").

Definition Open@{A P} (A : PreOrder@{A P}) := Subset@{A P} A.
Delimit Scope FT_scope with FT.

Local Open Scope FT.

Set Printing Universes.

Definition downset@{A P} {A : PreOrder@{A P}} (U : Open A) : Open A :=
  union U (fun x y => y <= x).

Notation "⇓ U" := (downset U) (at level 30).

Definition down@{A P} {A : PreOrder@{A P}} (U V : Open A) : Open A :=
  ⇓ U ∩ ⇓ V.

Infix "↓" := (down) (at level 30).

Section Down_Props.
Context {A : PreOrder}.

Lemma downset_included {PO : PreO.t (le A)} : forall (V : Open A),
   V ⊆ ⇓ V.
Proof.
intros. unfold Included, pointwise_rel, arrow; intros.
econstructor. eassumption. reflexivity.
Qed.

Lemma downset_Proper_impl : Proper (Included ==> Included)
  (@downset A).
Proof.
unfold Proper, respectful.
intros. unfold Included, In, pointwise_rel, arrow.
firstorder. unfold downset. exists a0. apply X. assumption. assumption.
Qed.

Instance downset_Proper : Proper (Same_set ==> Same_set) (@downset A).
Proof.
unfold Proper, respectful. intros.
apply Same_set_Included in X. destruct X. 
apply Included_Same_set; apply downset_Proper_impl; try assumption;
  unfold respectful, arrow; intros; subst.
Qed.

Context {PO : PreO.t (le A)}.

Lemma down_intersection {U V : Subset A} :
  U ∩ V ⊆ U ↓ V.
Proof.
apply Included_impl. intros. destruct X.
unfold down. split; exists x;
  (assumption || reflexivity).
Qed.

Lemma downset_down_incl {U V : Subset A} :
  ⇓ (U ↓ V) === ⇓ (U ∩ V).
Proof.
Abort.

Lemma downset_down {U V : Subset A} :
  ⇓ (U ↓ V) === U ↓ V.
Proof.
apply Included_Same_set.
- unfold down. apply Intersection_Included.
  + apply Included_impl; intros. destruct X.
    destruct i. destruct d.
    eexists. eassumption. etransitivity; eassumption.
  + apply Included_impl; intros. destruct X.
    destruct i. destruct d0. eexists. eassumption.
    etransitivity; eassumption.
- apply downset_included.
Qed.

Lemma downset_idempotent (U : Subset A) : 
 ⇓ (⇓ U) === ⇓ U.
Proof.
unfold downset. apply Same_set_iff. intros. split; intros.
- destruct X. destruct i. econstructor. eassumption.
  etransitivity; eassumption.
- exists x. assumption. reflexivity.
Qed.

Lemma down_assoc {U V W : Subset A} :
  (U ↓ V) ↓ W === U ↓ (V ↓ W).
Proof.
unfold down at 1 3.
rewrite !downset_down. unfold down.
symmetry.
apply Intersection_assoc.
Qed.

Lemma le_down {a b : A} : a <=[A] b
  -> eq a ↓ eq b === ⇓ (eq a).
Proof.
intros H. apply Included_Same_set.
- unfold down. apply Intersection_Included_l.
- apply Included_impl. intros. destruct X.
  unfold In in i. subst. split.
  eexists. reflexivity. eassumption. eexists.
  reflexivity. etransitivity; eassumption.
Qed.

Lemma down_eq {a b : A}
 : forall c : A, ((c <= a) * (c <= b))%type <--> (eq a ↓ eq b) c.
Proof.
intros. split; intros. 
- destruct X. split; (eexists; [reflexivity | eassumption]).
- destruct X. destruct d, d0. unfold In in *. subst. 
  split; assumption. 
Qed.

Lemma down_Proper {U V U' V' : Subset A} :
  U ⊆ U' -> V ⊆ V' -> U ↓ V ⊆ U' ↓ V'.
Proof.
intros HU HV. unfold down.
apply Intersection_Included.
- etransitivity. apply Intersection_Included_l. 
  apply downset_Proper_impl. assumption.
- etransitivity. apply Intersection_Included_r.
  apply downset_Proper_impl; assumption.
Qed.

Lemma down_comm {U V : Subset A}
  : U ↓ V === V ↓ U.
Proof.
unfold down. apply Intersection_comm.
Qed.

End Down_Props.

Lemma le_down1@{A P} {A : PreOrder@{A P}} {H : PreO.t@{A P} (le A)} (a b : A)
  : a <=[A] b <--> (⇓ eq b) a.
Proof.
split; intros X.
- exists b. reflexivity. assumption.
- destruct X. unfold In in i. subst. assumption.
Qed.

Lemma union_down {A B : PreOrder}
  (U : Subset A)
  (F : A -> B -> Type)
  : union U (fun a => ⇓ F a) === ⇓ union U F.
Proof.
intros b; split.
- intros H. destruct H. destruct d.
eexists. 2:eassumption.
econstructor; eassumption.
- intros H.  destruct H.  destruct i.
  eexists. eassumption. eexists; eassumption.
Qed.

Ltac le_down := rewrite <- !le_down1.
Ltac le_downH H := rewrite <- !le_down1 in H.


Definition BProdPO (A B : PreOrder) : PreOrder :=
  {| PO_car := A * B
  ; le := prod_op (le A) (le B) |}.

Section Sum.
Universes A P Ix.
Context {Ix : Type@{Ix}}.
Context {Ix_UIP : EqdepFacts.UIP_ Ix}.
Context {X : Ix -> PreOrder@{A P}}.

(** See
  https://www.cs.bham.ac.uk/~sjv/InfiniteTych.pdf
*)
Record SomeOpen_car@{} : Type@{A} :=
  { SOIx : Ix
  ; SOOpen : X SOIx
  }.

Inductive SomeOpen_le : SomeOpen_car -> SomeOpen_car -> Type :=
  | MkSomeOpen_le : forall ix (aix bix : X ix),
     aix <=[X ix] bix
     -> SomeOpen_le (Build_SomeOpen_car ix aix) (Build_SomeOpen_car ix bix).

Definition SomeOpen : PreOrder :=
  {| PO_car := SomeOpen_car
  ;  le := SomeOpen_le
  |}.

Definition MkSomeOpen (ix : Ix) (u : X ix) : SomeOpen
  := Build_SomeOpen_car ix u.

Context {PO : forall ix : Ix, PreO.t (le (X ix))}.

Instance Sum_PO : PreO.t SomeOpen_le.
Proof.
constructor; simpl; intros.
- destruct x. econstructor. reflexivity.
- induction X0. UIP_inv X1.
  econstructor. etransitivity; eassumption.
Qed.

End Sum.

Arguments SomeOpen {Ix} X.