Require Import 
  Coq.Lists.List
  CMorphisms.
Import ListNotations.

Set Universe Polymorphism.

Inductive member {A} : A -> list A -> Type :=
| here : forall {x xs}, member x (x :: xs)
| there : forall {x y ys}, member x ys -> member x (y :: ys).

Lemma member_map {A B} (f : A -> B) {x : A} {xs : list A}
      (elem : member x xs)
  : member (f x) (List.map f xs).
Proof.
  induction elem; simpl. constructor. constructor. assumption.
Defined.

Inductive EachI {A} {B : A -> Type} : list A -> Type :=
  | Each_nil : EachI nil
  | Each_cons : forall {x : A} {xs : list A}, B x -> EachI xs -> EachI (x :: xs).

Arguments EachI {A} B xs.

Inductive SomeI {A} {B : A -> Type} : list A -> Type :=
  | Some_here : forall {x xs}, B x -> SomeI (x :: xs)
  | Some_there : forall {x xs}, SomeI xs -> SomeI (x :: xs).

Arguments SomeI {A} B xs.

(** Remove one element from a list. *)
Inductive Split {A} : list A -> A -> list A -> Type :=
  | Split_here : forall {x xs}, Split (x :: xs) x xs
  | Split_there : forall {x xs y ys}, Split xs y ys -> Split (x :: xs) y (x :: ys).

Ltac inv H := inversion H; clear H; subst.

Definition swap_member {X : Type} {A B C : X} {Γ : list X}
           (x : member C (A :: B :: Γ))
  : member C (B :: A :: Γ).
Proof.
  inv x. apply there. apply here.
  inv X0. apply here. apply there. apply there.
  assumption.
Defined.

Definition Each {A} (B : A -> Type) (xs : list A) : Type :=
  forall x, member x xs -> B x.

Require Import Algebra.SetsC.
Local Open Scope Subset.

Lemma Each_member {A} {B : A -> Type}
  : Each B === EachI B.
Proof.
intros xs.
split; intros H. 
- induction xs.
  + econstructor.
  + econstructor. apply H. econstructor.
    apply IHxs. unfold Each. 
    intros. apply H. econstructor. assumption.
- unfold Each; induction H; intros; inv X.
  + assumption.
  + apply IHEachI. assumption.
Qed.

Record LSome {A} {B : A -> Type} {xs : list A} : Type :=
  MkLSome
  { S_elem : A
  ; S_member : member S_elem xs
  ; S_holds : B S_elem
  }.

Arguments LSome {A} B xs.

Lemma Some_member {A} {B : A -> Type}
  : LSome B === SomeI B.
Proof.
intros xs.
split; intros H. 
- induction H. induction S_member0. 
  + econstructor. assumption.
  + econstructor 2. auto.
- induction H.
  + econstructor. econstructor. assumption.
  + induction IHSomeI. econstructor.
    econstructor 2. eassumption. assumption.
Qed.

Lemma member_rect1 :
  forall (A : Type) (P : forall (a : A) (b : A) (l : list A), member a (b :: l) -> Type),
    (forall (x : A) (xs : list A), P x x xs here) ->
    (forall (x y b : A) (ys : list A) (m : member x (b :: ys)),
        P x b ys m -> P x y (b :: ys) (there m)) ->
    forall (y : A) (b : A) (l : list A) (m : member y (b :: l)), P y b l m.
Proof.
  intros A P X X0.
  pose (fun l : list A => match l as ll return forall (a : A), member a ll -> Type with
                       | [] => fun a mem => False
                       | x :: xs => fun a => P a x xs
                       end) as P'.
  assert (forall l a mem, P' l a mem).
  intros.
  induction mem. 
  - simpl. auto.
  - simpl. destruct ys. simpl in *. contradiction. 
    apply X0.  simpl in IHmem. assumption.
  - intros. apply (X1 (b :: l) y m).
Defined.

Require Import CMorphisms.

Lemma member_app {A} {xs ys : list A} {x : A} :
  iffT (member x (xs ++ ys)) (member x xs + member x ys).
Proof.
split; intros.
- induction xs.
  + right. apply X.
  + inv X. left. apply here.
    destruct (IHxs X0). left. apply there.  assumption.
    right. assumption.
- induction xs. 
  + destruct X. inv m. assumption.
  + inv X. inv X0. apply here.
    simpl. apply there. apply IHxs. left. assumption.
    simpl. apply there. apply IHxs. right. assumption.
Qed.

Definition FSubset {A} (xs ys : list A) : Type :=
  forall a : A, member a xs -> member a ys.

Definition FSameset {A} (xs ys : list A) : Type :=
  forall a : A, iffT (member a xs) (member a ys).

Instance FSubset_PreOrder {A} : PreOrder (@FSubset A).
Proof.
firstorder.
Qed.

Instance FSameset_Equivalence {A} : Equivalence (@FSameset A).
Proof.
firstorder.
Qed.

Delimit Scope list_scope with list.
Local Open Scope list.

Infix "⊆" := FSubset (at level 60) : list_scope.
Infix "===" := FSameset (at level 70) : list_scope.

Lemma FSameset_FSubset {A} (xs ys : list A) :
  xs === ys -> ((xs ⊆ ys) * (ys ⊆ xs)).
Proof.
firstorder.
Qed.

Lemma FSubset_FSameset {A} (xs ys : list A) : 
  xs ⊆ ys -> ys ⊆ xs -> xs === ys.
Proof.
firstorder.
Qed.

Lemma FSubset_cons {A} (x : A) (xs ys : list A)
  : xs ⊆ ys -> (x :: xs) ⊆ (x :: ys).
Proof.
unfold FSubset. intros. inv X0.
- econstructor.
- econstructor 2. auto.
Qed.

Lemma FSubset_nil {A} (xs : list A)
  : [] ⊆ xs.
Proof.
unfold FSubset. intros. inv X.
Qed.

Lemma LSome_app {A} {B : A -> Type} {xs ys : list A}
  : LSome B (xs ++ ys) <--> LSome B xs + LSome B ys.
Proof.
split; intros H.
- induction H. apply member_app in S_member0.
  induction S_member0; [left | right]; econstructor; eassumption.
- induction H.
  + induction a. econstructor.
    eapply member_app. left. eassumption. assumption.
  + induction b. econstructor.
    eapply member_app. right. eassumption. eassumption.
Qed.

Lemma member_singleton {A} (x y : A)
  : member x [y] <--> x = y.
Proof.
split; intros H.
- inv H. reflexivity. inv X.
- subst. econstructor.
Qed.

Lemma FSubset_app_l {T} (x y : list T)
 : (x ⊆ (x ++ y))%list.
Proof.
unfold FSubset. intros. apply member_app.
left. assumption.
Qed.

Lemma FSubset_app_r {T} (x y : list T) 
  : (y ⊆ (x ++ y))%list.
Proof.
unfold FSubset. intros. apply member_app.
right. assumption.
Qed.

Lemma Each_app {T} {B : T -> Type} (xs ys : list T)
  : Each B xs * Each B ys <--> Each B (xs ++ ys).
Proof.
split; intros H.
- destruct H. intros x mem. apply member_app in mem.
  destruct mem.
  + apply e. assumption.
  + apply e0. assumption.
- split; intros x mem; apply H; apply member_app.
  + left. assumption.
  + right. assumption.
Qed.