Require Import Coq.Lists.List.
Import ListNotations.

Inductive member {A} : A -> list A -> Type :=
| here : forall {x xs}, member x (x :: xs)
| there : forall {x y ys}, member x ys -> member x (y :: ys).

Lemma member_map {A B} (f : A -> B) {x : A} {xs : list A}
      (elem : member x xs)
  : member (f x) (List.map f xs).
Proof.
  induction elem; simpl. constructor. constructor. assumption.
Defined.

Polymorphic Inductive Each {A} {B : A -> Type} : list A -> Type :=
  | Each_nil : Each nil
  | Each_cons : forall {x : A} {xs : list A}, B x -> Each xs -> Each (x :: xs).

Arguments Each {A} B xs.

Ltac inv H := inversion H; clear H; subst.

Definition swap_member {X : Type} {A B C : X} {Γ : list X}
           (x : member C (A :: B :: Γ))
  : member C (B :: A :: Γ).
Proof.
  inv x. apply there. apply here.
  inv X0. apply here. apply there. apply there.
  assumption.
Defined.

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