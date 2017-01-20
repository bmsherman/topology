Require Import FormTopC.FormTop 
  FormTopC.Cont
  FormTopC.InfoBase
  Algebra.SetsC
  Algebra.OrderC
  Coq.Classes.CMorphisms
  Prob.StdLib.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Local Open Scope FT.

Module Discrete.
Section Discrete.

Universes A P.
Variable A : Type@{A}.

Definition DiscretePO@{} : FormTop.PreOrder@{A P} :=
  {| PO_car := A
   ; le := Logic.eq
  |}.

Require Import FormTopC.Bundled.

Instance discretePO@{} : PreO.t Logic.eq := PreO.discrete@{A P} A.

Set Printing Universes.
Axiom undefined : forall A, A.
Definition DiscI@{X} : IGT@{A P P} := InfoBase@{A P P X} DiscretePO.

Definition Disc : PreSpace.t :=
  {| PreSpace.S := DiscretePO
   ; PreSpace.Cov := fun a U => In U a |}.

Lemma CovG_Cov : forall a U, a <|[DiscI] U -> In U a.
Proof.
intros. induction X. 
- simpl in *. subst. assumption.
- simpl in *. subst. assumption.
- induction i.
Qed.

Instance isCov : FormTop.t Disc.
Proof.
econstructor; try (simpl; eauto).
- intros. subst. eauto.
- intros. split; unfold downset; exists a;
  (assumption || reflexivity).
Qed.

Definition pt_ok (x : A) : Cont.pt Disc (eq x).
Proof.
constructor.
- econstructor. reflexivity.
- intros. subst.
  repeat (econstructor || eauto).
- intros. subst. econstructor.
  econstructor. reflexivity. assumption.
Qed.

Lemma pt_singleton (U : Subset A) :
  Cont.pt Disc U -> forall x y : A, U x -> U y -> x = y.
Proof.
intros H x y Ux Uy.
pose proof (Cont.pt_local H Ux Uy).
destruct X. destruct i.
destruct d. simpl in *. subst. assumption.
Qed.

Definition pt_eval (U : Subset A) (x : Cont.pt Disc U)
  := match Cont.pt_here x with
   | Inhabited_intro y _ => y
  end.

End Discrete.
End Discrete.

Require Import
  Spec.Category
  FormTopC.Bundled
  FormTopC.Cont
  FormTopC.Product.
Import Category.

Local Open Scope loc.

Axiom undefined : forall A, A.


Set Printing Universes.

Definition discrete (A : Type) : IGT :=
  {| S := Discrete.DiscI A
  ; PO := PreO.discrete A
  ; pos := InfoBase.Pos (Discrete.DiscretePO A)
  |}.

Module DiscreteFunc.
Ltac inv H := inversion H; clear H; subst.

Section Func.

Context {A : Type}.
Variable B : IGT.

Variable (f : A -> Subset (S B)).

Definition pointwise : Cont.map (discrete A) B :=
  fun (y : S B) (x : A) => In (f x) y.

Hypothesis fpt : forall a, Cont.pt B (f a).

Theorem pointwise_cont : Cont.t (Discrete.Disc A) B pointwise.
Proof.
constructor; simpl; intros.
- destruct (Cont.pt_here (fpt a)).
  exists a0. constructor. assumption.
- unfold pointwise in *. subst. assumption.
- unfold pointwise in *.
  pose proof (Cont.pt_local (fpt a) X X0).
  destruct X1. destruct i. exists a0; assumption.
- unfold pointwise in X.
  pose proof (Cont.pt_cov (fpt a) X X0).
  destruct X1. destruct i. exists a0; assumption.
Qed.

End Func.

Section DFunc.

Context {A B : Type}.
Definition discrF (f : A -> B) (y : B) (x : A) : Prop := f x = y.

Instance POB : PO.t Logic.eq Logic.eq := PO.discrete B.

(*
Theorem fCont (f : A -> B) :
  Cont.t Logic.eq (le (discrete B)) (Discrete.Cov A) (Discrete.Cov B) (discrF f).
Proof.
apply pointwise_cont. intros. apply Discrete.pt_ok.
Qed.
*)

(** Should be able to get this from the above just from
  rewriting, but it's not working... *)
Theorem fContI (f : A -> B) :
  Cont.t (discrete A) (discrete B) (discrF f).
Proof.
constructor; unfold Cov; intros.
- apply FormTop.grefl. exists (f a); constructor.
- simpl in X. subst. assumption.
- inv H. inv H0. apply FormTop.grefl. exists (f a). split; reflexivity.
  reflexivity.
- apply FormTop.grefl. exists b; unfold In; auto. induction X; auto.
  simpl in *. subst. apply IHX. assumption. induction i.
Qed.

(** Same story here... *)
Definition pt_okI (x : A) : Cont.pt (discrete A) (Logic.eq x).
Proof.
constructor.
- econstructor. reflexivity.
- intros. subst.
  repeat (econstructor || eauto).
- intros. subst. econstructor.
  econstructor. reflexivity. induction X. 
  + assumption.
  + simpl in *. subst. assumption.
  + destruct i.
Qed.

(** Show that (discrete A * discrete B ≅ discrete (A * B) *)

Require Import FormTopC.Product.

Theorem prod_assoc_cont :
  Cont.t (discrete A * discrete B) (discrete (A * B)) Logic.eq.
Proof.
constructor; intros.
- apply FormTop.grefl. econstructor. constructor. reflexivity.
- destruct X. destruct a, b, c. simpl in *. subst. assumption.
- subst. apply FormTop.grefl. constructor 1 with a.
  split; reflexivity. reflexivity.
- subst. unfold Cov in X. apply FormTop.grefl.
  econstructor. apply Discrete.CovG_Cov. eassumption. reflexivity.
Qed.

Theorem prod_deassoc_cont : 
  Cont.t (discrete (A * B)) (discrete A * discrete B) Logic.eq.
Proof.
constructor; unfold Cov; intros.
- econstructor. econstructor. reflexivity. reflexivity.
- congruence.
- subst. destruct a. econstructor. econstructor. repeat (split || reflexivity).
  reflexivity.
- subst. apply FormTop.grefl. constructor 1 with a; try reflexivity.
  induction X. assumption. destruct a, b. destruct l.
  simpl in *. subst. assumption.
  destruct a.
  destruct i; subst; apply X; split;
  repeat match goal with
  | [ H : PreISpace.Ix _ _ |- _ ] => destruct H; subst
  | [  |- _ = _ ] => reflexivity
  | [ i : Product.Ix _ _ |- _] => destruct i
  end.
Qed.


End DFunc.

End DiscreteFunc.

Definition discrete_f {A B} (f : A -> B) : discrete A ~~> discrete B :=
  {| mp_ok := DiscreteFunc.fContI f |}.

Definition discrete_prod_assoc {A B : Type} : 
  discrete A * discrete B ~~> discrete (A * B) :=
  {| mp_ok := DiscreteFunc.prod_assoc_cont
  |}.

(** Could have used Sierpinski? *)
Class Discrete {A : IGT} : Type :=
  { bequal : A * A ~~> discrete bool }.