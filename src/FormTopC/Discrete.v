Require Import FormTopC.FormTop 
  FormTopC.Cont
  FormTopC.InfoBase
  FormTopC.FormalSpace
  Algebra.SetsC
  Algebra.OrderC
  Coq.Classes.CMorphisms
  Prob.StdLib.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Set Printing Universes.

Local Open Scope FT.

Module Discrete.
Section Discrete.

Universes A A'.
Variable A : Type@{A}.

Definition DiscretePO@{} : FormTop.PreOrder@{A A} :=
  {| PO_car := A
   ; le := Logic.eq
  |}.

Instance discretePO@{} : PreO.t Logic.eq := PreO.discrete@{A A} A.

Set Printing Universes.

Definition DiscI@{} : IGt@{A A A A'} := InfoBase.InfoBase@{A A A'} DiscretePO.

Definition Disc@{} : PreSpace.t :=
  {| PreSpace.S := DiscretePO
   ; PreSpace.Cov := fun a U => In U a |}.

Local Open Scope Subset.

Lemma CovG_Cov a U : a <|[DiscI] U <--> In U a.
Proof.
split; intros H.
- induction H. 
  + simpl in *. subst. assumption.
  + simpl in *. subst. assumption.
  + induction i.
- apply FormTop.refl. assumption.
Qed.

Instance isCov@{} : FormTop.t Disc.
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
apply down_eq in d. destruct d. destruct l, l0.
reflexivity.
Qed.

Definition pt_eval (U : Subset A) (x : Cont.pt Disc U)
  := match Cont.pt_here x with
   | Inhabited_intro y _ => y
  end.

End Discrete.
End Discrete.

Require Import
  FormTopC.Cont
  FormTopC.Product.

Local Open Scope loc.

Definition discrete@{A A'} : Type@{A} -> IGt@{A A A A'} := Discrete.DiscI.

Module DiscreteFunc.
Ltac inv H := inversion H; clear H; subst.

Section Func.

Universes A A' B P I BPI.
Context {A : Type@{A}}.
Variable B : IGt@{A P I BPI}.

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
Universes A A' B B'.
Context {A : Type@{A}} {B : Type@{B}}.
Definition discrF (f : A -> B) (y : B) (x : A) : Prop := f x = y.

Instance POB@{} : PO.t Logic.eq Logic.eq := PO.discrete B.

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
  Cont.t (discrete@{A A'} A) (discrete@{B B'} B) (discrF f).
Proof.
constructor; intros.
- apply FormTop.refl. exists (f a); constructor.
- unfold discrF in *. simpl in X. subst. reflexivity.
- inv H. inv H0. apply FormTop.refl. 
  exists (f a). split; le_down; simpl; reflexivity.
  reflexivity.
- apply FormTop.refl. exists b; unfold In; auto. induction X; auto.
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

(** This is only true for finitary products! *)
(** Show that (discrete A * discrete B ≅ discrete (A * B) *)


End DFunc.

End DiscreteFunc.

(** For some reason, I get a universe inconsistency if I try to do
    this in normal definition mode. *)
Definition discrete_f {A B : Type} (f : A -> B) : discrete A ~~> discrete B.
Proof.
unshelve econstructor.
- exact (DiscreteFunc.discrF f).
- exact (DiscreteFunc.fContI f).
Defined.