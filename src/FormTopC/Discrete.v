Require Import FormTopC.FormTop 
  FormTopC.Cont
  FormTopC.InfoBase
  Algebra.SetsC
  Algebra.OrderC
  Coq.Classes.CMorphisms
  Prob.StdLib.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Module Discrete.
Section Discrete.

Variable A : Type.

Definition Ix := @InfoBase.Ix _ (@Logic.eq A).
Definition C := @InfoBase.C _ (@Logic.eq A) (@Logic.eq A).
Definition CovI := @InfoBase.Cov _ (@Logic.eq A).
Definition CovG := @InfoBase.GCov A Logic.eq Logic.eq.

Definition Cov (a : A) (U : Subset A) : Type := U a.

Lemma CovG_Cov : forall a U, CovG a U -> In U a.
Proof.
intros. induction X. 
- assumption.
- subst. assumption.
- induction i. subst. apply X. reflexivity.
Qed.

Theorem CovEquiv : (eq ==> Same_set ==> iffT)%signature Cov CovI.
Proof.
simpl_crelation. unfold Cov, CovI, InfoBase.Cov.
split; intros.
- exists y. apply X. assumption. reflexivity.
- destruct X0 as [x t xt leat]. subst. apply X. assumption. 
Qed.

Instance FTproper : Proper _ FormTop.t := @FormTop.t_proper A.

Instance discretePO : PO.t Logic.eq Logic.eq := PO.discrete A.

Instance isCov : FormTop.t Logic.eq Cov.
Proof.
eapply FormTop.t_proper. 3: apply InfoBase.isCov.
reflexivity.  apply CovEquiv.
Qed.

Definition pt_ok (x : A) : Cont.pt eq Cov (eq x).
Proof.
constructor.
- econstructor. reflexivity.
- intros. subst.
  repeat (econstructor || eauto).
- intros. subst. econstructor.
  econstructor. reflexivity. assumption.
Qed.

Lemma pt_singleton (U : Subset A) :
  Cont.pt eq Cov U -> forall x y : A, U x -> U y -> x = y.
Proof.
intros H x y Ux Uy.
pose proof (Cont.pt_local H Ux Uy).
destruct X. destruct i.
destruct d. subst. assumption.
Qed.

Definition pt_eval (U : Subset A) (x : Cont.pt eq Cov U)
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

Definition discrete (A : Type) : IGT :=
  {| S := A 
  ; PO := PreO.discrete A
  ; localized := @InfoBase.loc _ _ _ (PO.discrete A)
  ; pos := InfoBase.Overt (PO := PO.discrete A)
  |}.

Module DiscreteFunc.
Ltac inv H := inversion H; clear H; subst.

Section Func.

Context {A : Type}.
Variable B : IGT.

Variable (f : A -> Subset (S B)).

Definition pointwise : Contmap (discrete A) B :=
  fun (y : S B) (x : A) => In (f x) y.

Hypothesis fpt : forall a, Cont.pt (le B) (Cov B) (f a).

Theorem pointwise_cont : Cont.t Logic.eq (le B) (Discrete.Cov A) (Cov B) pointwise.
Proof.
constructor; unfold Cov; intros.
- destruct (Cont.pt_here (fpt a)).
  exists a0. constructor. assumption.
- subst. assumption.
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
  Contprf (discrete A) (discrete B) (discrF f).
Proof.
constructor; unfold Cov; intros.
- apply FormTop.grefl. exists (f a); constructor.
- simpl in X. subst. assumption.
- inv H. inv H0. apply FormTop.grefl. exists (f a). split; reflexivity.
  reflexivity.
- apply FormTop.grefl. exists b; unfold In; auto. induction X; auto.
  simpl in *. subst. apply IHX. assumption. induction i. subst.
  apply X. constructor. assumption. 
Qed.

(** Same story here... *)
Definition pt_okI (x : A) : Contpt (discrete A) (Logic.eq x).
Proof.
constructor.
- econstructor. reflexivity.
- intros. subst.
  repeat (econstructor || eauto).
- intros. subst. econstructor.
  econstructor. reflexivity. induction X. 
  + assumption.
  + simpl in *. subst. assumption.
  + destruct i. subst. apply X. constructor.
Qed.

(** Show that (discrete A * discrete B ≅ discrete (A * B) *)

Require Import FormTopC.Product.

Theorem prod_assoc_cont :
  Contprf (discrete A * discrete B) (discrete (A * B)) Logic.eq.
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
  Contprf (discrete (A * B)) (discrete A * discrete B) Logic.eq.
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
  | [ H : Ix _ _ |- _ ] => destruct H; subst
  | [  |- _ = _ ] => reflexivity
  | [ |- C _ _ _ _ ] => constructor
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