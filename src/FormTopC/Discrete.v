Require Import FormTopC.FormTop 
  FormTopC.Cont
  FormTopC.InfoBase
  Algebra.SetsC Algebra.FrameC
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

Ltac inv H := inversion H; clear H; subst.

Section Func.

Context {A : Type}.

Context {T : Type} {leT : crelation T}
  {POT : PreO.t leT}
  {CovT : T -> (Subset T) -> Type}
  {FTT : FormTop.t leT CovT}.

Variable (f : A -> Subset T).

Definition pointwise : Cont.map A T :=
  fun (y : T) (x : A) => In (f x) y.

Hypothesis fpt : forall a, Cont.pt leT CovT (f a).

Theorem pointwise_cont : Cont.t Logic.eq leT (Cov A) CovT pointwise.
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


Theorem fCont (f : A -> B) :
  Cont.t Logic.eq Logic.eq (Cov A) (Cov B) (discrF f).
Proof.
apply pointwise_cont. intros. apply pt_ok.
Qed.

(** Should be able to get this from the above just from
  rewriting, but it's not working... *)
Theorem fContI (f : A -> B) :
  Cont.t Logic.eq Logic.eq (CovG A) 
  (CovG B) (discrF f).
Proof.
constructor; unfold Cov; intros.
- apply FormTop.grefl. exists (f a); constructor.
- subst. assumption.
- inv H. inv H0. apply FormTop.grefl. exists (f a). split; reflexivity.
  reflexivity.
- apply FormTop.grefl. exists b; unfold In; auto. induction X; auto.
  subst. apply IHX. assumption. induction i. subst.
  apply X. constructor. assumption. 
Qed.

(** Same story here... *)
Definition pt_okI (x : A) : Cont.pt eq (CovG A) (eq x).
Proof.
constructor.
- econstructor. reflexivity.
- intros. subst.
  repeat (econstructor || eauto).
- intros. subst. econstructor.
  econstructor. reflexivity. induction X. 
  + assumption.
  + subst. assumption.
  + destruct i. subst. apply X. constructor.
Qed.

(** Show that (discrete A * discrete B ≅ discrete (A * B) *)

Require Import FormTopC.Product.

Theorem prod_assoc_cont :
  Cont.t (prod_op Logic.eq Logic.eq) Logic.eq
         (Product.Cov A B (leS := Logic.eq) (leT := Logic.eq) 
         (Ix A) (Ix B) (C A) (C B)) (CovG (A * B)) Logic.eq.
Proof.
constructor; intros.
- apply FormTop.grefl. econstructor. constructor. reflexivity.
- destruct X. destruct a, b, c. simpl in *. subst. assumption.
- subst. apply FormTop.grefl. constructor 1 with a.
  split; reflexivity. reflexivity.
- subst. unfold Cov in X. apply FormTop.grefl.
  econstructor. apply CovG_Cov. eassumption. reflexivity.
Qed.

Theorem prod_deassoc_cont : 
  Cont.t Logic.eq (prod_op Logic.eq Logic.eq) (CovG (A * B))
         (Product.Cov A B (leS := Logic.eq) (leT := Logic.eq) 
         (Ix A) (Ix B) (C A) (C B)) Logic.eq.
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

Definition discrete_f_mp {A B} (f : A -> B)
  : Contmap (discrete A) (discrete B) :=
  Discrete.discrF f.

Definition discrete_f_mp_ok {A B} (f : A -> B)
  : Contprf (discrete A) (discrete B) (discrete_f_mp f) := Discrete.fContI f.

Definition discrete_f {A B} (f : A -> B) : discrete A ~~> discrete B :=
  {| mp := discrete_f_mp f 
   ; mp_ok := discrete_f_mp_ok f |}.

Definition discrete_prod_assoc_mp {A B}
  : Contmap (discrete A * discrete B) (discrete (A * B)) := Logic.eq.

Lemma discrete_prod_assoc_mp_ok {A B}
  : Contprf (discrete A * discrete B) (discrete (A * B)) 
  discrete_prod_assoc_mp. 
Proof. apply Discrete.prod_assoc_cont.
Qed.

Definition discrete_prod_assoc {A B : Type} : 
  discrete A * discrete B ~~> discrete (A * B) :=
  {| mp := discrete_prod_assoc_mp
   ; mp_ok := discrete_prod_assoc_mp_ok
  |}.

(** Could have used Sierpinski? *)
Class Discrete {A : IGT} : Type :=
  { bequal : A * A ~~> discrete bool }.