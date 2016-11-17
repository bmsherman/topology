Require Import 
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop.

Set Universe Polymorphism.
Module NatInfty.
(* The Alexandroff compactification of the natural numbers. *)

Inductive O : Set := 
  | MoreThan : nat -> O
  | Exactly : nat -> O.

Inductive le : O -> O -> Set :=
  | MoreThan_le : forall n m, m <= n -> le (MoreThan n) (MoreThan m)
  | Eventually_le : forall n m, n < m -> le (Exactly m) (MoreThan n)
  | Exactly_le : forall n m, m = n -> le (Exactly m) (Exactly n).

Ltac inv H := inversion H; clear H; subst.

Local Instance le_PreO : PreO.t le.
Proof.
constructor; intros.
- destruct x; constructor. reflexivity. reflexivity.
- destruct H. inv H0. constructor.
  eapply PeanoNat.Nat.le_trans; eassumption.
  inv H0. constructor. 
  eapply PeanoNat.Nat.le_lt_trans; eassumption.
  subst. assumption.
Qed.

Inductive Next {n : nat} : O -> Set :=
  | Next_Later : Next (MoreThan (S n))
  | Next_Now : Next (Exactly (S n)).

Arguments Next : clear implicits.

(** This axiom set is not localized. However,
    doing the localization procedure will
    generate the right thing! *)
Definition IxUL (a : O) : Set := match a with
  | MoreThan _ => unit
  | Exactly _ => Empty_set
  end. 

Definition CUL (a : O) : IxUL a -> Subset O := match a with
  | MoreThan n => fun _ => Next n
  | Exactly _ => Empty_set_rect _
  end.

Definition NatInfPO : FormTop.PreOrder :=
  {| PO_car := O
   ; FormTop.le := le
  |}.

Definition NatInfUL : PreISpace.t :=
  {| PreISpace.S := NatInfPO
   ; PreISpace.C := CUL
  |}.

Definition NatInfPS := Localized NatInfUL.

Definition exactly (n : nat) : Subset O := le (Exactly n).

Arguments exactly : clear implicits.

Inductive infty : Subset O :=
  | in_infty : forall n, infty (MoreThan n).

Require Import FormTopC.Cont.

Definition is_pt := IGCont.pt NatInfPS.

Lemma pt_infty : is_pt infty.
Proof.
constructor; intros.
- exists (MoreThan 0). constructor.
- destruct H, H0. exists (MoreThan (max n n0)). 
  econstructor. constructor; constructor.
  apply Max.le_max_l. apply Max.le_max_r.
  constructor.
- destruct H. inv H0. constructor.
- destruct i. simpl. destruct H.
  inv l. 
  destruct (Compare_dec.le_lt_eq_dec _ _ H0).
  + exists (MoreThan n). split. constructor.
    exists (MoreThan (S m)). split.  constructor.
    split. reflexivity. constructor. assumption.
  + subst. exists (MoreThan (S n)). split.  constructor.
    exists (MoreThan (S n)). split. constructor.
    split; constructor. apply Le.le_n_Sn. reflexivity.
Qed.

Lemma pt_exactly n : is_pt (exactly n).
Proof.
constructor; unfold exactly; intros.
- exists (Exactly n). unfold In. reflexivity.
- exists (Exactly n). split. split; assumption.
  reflexivity.
- etransitivity; eassumption.
- destruct i. destruct c. simpl in *; 
    try contradiction.
  exists (Exactly n). constructor. reflexivity.
  destruct (Compare_dec.lt_eq_lt_dec (S n0) n) as [[LT | EQ] | GT].
  + exists (MoreThan (S n0)). split. constructor.
      split. assumption. constructor; assumption.
  + subst. exists (Exactly (S n0)).  split. constructor.
      split. assumption. reflexivity.
  + exfalso. eapply Lt.le_not_lt. 2: eassumption. 
    inv H; inv l.
    * transitivity (S n1). apply Le.le_n_S. assumption. 
      assumption.
    * assumption.
  + simpl in *. contradiction.
Qed.

Lemma Pos : FormTop.gtPos NatInfPS.
Proof.
apply FormTop.gall_Pos.
intros a. destruct a.
- (** MoreThan n - take the point infty as an example. *)
  intros i.
  rewrite <- (Intersection_Included_r _ infty (PreISpace.C NatInfPS (MoreThan n) i)).
  apply (IGCont.pt_cov pt_infty).
  constructor.
- (** Exactly n - take the point (exactly n) as an example. *)
  intros i.
  rewrite <- (Intersection_Included_r _ (exactly n) (PreISpace.C NatInfPS (Exactly n) i)).
  apply (IGCont.pt_cov (pt_exactly n)).
  constructor. reflexivity.
Qed.

Require Import FormTopC.Discrete
  FormTopC.Bundled.

(** The (open) embedding of the natural numbers into
    its Alexandroff compactification. *)
Definition inj : Cont.map (discrete nat) NatInfPS := fun o n =>
  exactly n o.

(*
Lemma inj_cont : Cont.t Logic.eq le (Discrete.Cov nat) (FormTop.GCov le C) inj.
Proof.
apply DiscreteFunc.pointwise_cont.
intros. unfold Cov. apply IGCont.pt_cont. apply pt_exactly.
Qed.
*)

(** A little function that checks if a property holds for
    some natural number. *)
Section Checker.

Variable (f : nat -> bool).

Definition checkf : Subset O := fun o => match o with
  | MoreThan n => forall k, k <= n -> f k = false
  | Exactly n => (forall k, k < n -> f k = false) /\ f n = true
  end.

(* Super duper ugly! *)
Lemma checkf_cont : is_pt checkf.
Proof.
unfold is_pt. constructor.
- destruct (f 0) eqn: f0.
  + exists (Exactly 0). unfold In, checkf. split.
    intros. exfalso. eapply PeanoNat.Nat.nlt_0_r.
    eassumption. assumption.
  + exists (MoreThan 0). unfold In, checkf.
    intros. apply Le.le_n_0_eq in H. subst.
    assumption.
- intros b c X X0. destruct b. destruct c.
  exists (MoreThan (max n n0)). constructor.
  constructor; constructor. apply Max.le_max_l. apply Max.le_max_r.
  unfold checkf in *.
  apply Max.max_case_strong.
  intros. apply X. assumption. intros.
  apply X0. assumption.
  + destruct (Compare_dec.le_lt_dec n0 n).
    exfalso. unfold checkf in *. destruct X0.
    specialize (X n0 l). congruence.
    exists (Exactly n0). constructor.
    constructor; constructor. assumption. reflexivity.
    assumption.
  + destruct c. destruct (Compare_dec.le_lt_dec n n0).
    exfalso. unfold checkf in *. destruct X.
    specialize (X0 n l). congruence.
    exists (Exactly n). split. constructor; constructor.
    reflexivity. assumption. assumption. unfold checkf in X, X0.
    destruct (Compare_dec.lt_eq_lt_dec n n0). destruct s. 
    exfalso. destruct X, X0. specialize (H1 n l). congruence.
    subst. 
    exists (Exactly n0). split. 
    constructor; constructor; reflexivity.
    assumption. exfalso. destruct X, X0.
    specialize (H _ l). congruence.
- intros a b X H. induction H; unfold checkf in *.
  + intros. apply X. eapply Le.le_trans; eassumption.
  + intros. destruct X. apply H0.
    eapply Lt.le_lt_trans; eassumption.
  + subst. assumption.
- intros. induction i.
  + destruct c. simpl in *. destruct ix.
    inv l. destruct (Compare_dec.le_lt_eq_dec _ _ H2).
    exists (MoreThan n0). split. assumption.
    exists (MoreThan (Datatypes.S n)). split. constructor.
    split; constructor. reflexivity. assumption.
    subst. clear H2.
    destruct (f (Datatypes.S n0)) eqn:fSn.
    exists (Exactly (Datatypes.S n0)). split.  unfold checkf. split. 
    intros. apply H. apply Lt.lt_n_Sm_le; assumption.
    assumption. exists (Exactly (Datatypes.S n0)). split. constructor.
    split; constructor. constructor. reflexivity.
    exists (MoreThan (Datatypes.S n0)). split. unfold checkf. intros.
    inv H0. assumption. apply H. assumption.
    exists (MoreThan (Datatypes.S n0)). split. constructor.
    split; constructor. constructor. reflexivity.
    reflexivity. exists (Exactly m). split.  assumption.
    destruct (Compare_dec.le_lt_eq_dec _ _ H2).
    exists (MoreThan (Datatypes.S n)). split. constructor.
    split; constructor. reflexivity. assumption.
    subst. exists (Exactly (Datatypes.S n)). split.  constructor.
    split; constructor; reflexivity.
    induction ix.
Qed.

End Checker.


CoInductive Partial {A} : Type :=
  | Later : Partial -> Partial
  | Now   :  A -> Partial.

Arguments Partial : clear implicits.


Definition pt_to_Partial (x : Subset O) (ptx : is_pt x) : Partial unit.
Proof.
destruct (IGCont.pt_here ptx).
induction a.
Focus 2. apply Now. apply tt.
generalize dependent n. cofix.
intros.
pose proof (IGCont.pt_cov ptx i 
  (FormTop.MkIxL NatInfUL (MoreThan n) tt  (PreO.le_refl (MoreThan n)))) as X.
simpl in X. destruct X. destruct i0. destruct s.
destruct p. destruct d. induction n0.
- induction a.
  + apply Later. apply (pt_to_Partial _ x0).
  + apply (Now tt).
- apply Now. apply tt.
Defined.

End NatInfty.

Require Import
  Spec.Category
  FormTopC.Bundled
  FormTopC.Cont
  FormTopC.InfoBase
  FormTopC.All.
Import Category.

Lemma NIPO : PreO.t (le NatInfty.NatInfUL).
Proof.
apply NatInfty.le_PreO.
Qed.

Definition NatInfty : IGT :=
  {| S := NatInfty.NatInfPS
   ; Bundled.PO := NatInfty.le_PreO
   ; pos := NatInfty.Pos
   ; localized := @FormTop.Llocalized _ NIPO
  |}.

Local Open Scope loc.

Definition NatInfty_exactly (n : nat) : unit ~~> NatInfty
  := point NatInfty (NatInfty.exactly n)
  (IGCont.pt_cont _ (NatInfty.pt_exactly n)).

Definition NatInfty_infty : unit ~~> NatInfty :=
  point NatInfty (NatInfty.infty) (IGCont.pt_cont _
    (NatInfty.pt_infty)).

Definition NatInfty_checker (f : nat -> bool) : unit ~~> NatInfty
  := point NatInfty (NatInfty.checkf f)
    (IGCont.pt_cont _ (NatInfty.checkf_cont f)).

Definition run_NatInfty (x : unit ~~> NatInfty) :
  NatInfty.Partial Datatypes.unit.
Proof.
eapply NatInfty.pt_to_Partial.
unfold NatInfty.is_pt.
eapply IGCont.pt_cont_converse.

pose proof (mp_ok NatInfty_infty).
Abort.


Definition test_computation : NatInfty.Partial Datatypes.unit
  := NatInfty.pt_to_Partial _ (NatInfty.checkf_cont (fun x => false)).

(*
Extraction Language Haskell.
Extraction "test.hs" test_computation.
*)