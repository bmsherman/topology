Require Import 
  Coq.Arith.Compare_dec

  Prob.StdLib
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  FormTopC.FormTop
  FormTopC.Cont
  FormTopC.Discrete.

Set Universe Polymorphism.
(* The Alexandroff compactification of the natural numbers. *)

Inductive O : Set := 
  | MoreThan : nat -> O
  | Exactly : nat -> O.

Inductive le : O -> O -> Set :=
  | MoreThan_le : forall n m, m <= n -> le (MoreThan n) (MoreThan m)
  | Eventually_le : forall n m, n < m -> le (Exactly m) (MoreThan n)
  | Exactly_le : forall n m, m = n -> le (Exactly m) (Exactly n).

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
Inductive Ix : O -> Set := 
  | IxNext : forall n, Ix (MoreThan n).

Definition C (a : O) (ix : Ix a) : Subset O := match ix with
  | IxNext n => Next n
  end.

Definition NatInfPO : PreOrder :=
  {| PO_car := O
   ; PreOrder.le := le
  |}.

Definition NatInf : PreISpace.t :=
  {| PreISpace.S := NatInfPO
   ; PreISpace.C := C
  |}.

Definition exactly (n : nat) : Subset O := le (Exactly n).

Arguments exactly : clear implicits.

Inductive infty : Subset O :=
  | in_infty : forall n, infty (MoreThan n).

Definition is_pt := IGCont.pt NatInf.

Lemma pt_infty : is_pt infty.
Proof.
constructor; intros.
- exists (MoreThan 0). constructor.
- destruct H, H0. exists (MoreThan (max n n0)). 
  econstructor. split; le_down; constructor.
  apply Max.le_max_l. apply Max.le_max_r.
  constructor.
- destruct H. inv H0. constructor.
- destruct j as [m]. simpl.
  simpl in H. destruct H0 as [n].
  inv H.
  destruct (Compare_dec.le_lt_eq_dec _ _ H2).
  + exists (MoreThan n). split. constructor.
    split. le_down. simpl. econstructor. reflexivity.
    exists (MoreThan (S m)).  constructor.
    constructor. assumption.
  + subst. exists (MoreThan (S n)). split.  constructor.
    split. le_down. simpl. constructor. apply Le.le_n_Sn.
    exists (MoreThan (S n)). constructor.
    simpl. constructor. reflexivity.
Qed.

Lemma pt_exactly n : is_pt (exactly n).
Proof.
constructor; unfold exactly; intros.
- exists (Exactly n). unfold In. reflexivity.
- exists (Exactly n). split. split; le_down; assumption.
  reflexivity.
- etransitivity; eassumption.
- destruct j as [m]. simpl.
  inv H0.
  + inv H. 
  exists (Exactly n). constructor. reflexivity.
  destruct (Compare_dec.lt_eq_lt_dec (S m) n) as [[LT | EQ] | GT].
    * split. le_down. simpl. constructor. assumption. 
      exists (MoreThan (S m)). constructor. simpl. constructor.
      assumption.
    * subst. split. le_down. simpl. constructor.
      assumption. exists (Exactly (S m)). constructor.
      reflexivity.
    * exfalso. eapply Lt.le_not_lt. 2: eassumption.
      etransitivity. 2: eapply H2. apply Le.le_n_S. assumption. 
  + inv H. exists (Exactly n0).
    split. constructor. reflexivity.
    split. le_down. reflexivity.
    exists (MoreThan (S m)). constructor.
    simpl. constructor. admit.
Admitted.

Lemma Pos : FormTop.gtPos NatInf.
Proof.
apply FormTop.gall_Pos.
intros b i a. induction a.
- (** MoreThan n - take the point infty as an example. *)
  intros H.
  pose proof (IGCont.pt_cov pt_infty (MoreThan n) b i H).
  assert (H1 : infty (MoreThan n)) by constructor.
  specialize (H0 H1).
  destruct H0. destruct i0. eexists; eassumption.
- (** Exactly n - take the point (exactly n) as an example. *)
  intros H.
  pose proof (IGCont.pt_cov (pt_exactly n) (Exactly n) b i H).
  assert (H1 : exactly n (Exactly n)). 
  unfold exactly. reflexivity.
  specialize (H0 H1). destruct H0. destruct i0.
  eexists; eassumption.
Qed.

(** The (open) embedding of the natural numbers into
    its Alexandroff compactification. *)

Require Import FormTopC.FormalSpace.

Definition inj : Cont.map (discrete nat) (toPSL NatInf) := fun o n =>
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
pose proof (IGCont.pt_cov ptx 
  (MoreThan n) (MoreThan n) (IxNext n) 
  (PreO.le_refl (MoreThan n)) i) as X.
simpl in X. destruct X. destruct i0. destruct d. 
le_downH d. destruct d0. destruct i0.
- induction a.
  + apply Later. apply (pt_to_Partial _ x0).
  + apply (Now tt).
- apply Now. apply tt.
Defined.