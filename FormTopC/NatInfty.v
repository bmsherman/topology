Require Import Algebra.SetsC Algebra.FrameC
  FormTopC.FormTop.

(* The Alexandroff compactification of the natural numbers. *)
Module NatInfty.

Inductive O := 
  | MoreThan : nat -> O
  | Exactly : nat -> O.

Inductive le : O -> O -> Type :=
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

Inductive Next {n : nat} : O -> Type :=
  | Next_Later : Next (MoreThan (S n))
  | Next_Now : Next (Exactly (S n)).

Arguments Next : clear implicits.

(** This axiom set is not localized. However,
    doing the localization procedure will
    generate the right thing! *)
Definition IxUL (a : O) : Type := match a with
  | MoreThan _ => unit
  | Exactly _ => Empty_set
  end. 

Definition CUL (a : O) : IxUL a -> Subset O := match a with
  | MoreThan n => fun _ => Next n
  | Exactly _ => Empty_set_rect _
  end.

Definition Ix := FormTop.IxL le (Ix := IxUL).
Definition C := FormTop.CL le CUL.

Definition Cov := FormTop.GCovL le CUL.

Definition exactly (n : nat) : Subset O := le (Exactly n).

Arguments exactly : clear implicits.

Inductive infty : Subset O :=
  | in_infty : forall n, infty (MoreThan n).

Require Import FormTopC.Cont.

Definition is_pt := IGCont.pt le C.

Lemma pt_infty : is_pt infty.
Proof.
constructor; intros.
- exists (MoreThan 0). constructor.
- destruct H, H0. exists (MoreThan (max n n0)). 
  econstructor. constructor; constructor.
  apply Max.le_max_l. apply Max.le_max_r.
  constructor.
- destruct H. inv H0. constructor.
- destruct i. destruct x. simpl. destruct H.
  inv y. 
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
- destruct i. destruct x. destruct x; simpl in *; 
    try contradiction.
  exists (Exactly n). constructor. reflexivity.
  destruct (Compare_dec.lt_eq_lt_dec (S n0) n) as [[LT | EQ] | GT].
  + exists (MoreThan (S n0)). split. constructor.
      split. assumption. constructor; assumption.
  + subst. exists (Exactly (S n0)).  split. constructor.
      split. assumption. reflexivity.
  + exfalso. eapply Lt.le_not_lt. 2: eassumption. 
    inv H; inv y.
    * transitivity (S n1). apply Le.le_n_S. assumption. 
      assumption.
    * assumption.
Qed.

Require Import FormTopC.InfoBase.

(** The (open) injection of the natural numbers into
    its Alexandroff compactification. *)
Definition inj : Cont.map nat O := fun o n =>
  exactly n o.



End NatInfty.