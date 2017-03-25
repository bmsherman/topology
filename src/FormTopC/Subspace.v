 Require Import
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  FormTopC.FormTop
  FormTopC.Cont
  FormTopC.Locale
  FormTopC.FormalSpace
  CRelationClasses.

Local Open Scope Subset.
Local Open Scope FT.
Set Universe Polymorphism.

Existing Instances FormalSpace.FT FormalSpace.PreO
  FormalSpace.Cov_Proper FormalSpace.Cov_Proper2
  FormalSpace.Cov_Proper3.

(** General properties of subspaces and their inclusions. *)

Section GenSub.
Context {A : FormalSpace.t}.

Variable Cov' : A -> Open A -> Type.

Definition Subspace : PreSpace.t :=
  {| PreSpace.S := PreSpace.S A
   ; PreSpace.Cov := Cov'
  |}.

Hypothesis tSubspace : FormTop.t Subspace.
Hypothesis tPosSub : tPos Subspace.

Definition SubspaceSub : FormalSpace.t :=
  {| S := Subspace
  ; isFT := tSubspace |}.

Definition incl : Cont.map Subspace A :=
  fun a => Sat SubspaceSub (eq a).

Hypothesis CovImpl : PreSpace.Cov A ⊑ PreSpace.Cov SubspaceSub.

Lemma incl_refl : forall a, incl a a.
Proof.
intros. unfold incl, Sat. apply FormTop.refl.
reflexivity.
Qed.

Lemma incl_cont : Cont.t Subspace A incl.
Proof.
econstructor; intros.
- apply FormTop.refl. exists a. unfold In. auto.
  apply incl_refl.
- unfold incl, Sat in *. rewrite X.  assumption.
- unfold incl, Sat in X, X0.
  FormTop.ejoin. FormTop.etrans. apply FormTop.refl.
  exists a. assumption. apply incl_refl.
- unfold incl, Sat in X. FormTop.etrans.
  unfold In in X. subst. apply CovImpl in X0.
  FormTop.etrans. apply FormTop.refl.
  exists a. assumption. apply incl_refl.
Qed.

End GenSub.

(** Closed subspaces *)
Section Defn.
Context {A : FormalSpace.t}.
Variable (V : Open A).

Definition CovC a U := a <|[A] V ∪ U.


Definition Closed : PreSpace.t :=
  {| PreSpace.S := PreSpace.S A
   ; PreSpace.Cov := CovC
  |}.

Theorem t : FormTop.t Closed.
Proof.
constructor; unfold CovC; intros.
- apply FormalSpace.refl. right. assumption.
- FormalSpace.etrans.
  destruct X. 
  + apply FormalSpace.refl. left. assumption.
  + apply X0. assumption.
- apply FormalSpace.le_left with b; assumption.
- FormalSpace.ejoin. simpl in *.  unfold CovC. 
  FormalSpace.etrans.
  destruct X1. destruct d, d0.
  destruct i.
  + rewrite l. apply FormalSpace.refl. left. assumption.
  + destruct i0. rewrite l0. apply FormalSpace.refl.
    left. assumption.
    rewrite <- Union_Included_r.
    apply FormTop.le_right.
    * rewrite l. apply FormalSpace.refl. assumption.
    * rewrite l0. apply FormalSpace.refl. assumption.
Qed.

Definition ClosedSub : FormalSpace.t :=
  {| S := Closed
  ; isFT := t |}.

Definition closed_incl : Cont.map ClosedSub A :=
  incl CovC t.

Lemma closed_incl_cont : Cont.t ClosedSub A closed_incl.
Proof.
apply incl_cont. intros. simpl. 
unfold RelIncl, Included, pointwise_rel, arrow, CovC.
intros. 
FormTop.etrans. apply FormTop.refl. right. assumption.
Qed.

(** Open subspaces. *)

Definition CovO a U := eq a ↓ V <<|[A] U.

Definition OpenPS : PreSpace.t :=
  {| PreSpace.S := PreSpace.S A
   ; PreSpace.Cov := CovO
  |}.

Theorem tOpen : FormTop.t OpenPS.
Proof.
constructor; simpl; unfold CovO; intros.
- destruct X0. destruct d, d0. unfold In in i.
   subst. rewrite l. apply FormalSpace.refl. assumption.
- destruct X1. destruct d, d0. unfold In in i. subst.
  apply (FormalSpace.trans (U := (U ↓ eq a0) ↓ V)). 
  Focus 2. intros a X2. destruct X2.
  destruct d, d0. destruct i.  le_downH d0. destruct d.
  eapply X0. eassumption.
  split. exists a5. reflexivity. rewrite <- l3. assumption.
  exists a4; assumption. 
  apply FormalSpace.le_right. apply FormalSpace.le_right.
  apply X. split. le_down. assumption.
  exists a2; assumption. apply FormalSpace.refl. reflexivity.
  rewrite l0. apply FormalSpace.refl. assumption.
- destruct X1. destruct d, d0. unfold In in i.
   subst. eapply FormalSpace.trans. 
  2: eapply X0. eapply FormalSpace.le_right. 
  rewrite l, X. apply FormalSpace.refl. reflexivity. 
  rewrite l0. apply FormalSpace.refl. assumption.
- destruct X1. destruct d, d0. 
  unfold In in i. subst.
  apply FormalSpace.le_right. eapply FormalSpace.trans.
  2: eapply X. apply FormalSpace.le_right.
  rewrite l.  apply FormalSpace.refl. reflexivity.
  rewrite l0. apply FormalSpace.refl. assumption.
  eapply FormalSpace.trans. 2: eapply X0.
  apply FormalSpace.le_right. rewrite l. apply FormalSpace.refl.
  reflexivity. rewrite l0. apply FormalSpace.refl.
  assumption.
Qed.

Definition OpenSub : FormalSpace.t :=
  {| S := OpenPS
  ; isFT := tOpen |}.

Definition open_incl : Cont.map OpenSub A :=
  incl CovO tOpen.

Lemma open_incl_cont : Cont.t OpenSub A open_incl.
Proof.
apply incl_cont. intros. simpl. 
unfold RelIncl, Included, pointwise_rel, arrow, CovO.
intros. destruct X0.  destruct d. unfold In in *.
subst. rewrite l. assumption.
Qed.


End Defn.