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

Hypothesis tPos : FormTop.tPos Closed.

Definition ClosedSub : FormalSpace.t :=
  {| S := Closed
  ; isFT := t |}.

Definition closed_incl : Cont.map ClosedSub A :=
  incl CovC t tPos.

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

Existing Instances pos.

Theorem tOpen : FormTop.t OpenPS.
Proof.
constructor; simpl; unfold CovO; intros.
- destruct X0. destruct d, d0. unfold In in i.
   subst. rewrite l. apply FormalSpace.refl. assumption.
- destruct X1. destruct d, d0. unfold In in i. subst. 
  apply positive. intros. 
  apply (FormalSpace.trans (U := ⇓ (⇓ U ∩ ⇓ eq a0) ∩ ⇓ V)). 
  Focus 2. intros. destruct X2.
  destruct d, d0. destruct i.  destruct d, d0.
  unfold In in *. subst.
  eapply X0. eassumption.
  split. exists a5. reflexivity. rewrite <- l3. assumption.
  exists a4; assumption. 
  apply FormalSpace.le_right. apply FormalSpace.le_right.
  apply X. split. exists a1. reflexivity. assumption.
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


Hypothesis tPosO : FormTop.tPos OpenPS.

Definition OpenSub : FormalSpace.t :=
  {| S := OpenPS
  ; isFT := tOpen |}.

Definition open_incl : Cont.map OpenSub A :=
  incl CovO tOpen tPosO.

Lemma open_incl_cont : Cont.t OpenSub A open_incl.
Proof.
apply incl_cont. intros. simpl. 
unfold RelIncl, Included, pointwise_rel, arrow, CovO.
intros. destruct X0.  destruct d. unfold In in *.
subst. rewrite l. assumption.
Qed.


End Defn.


(** Closed subspaces are inductively generated. *)
Section IGDefn.

Context {A : IGt}.

Variable V : Open A. 

Inductive SIx {a : S A} : Type :=
  | Orig : PreISpace.Ix A a -> SIx
  | InV : V a -> SIx.

Arguments SIx : clear implicits.

Definition SC (a : S A) (i : SIx a) : Open A := 
  match i with
  | Orig i' => PreISpace.C A a i'
  | InV _ => fun _ => False
  end.

Definition LocalizedPS (X : PreISpace.t) : PreSpace.t :=
  {| PreSpace.S := PreISpace.S X
   ; PreSpace.Cov := FormTop.GCovL X
  |}.

Definition A' : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.C := SC
  |}.

Theorem same : PreSpace.Cov (LocalizedPS A') ==== PreSpace.Cov (Closed (A := fromIGt A) V).
Proof.
apply RelSame_iffT. intros a U. simpl. unfold CovC. split; intros H.
- induction H.
  + apply FormTop.refl. right. assumption.
  + apply FormTop.le_left with b. assumption.
    assumption.
  + destruct i.
    * apply (FormTop.gle_infinity (A := A) a (V ∪ U) b i l).
      apply X.
    * rewrite l. apply FormTop.refl. left. assumption. 
- simpl in H. simpl in U. 
  remember ((V : Open (PreISpace.S A)) ∪ (U : Open (PreISpace.S A))) as U' in H. 
  induction H; subst.
  + destruct u.
    * eapply FormTop.gmonotoneL. Focus 2.
    pose proof (PreO.le_refl a) as aa.
    pose proof (FormTop.gle_infinity (A := A') a (fun _ => False) a (InV v)
       aa) as H0.
    apply H0. intros u H1. simpl in *.
    destruct H1. destruct d0. destruct i. firstorder.
    * apply FormTop.glrefl. assumption.
  + simpl in *. apply (FormTop.glle_left (A := A')) with b. assumption. apply IHGCovL.
    reflexivity.
  + apply (FormTop.gle_infinity (A := A') a _ b (Orig i)).
    assumption. intros. apply X. assumption. reflexivity. 
Qed.

End IGDefn.