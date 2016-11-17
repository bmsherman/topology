 Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.FormalSpace
  CRelationClasses.

Local Open Scope Subset.
Local Open Scope FT.
Set Universe Polymorphism.

Module Subspace.

(** Closed subspaces *)
Section Defn.
Context {A : FormalSpace.t}.
Variable (V : Open A).

Definition Cov' a U := a <|[A] V ∪ U.


Definition Closed : PreSpace.t :=
  {| PreSpace.S := A
   ; PreSpace.Cov := Cov'
  |}.

Existing Instances FormalSpace.FT FormalSpace.PreO
  FormalSpace.Cov_Proper FormalSpace.Cov_Proper2
  FormalSpace.Cov_Proper3.

Theorem t : FormTop.t Closed.
Proof.
constructor; unfold Cov'; intros.
- apply FormalSpace.refl. right. assumption.
- FormalSpace.etrans.
  destruct X. 
  + apply FormalSpace.refl. left. assumption.
  + apply X0. assumption.
- apply FormalSpace.le_left with b; assumption.
- FormalSpace.ejoin. simpl in *.  unfold Cov'. 
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

End Defn.

Lemma RelSame_iffT {A B} (R S : A -> B -> Type) :
  (forall a b, R a b <--> S a b) <--> (R ==== S).
Proof.
firstorder.
Qed.

Require Import FormTopC.Bundled.
Section IGDefn.

Context {A : IGT}.

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

Existing Instances Bundled.IGT_PreO
  FormTop.Cov_Proper FormTop.Cov_Proper2 FormTop.Cov_Proper3.

Definition LocalizedPS (X : PreISpace.t) : PreSpace.t :=
  {| PreSpace.S := PreISpace.S X
   ; PreSpace.Cov := FormTop.GCovL X
  |}.

Definition A' : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.C := SC
  |}.

Theorem same : PreSpace.Cov (LocalizedPS A') ==== PreSpace.Cov (Closed (A := fromIGT A) V).
Proof.
apply RelSame_iffT. intros a U. simpl. unfold Cov'. split; intros H.
- induction H.
  + apply FormTop.grefl. right. assumption.
  + simpl in *. apply FormTop.gle_left with b. assumption.
    assumption.
  + destruct i.
    * simpl. destruct (Bundled.localized A a b l i).
      simpl in *.
      apply (FormTop.ginfinity a _ x). intros. apply X.
      simpl. apply s. assumption.
    * rewrite l. apply FormTop.grefl. left. assumption. 
- simpl in H. remember (V ∪ U) as U' in H. 
  induction H; subst.
  + destruct u.
    * eapply FormTop.gmonotoneL. Focus 2.
    pose proof (PreO.le_refl a) as aa.
    pose proof (FormTop.gle_infinity (A := A') a (fun _ => False) a (InV v)
       aa) as H0.
    apply H0. intros u H1. simpl in *.
    destruct H1 as (u' & bot & downau). contradiction. 
    unfold Included, pointwise_rel, arrow; intros; contradiction.
    * apply FormTop.glrefl. assumption.
  + simpl in *. apply (FormTop.glle_left (A := A')) with b. assumption. apply IHGCov.
    reflexivity.
  + apply (FormTop.gle_infinity (A := A') a _ a (Orig i)).
    reflexivity. intros. destruct X0.  simpl in p. 
    destruct p, d. apply FormTop.glle_left with x. assumption. 
    apply X. assumption. reflexivity.
Qed.

End IGDefn.

End Subspace.