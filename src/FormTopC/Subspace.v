Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.Bundled
  FormTopC.FormTop
  CRelationClasses.

Local Open Scope Subset.
Set Universe Polymorphism.

Module Subspace.

Section Defn.
Universes S P.
Set Printing Universes.
Context {S : Type@{S}} {leS : crelation@{S P} S}.
Hypothesis POS : PreO.t leS.
Variable CovS : S -> (Subset@{S P} S) -> Type@{P}.

Definition Cov (V : Subset@{S P} S) (a : S)
  (U : Subset@{S P} S) : Type@{P} := CovS a (V ∪ U).


Context {FTS : FormTop.t leS CovS}.

Existing Instances FormTop.Cov_Proper.

Theorem t (V : Subset S) : FormTop.t leS (Cov V).
Proof.
constructor; unfold Cov; intros.
- apply FormTop.refl. right. assumption.
- FormTop.etrans.
  destruct X. apply FormTop.refl. left. assumption.
  apply X0. assumption.
- apply FormTop.le_left with b; assumption.
- FormTop.ejoin. FormTop.etrans.
  destruct X1. destruct d, d0.
  destruct i.
  rewrite l. apply FormTop.refl. left.  assumption.
  destruct i0. rewrite l0. apply FormTop.refl. left. assumption.
  rewrite <- Union_Included_r.
  apply FormTop.le_right. 
  eapply FormTop.Cov_Proper. apply l. reflexivity. apply FormTop.refl. assumption.
  eapply FormTop.Cov_Proper. apply l0. reflexivity. apply FormTop.refl. assumption.
Qed.

End Defn.

Arguments Cov {S} CovS V a U : clear implicits.

Section IGDefn.

Context {A : IGT}.

Variable V : Subset (S A). 

Definition SIx (a : S A) : Type :=
  (Ix A a + { I : True & V a })%type.

Definition SC (a : S A) (i : SIx a) : Subset (S A) := 
  match i with
  | inl i' => C A a i'
  | inr _ => fun _ => False
  end.

Existing Instances Bundled.IGT_PreO.

Theorem same : forall a U,
  iffT (FormTop.GCovL (le A) SC a U) (Cov (FormTop.GCovL (le A) (C A)) V a U).
Proof.
intros. unfold Cov. split; intros H.
- induction H.
  + apply FormTop.glrefl. right. assumption.
  + apply FormTop.glle_left with b. assumption.
    assumption.
  + destruct i.
    * apply (FormTop.gle_infinity a _ b i).
      assumption. intros. apply X. simpl. apply X0.
    * destruct s. apply FormTop.glle_left with b. assumption.
      apply FormTop.glrefl. left. assumption.
- remember (V ∪ U) as U' in H. induction H; subst.
  + destruct u.
    * eapply FormTop.gmonotoneL. Focus 2.
    pose proof (PreO.le_refl a) as aa.
    pose proof (FormTop.gle_infinity (I := SIx) (C := SC) a (fun _ => False) a (inr (existT (fun _ => V a) I v))
       aa) as H0.
    apply H0. intros u H1. simpl in *.
    destruct H1 as (u' & bot & downau). contradiction. 
    unfold Included, pointwise_rel, arrow; intros; contradiction.
    * apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b. assumption. apply IHGCovL.
    reflexivity.
  + apply (FormTop.gle_infinity (C := SC) a _ b (inl i)).
    assumption. intros.
    apply X. apply X0. reflexivity.
Qed.

End IGDefn.

End Subspace.