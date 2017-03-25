Require Import 
  Algebra.PreOrder
  Algebra.OrderC
  Algebra.SetsC
  FormTopC.FormTop
  FormTopC.FormalSpace
  FormTopC.Subspace.

Local Open Scope FT.
Local Open Scope Subset.

(** Inductively generated spaces have arbitrary meets *)
Section Meet.
Context {A : PreOrder}.
Context {Ix : Type}.
Context {Ax : Ix -> A -> Type}.
Variable (C : forall (ix : Ix) (a : A), Ax ix a -> Open A).

Inductive MIx {a : A} : Type :=
  | MkMIx : forall (ix : Ix), Ax ix a -> MIx.

Arguments MIx : clear implicits.

Definition MC (a : A) (ax : MIx a) : Open A := match ax with
  | MkMIx ix ax' => C ix a ax'
  end.

Definition Component (ix : Ix) : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.Ix := Ax ix
   ; PreISpace.C := C ix
  |}.

Definition Meet : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.Ix := MIx
   ; PreISpace.C := MC
  |}.

Existing Instance GCovL_formtop.

Lemma Meet_AxiomSetRefine_le (ix : Ix)
  : AxiomSetRefine (C ix) MC.
Proof.
unshelve econstructor.
econstructor. eassumption.
simpl. reflexivity.
Qed.

Lemma Meet_AxiomSetRefine_least I' (C' : forall s, I' s -> Open A)
  (H : forall ix : Ix, AxiomSetRefine (C ix) C')
  : AxiomSetRefine MC C'.
Proof.
unfold AxiomSetRefine.
intros s i. destruct i as [ix a].
destruct (H ix s a) as [x s0].
exists x. simpl. assumption.
Qed.

Lemma Meet_le (ix : Ix)
  {a : A} {U : Open A}
  : a <|[toPSL (Component ix)] U -> a <|[toPSL Meet] U.
Proof.
apply AxRefineCovL. apply Meet_AxiomSetRefine_le.
Qed.

Hypothesis pos : forall ix : Ix, FormTop.gtPos (Component ix).

Lemma loc_mono {A' : PreSpace.t} {FTA' : FormTop.t A'} 
  {tPos : tPos A'} (a : A') (U : Open A')
  : Pos a -> a <|[A'] U -> Inhabited (eq a ↓ U ∩ Pos).
Proof.
intros H H'.
eapply FormTop.mono. eassumption.
apply le_right_eq. assumption.
Qed.

Lemma loc_top {A' : PreSpace.t} {FTA' : FormTop.t A'} 
  {tPos : tPos A'} (a : A')
  : Pos a -> Inhabited (⇓ eq a ∩ Pos).
Proof.
intros H.
pose proof (loc_mono a (fun _ => True) H).
eapply Inhabited_mono. 2: eapply X.
apply Intersection_Proper_le. apply Intersection_Included_l.
reflexivity. apply FormTop.refl. unfold In. auto.
Qed.

Lemma MeetPos : FormTop.gtPos Meet.
Proof.
unshelve econstructor.
- exact (fun x => forall ix : Ix, gPos (A := Component ix) x).
- simpl. intros. eapply gmono_le; eauto.
- simpl. intros. 
  induction i; simpl.
  pose proof (gmono_ax b a0 a X (X0 ix)).
  revert X1. apply Inhabited_mono.
  simpl. apply Intersection_Proper_le. 
  reflexivity. intros x Px.
Abort.
(** I don't think it's actually possible to compute the
    positivity predicate for meets of subspaces. Or, at the least,
    the positivity predicate isn't just the intersection of the
    respective positivity predicates for the subspaces.
*)

End Meet.

(** Open and closed subspaces are inductively generated. *)
Section OpenClosed.

Context {A : PreOrder}.

Variable V : Open A. 

Inductive ClosedIx {a : A} : Type :=
  | InV : V a -> ClosedIx.

Arguments ClosedIx : clear implicits.

Definition ClosedC (a : A) (i : ClosedIx a) : Open A := 
  match i with
  | InV _ => fun _ => False
  end.

Inductive OpenIx {a : A} : Type :=
  | MkOpenIx.

Arguments OpenIx : clear implicits.

Definition OpenC (a : A) (_ : OpenIx a) : Open A := V.

Definition LocalizedPS (X : PreISpace.t) : PreSpace.t :=
  {| PreSpace.S := PreISpace.S X
   ; PreSpace.Cov := FormTop.GCovL X
  |}.

Definition A' : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.C := ClosedC
  |}.

(*
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
*)

End OpenClosed.