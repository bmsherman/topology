Require Import 
  Prob.StdLib 
  Coq.Lists.List
  Types.List
  Types.UIP
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.PreOrder
  Algebra.SetsC 
  FormTopC.Cont
  FormTopC.FormalSpace
  Algebra.FreeLattice.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Existing Instances 
  FormTop.GCov_formtop 
  FormalSpace.IGT_PreO 
  FormalSpace.IGTFT.

Local Open Scope FT.
Local Open Scope FreeML.



(** Product spaces for inductively generated formal topologies.
    See Section 4.3 of [1]. *)
Module Product.

Generalizable All Variables.
Section Product.

Universes A P I API API' Ix.
Context {Ix : Type@{Ix}}.
Context {Ix_UIP : EqdepFacts.UIP_ Ix}.
Variable X : Ix -> IGt@{A P I API}.

(** See
  https://www.cs.bham.ac.uk/~sjv/InfiniteTych.pdf
*)
Definition ProdPO@{} : PreOrder@{A P} :=
  ML.FreeML (SomeOpen X).

Inductive Ix'@{} : ProdPO -> Type@{I} := 
  | Slice : forall {x : SomeOpen X}, PreISpace.Ix (X (SOIx x)) (SOOpen x) -> 
      forall xs, Ix' (ML.inj x ∧ xs)
  | DimUnion : forall xs, Ix -> Ix' xs
  | ProdStable : forall {ix : Ix} (a a' : X ix) xs, 
    Ix' (MkSomeOpen ix a :: MkSomeOpen ix a' :: xs).

Arguments Ix' : clear implicits.

Inductive ExtSubset@{} {s : ProdPO} {ix : Ix} {C : Subset@{A P} (X ix)}
  : Subset@{A P} ProdPO :=
  | MkExtSubset : forall u, C u -> ExtSubset (ML.inj (MkSomeOpen ix u) ∧ s).

Arguments ExtSubset s {ix} C.

Definition C'@{} : forall (p : ProdPO), Ix' p -> Subset@{A P} ProdPO :=
  fun p ix' => match ix' with
  | Slice x ax xs => ExtSubset xs (PreISpace.C _ _ ax)
  | DimUnion xs ix => @ExtSubset xs ix (fun _ => True)
  | ProdStable ix a a' xs => @ExtSubset xs ix (eq a ↓ eq a')
  end.

Definition Prod@{} : PreISpace.t@{A P I} :=
  {| PreISpace.S := ProdPO
   ; PreISpace.Ix := Ix'
   ; PreISpace.C := C'
  |}.

Instance Sum_PO : PreO.t (le (SomeOpen X)).
Proof.
unshelve eapply PreOrder.Sum_PO. eassumption.
Qed.

Local Instance loc : 
  (forall ix, FormTop.localized (X ix)) 
 -> FormTop.localized Prod.
Proof.
intros locX.
unfold FormTop.localized.
intros a c H1 i. destruct i.
specialize (locX (SOIx x)).
simpl in H1.
apply Each_member in H1.
inv H1.
induction X0. induction S_holds.
simpl in *.
specialize (locX aix bix l i).
destruct locX.
Abort.


Definition Prodt : IGt :=
  {| IGS := Prod
   ; IGPO := ML.PO
  |}.

Definition proj (ix : Ix) : Cont.map Prodt (X ix) :=
  fun (out : X ix) => ⇓ eq (ML.inj (MkSomeOpen ix out)).

Lemma slice_cov_top (ix : Ix) (a : Prodt)
  : a <|[Prodt] union (fun _ : X ix => True)
                (fun out : X ix =>
                 eq (ML.inj (MkSomeOpen ix out))).
Proof.
eapply FormalSpace.trans.
apply (@ig_ax_cov Prodt _ (DimUnion a ix)).
simpl. intros s Cs.
inv Cs. clear H.
eapply FormTop.glle_left with (ML.inj (MkSomeOpen ix u)).
apply ML.bmeet_le_l.
apply FormTop.glrefl.
eexists. unfold In. auto.
reflexivity.
Qed.

  (* Hmm, this looks like I need to add rule 2 
     from page xv of
     https://www.cs.bham.ac.uk/~sjv/InfiniteTych.pdf.
     But since I don't require my axiom sets to be localized,
     perhaps that rule is actually just admissible?

     NO, in fact it should be enough to use rule 3, which should
     generalize to any covering a <| U, taking
     U = eq b ↓ eq c, so
     a <| eq b ↓ eq c
  *)
Lemma prod_stable (ix : Ix) (a a' : X ix) (xs : Prod) :
  (MkSomeOpen ix a :: MkSomeOpen ix a' :: xs)
  <|[Prodt] ExtSubset xs (eq a ↓ eq a').
Proof.
apply (@ig_ax_cov Prodt _ (@ProdStable ix a a' xs)).
Qed.

Lemma ext_le_cov (ix : Ix) {aix : X ix} 
  {U : Open (X ix)} (Hc : aix <|[X ix] U) (xs : Prodt)
  : (ML.inj (MkSomeOpen ix aix) ∧ xs) <|[Prodt] ExtSubset xs U.
Proof.
induction Hc.
- apply FormTop.refl. constructor. assumption.
- eapply FormTop.le_left.
  eapply (ML.le_app_r (ML.inj (MkSomeOpen ix a)) (ML.inj (MkSomeOpen ix b))).
  apply ML.le_singleton.
  econstructor. eassumption. simpl app.
  assumption.
- pose proof (FormTop.gle_infinity (A := Prodt) 
    (ML.inj (MkSomeOpen ix a) ∧ xs) (ExtSubset xs U) _ (@Slice (MkSomeOpen ix b) i xs))
    as H.
  eapply H; clear H. apply ML.le_cons.
  econstructor. eassumption. reflexivity.
  intros. destruct X1.
  le_downH d.
  destruct d0. induction i0. simpl in c.
  apply FormTop.glle_left with
     (ML.inj (MkSomeOpen ix a) ∧ ML.inj (MkSomeOpen ix u0) ∧ xs).
  apply ML.le_cons_r.
  rewrite d. apply ML.bmeet_le_l. apply l0.
  eapply (@FormTop.trans Prodt). typeclasses eauto. 
  apply prod_stable. simpl.
  intros. induction X1. apply X0.
  destruct c0. le_downH d1.
  split. assumption. exists u0; assumption. 
Qed.

Lemma t_proj (ix : Ix) : Cont.t Prodt (X ix) (proj ix).
Proof.
constructor; intros; unfold proj in *.
- eapply FormTop.monotone. 2: apply slice_cov_top.
  apply union_monotone.
  intros out. apply downset_included.
- le_down. le_downH X1. etransitivity; eassumption.
- le_downH X0. le_downH X1.
  pose proof (prod_stable ix b c a) as X2.
  assert (a <=[Prod] (MkSomeOpen ix b :: MkSomeOpen ix c :: a)) as X3.
  apply ML.le_cons_r. eassumption. 
  apply ML.le_cons_r. eassumption. reflexivity.
  apply (FormTop.le_left (A := Prodt) _ _ _ X3) in X2.  
  clear X0 X1 X3.
  eapply FormTop.monotone. 2: eassumption.
  clear X2.
  intros x Px. induction Px.
  destruct c0. eexists. split; eassumption.
  le_down. apply ML.bmeet_le_l.
- le_downH X0.
  pose proof (ext_le_cov ix X1 a) as X2.
  eapply FormTop.le_left. etransitivity. eapply ML.app_le. eapply X0.
  eapply ML.bmeet_comm. simpl app.
  eapply FormTop.monotone. 2: eassumption.
  clear X2. intros x []. eexists. eassumption.
  le_down. apply ML.bmeet_le_l.
Qed.

Variable A : FormalSpace.t.
Variable f : forall ix, Cont.map A (X ix).
Variable f_cont : forall ix, IGCont.t A (X ix) (f ix).

Definition univ : Cont.map A Prodt :=
  fun (out : Prodt) (a : A) => 
  Each (fun x : SomeOpen X => let (ix, uix) := x in
    (f ix) uix a) out.

Existing Instances FormalSpace.isFT.

Lemma univ_le_left (a : A) (b : Prodt) (c : A)
  : a <=[A] c -> univ b c -> univ b a.
Proof.
unfold univ. intros H H'. unfold Each. intros x mem.
destruct x as (ix & uix).
specialize (H' _ mem). simpl in H'. 
eapply (IGCont.le_left (f_cont ix)); eassumption.
Qed.

Lemma univ_app {a b c}
  (Hb : univ b a) (Hc : univ c a)
  : univ (b ∧ c) a.
Proof.
apply Each_app; split; assumption.
Qed.

Lemma univ_le_right {a b c}
  : a <=[Prodt] b -> univ a c -> univ b c.
Proof.
intros. unshelve eapply (ML.Each_monotone _ _ _ _ X0 X1).
simpl. intros.  destruct X2.
eapply (IGCont.le_right (f_cont ix)); eassumption.
Qed.

Lemma univ_cov (a : A)
 : forall l : Prodt, univ l a -> a <|[A] union (⇓ eq l) univ.
Proof.
intros xs H. eapply FormTop.refl.
eexists. 2: eassumption. 
unfold In. le_down. reflexivity.
Qed.

Existing Instances FormalSpace.PO.

Import ListNotations.

Theorem univ_cont : IGCont.t A Prodt univ.
Proof.
econstructor; intros.
- eapply FormTop.refl. exists []. unfold In. auto.
  apply Each_nil.
- eapply FormTop.monotone.
  eapply union_idx_monotone. eapply Same_set_Included.
  eapply ML.down_app.
  pose proof (univ_app X0 X1) as H. clear X0 X1.
  generalize dependent (b ∧ c). clear b c.
  apply univ_cov.
- eapply univ_le_left; eassumption.
- eapply (ML.Each_monotone). 2: eassumption. 2: eassumption.
  clear b c X0 X1.
  intros x y l H. induction l as [ix aix bix].
  eapply (IGCont.le_right (f_cont ix)); eassumption.
- induction j.
  + pose proof (X0 _ here) as tx. simpl in tx.
    induction tx. induction S_holds.
    simpl in i.
    pose proof (IGCont.ax_right (f_cont ix) a aix bix i l). 
    pose proof (X1 _ S_member) as X1'. simpl in X1'.
    specialize (X2 X1').
    eapply FormTop.le_right_eq in X2.
    eapply FormTop.monotone. 2: eassumption.
    apply Included_impl. intros u Pu.
    destruct Pu. le_downH d. destruct d0.
    destruct i0. destruct i0. le_downH d0.
    destruct d1.
    eexists. split. le_down.
    Focus 2. econstructor. econstructor.
    eapply i0. simpl SOIx.
    instantiate (1 := ML.inj (MkSomeOpen ix a1) ∧ t). 
    apply ML.le_cons. econstructor. eassumption.
    rewrite X0. apply ML.bmeet_le_r.
    apply ML.bmeet_le_r.
    apply univ_app. apply Each_singleton.
    eapply (IGCont.le_left (f_cont ix)). eassumption. eassumption.
    eapply univ_le_left. 2:eassumption. assumption.
  + pose proof (IGCont.here (f_cont i) a) as H'.
    apply FormTop.le_right_eq in H'.
    eapply FormTop.monotone. 2: apply H'.
    intros u Pu. destruct Pu. le_downH d. destruct d0.
    destruct i0. destruct i0.
    eexists. split. le_down.
    Focus 2. eexists. econstructor. 
    auto. instantiate (1 := a1).
    instantiate (1 := ML.inj (MkSomeOpen i a1) ∧ t).
    apply ML.le_cons. reflexivity. eassumption. 
    apply ML.bmeet_le_r.
    apply univ_app.
    * apply List.Each_singleton.
      eapply (IGCont.le_left (f_cont i)).  2: eassumption. 
      assumption. 
    * eapply univ_le_left. 2: eassumption. assumption.
  + simpl. 
    pose proof (IGCont.local (f_cont ix) a a0 a').
    pose proof (univ_le_right X0 X1) as X3.
    assert (univ xs a) as X4.
    eapply univ_le_right. 2: eapply X3.
    apply ML.FSubset_le.
    apply (FSubset_app_r [MkSomeOpen ix a0; MkSomeOpen ix a']).
    specialize (X2 (X3 _ here) (X3 _ (there here))).
    pose proof (univ_cov _ _ X1).
    FormTop.ejoin.
    eapply FormTop.trans. eassumption. clear X6.
    intros. apply FormTop.refl.
    destruct X2. destruct d, d0.
    destruct i, i0. unfold In in i0. le_downH i0.
    exists (ML.inj (MkSomeOpen ix a4) ∧ a5).  split. le_down. 
    rewrite ML.bmeet_le_r.  assumption.
    eexists.  econstructor. eassumption.
    apply ML.le_cons. reflexivity. rewrite i0.
    rewrite X0.
    apply ML.FSubset_le.
    apply (FSubset_app_r [MkSomeOpen ix a0; MkSomeOpen ix a']).
    apply univ_app. 
    eapply univ_le_left. apply l.
    apply Each_singleton. simpl. assumption.
    eapply univ_le_left. apply l0.
    assumption.
Qed.


(** Prove the space has a positivity predicate. *)

Context {X_Pos : forall ix : Ix, FormTop.gtPos (X ix)}.

Definition PosProd : Subset Prod :=
  Each (fun x => FormTop.gPos (SOOpen x)).

Local Open Scope Subset.

(*
Lemma PosProd_factors (a : Prod) :
  eq a ∩ PosProd === fun p => forall ix : Ix,
  (eq (a ix) ∩ FormTop.gPos) (p ix).
Proof.
apply Same_set_iff.
intros. split; intros H.
- destruct H. subst. intros. split. reflexivity.
  apply p.
- split. extensionality ix. destruct (H ix). assumption. 
  intros ix. apply H.
Qed.
*)

Existing Instance GCovL_formtop.

Lemma Pos : FormTop.gtPos Prod.
Proof.
unshelve econstructor.
- exact PosProd.
- intros a b l. apply (ML.Each_monotone (X := SomeOpen X)).
  2: assumption.
  clear a b l.
  intros x y l H. induction l.
  eapply FormTop.gmono_le; eassumption.
- intros b i a X0 X1. destruct i.
Admitted.
(*
  pose proof (FormTop.gmono_ax (gtPos := IGpos (X ix)) (b ix)
     i (a ix) (X0 ix) (X1 ix)).
- intros.
  apply (FormTop.trans (A := Prod) (U := eq a ∩ PosProd)).
  + eapply gmonotoneL. eapply Same_set_Included. 
    apply PosProd_factors.
    eapply factors; apply FormTop.gpositive; 
    intros; apply FormTop.grefl; split; trivial.
  + intros. destruct X1. subst. apply X0. assumption.
Qed.
*)

End Product.
End Product.