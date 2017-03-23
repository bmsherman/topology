Require Import 
  Prob.StdLib 
  Coq.Lists.List
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC 
  FormTopC.Cont
  FormTopC.FormalSpace
  Eqdep_dec
  FunctionalExtensionality
  Types.List.

Import ListNotations.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Existing Instances 
  FormTop.GCov_formtop 
  FormalSpace.IGT_PreO 
  FormalSpace.IGTFT
  FormalSpace.IGT_Pos.

Lemma UIP_eq_dep_eq {A} :
  EqdepFacts.UIP_ A -> EqdepFacts.Eq_dep_eq A.
Proof.
intros H. apply EqdepFacts.eq_rect_eq__eq_dep_eq.
apply EqdepFacts.Streicher_K__eq_rect_eq.
apply EqdepFacts.UIP_refl__Streicher_K.
apply EqdepFacts.UIP__UIP_refl. assumption.
Qed.

Lemma UIP_inj_dep_pair {A} :
  EqdepFacts.UIP_ A -> EqdepFacts.Inj_dep_pair A.
Proof.
intros H. apply EqdepFacts.eq_dep_eq__inj_pair2.
apply UIP_eq_dep_eq. assumption.
Qed.


Local Open Scope FT.


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
Record SomeOpen@{} : Type@{A} := MkSomeOpen
  { SOIx : Ix
  ; SOOpen : S (fromIGt@{A P I API API'} (X SOIx))
  }.

Inductive SomeOpen_le : SomeOpen -> SomeOpen -> Type :=
  | MkSomeOpen_le : forall ix (aix bix : S (fromIGt@{A P I API API'} (X ix))),
     aix <=[X ix] bix
     -> SomeOpen_le (MkSomeOpen ix aix) (MkSomeOpen ix bix).

Definition S'@{} : Type@{A} := 
  list SomeOpen.

Definition le' (a b : S') :=
  Each (fun ub => LSome (fun ua => SomeOpen_le ua ub) a) b.

Inductive Ix'@{} : S' -> Type@{I} := 
  | Slice : forall {x}, PreISpace.Ix (X (SOIx x)) (SOOpen x) -> forall xs, Ix' (x :: xs)
  | DimUnion : forall xs, Ix -> Ix' xs.

Arguments Ix' : clear implicits.

Inductive ExtSubset@{} {s : S'} {ix : Ix} {C : Subset@{A P} (X ix)}
  : Subset@{A P} S' :=
  | MkExtSubset : forall u, C u -> ExtSubset (MkSomeOpen ix u :: s).

Arguments ExtSubset s {ix} C.

Definition C'@{} : forall (p : S'), Ix' p -> Subset@{A P} S' :=
  fun p ix' => match ix' with
  | Slice x ax xs => ExtSubset xs (PreISpace.C _ _ ax)
  | DimUnion xs ix => @ExtSubset xs ix (fun _ => True)
  end.

Definition ProdPreO@{} : FormTop.PreOrder@{A P} :=
  {| PO_car := S'
   ; FormTop.le := le'
  |}.

Definition Prod@{} : PreISpace.t@{A P I} :=
  {| PreISpace.S := ProdPreO
   ; PreISpace.Ix := Ix'
   ; PreISpace.C := C'
  |}.

Local Instance Sum_PO : PreO.t SomeOpen_le.
Proof.
constructor; simpl; intros.
- destruct x. econstructor. reflexivity.
- induction X0. inv X1.
  econstructor.
  apply UIP_inj_dep_pair in H1. subst. 
  etransitivity; eassumption.
  assumption.
Qed.

Local Instance PO : PreO.t (le Prod).
Proof.
constructor; simpl; unfold le'; intros. 
- intros x' mem. econstructor. eassumption.
  reflexivity.
- unfold Each. intros. 
  specialize (X1 x0 X2). simpl in X1.
  induction X1.
  specialize (X0 _ S_member). simpl in X0.
  induction X0.
  econstructor. eassumption.
  etransitivity; eassumption.
Qed.

Lemma FSubset_le (xs ys : Prod) : (ys ⊆ xs)%list -> xs <=[Prod] ys.
Proof.
simpl. unfold le', FSubset, Each.
intros H x mem.
eexists x. apply H. assumption.
reflexivity.
Qed.

Local Open Scope Subset.

Lemma app_le (xs ys : Prod) : 
  xs <=[Prod] ys -> xs <=[Prod] (xs ++ ys).
Proof.
simpl. unfold le', Each. intros H x mem.
apply member_app in mem. induction mem.
- econstructor. eassumption. reflexivity.
- apply H. assumption.
Qed.

Lemma le_app_r (xs xs' ys : Prod)
  : xs <=[Prod] xs' -> (xs ++ ys) <=[Prod] (xs' ++ ys).
Proof.
simpl. unfold le', Each. intros H x mem.
apply member_app in mem. apply LSome_app.
induction mem.
- left. apply H. assumption.
- right. econstructor. eassumption. reflexivity. 
Qed.

Lemma le_singleton (a b : SomeOpen)
  : SomeOpen_le a b <--> [a] <=[Prod] [b].
Proof.
simpl; unfold le', Each; split; intros H.
- intros x mem. apply member_singleton in mem.
  subst. econstructor. econstructor. eassumption.
- specialize (H _ here). induction H.
  apply member_singleton in S_member.
  subst. assumption.
Qed.

Lemma le_app_swap (xs ys : Prod)
  : (xs ++ ys) <=[Prod] (ys ++ xs).
Proof.
simpl. unfold le', Each. intros x mem.
apply member_app in mem. apply LSome_app.
induction mem; [right | left]; 
  (econstructor; [eassumption | reflexivity]).
Qed.

Lemma le_app_l (ys ys' xs : Prod)
  : ys <=[Prod] ys' -> (ys ++ xs) <=[Prod] (ys' ++ xs).
Proof.
intros H.
rewrite (le_app_swap ys).
etransitivity.
Focus 2. eapply le_app_r. eassumption.
apply le_app_swap.
Qed.

Lemma le_app_distr {xs xs' ys ys'}
  : xs <=[Prod] xs' -> ys <=[Prod] ys' -> (xs ++ ys) <=[Prod] (xs' ++ ys').
Proof.
simpl. unfold le', Each.
intros Hx Hy x mem.
apply member_app in mem. apply LSome_app.
induction mem.
- left. apply Hx. assumption.
- right. apply Hy. assumption.
Qed.


Lemma le_cons (a b : SomeOpen) (xs ys : Prod)
  : SomeOpen_le a b -> xs <=[Prod] ys -> (a :: xs) <=[Prod] (b :: ys).
Proof.
intros H H'.
apply (@le_app_distr [a] [b] xs ys).
apply le_singleton. assumption. assumption.
Qed.

Local Instance loc : 
  (forall ix, FormTop.localized (X ix)) 
 -> FormTop.localized Prod.
Proof.
intros locX.
unfold FormTop.localized.
intros a c H1 i. destruct i.
specialize (locX (SOIx x)).
simpl in H1. unfold le' in H1.
apply Each_member in H1.
inv H1.
induction X0. induction S_holds.
simpl in *.
specialize (locX aix bix l i).
destruct locX.
Admitted.

(** Prove the space has a positivity predicate. *)
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
- unfold PosProd. intros a b l H. 
  unfold Each. intros.
  simpl in l. unfold le' in l.
  specialize (l x X0). simpl in l.
  induction l. induction S_holds. simpl in *.
  eapply FormTop.gmono_le. eassumption. 
  specialize (H _ S_member). simpl in H.
  assumption.
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

(*
Lemma factors (xs : S')
  (U : forall x, member x xs -> Open (X (SOIx x)))
  (Cov : forall x (H : member x xs), SOOpen x <|[@toPreSpaceUL (X (SOIx x))] U x H)
  : xs <|[@toPreSpaceUL Prod] (fun p => forall x (H : member x xs), 
    Some   p).
  (Cov : Each (fun x => ) xs
 ( : a <|[@toPreSpaceUL X] U -> b <|[@toPreSpaceUL Y] V -> 
  (a, b) <|[@toPreSpaceUL Prod] (fun p => let (a', b') := p in U a' * V b')%type.
Proof.
intros H H0. induction H.
- induction H0.
  + apply FormTop.grefl. split; assumption.
  + eapply FormTop.gle_left. 2:apply IHGCov.
    split; simpl. apply PreO.le_refl. assumption.
  + apply (FormTop.ginfinity) with (PRight i a).
    intros. simpl in X0. destruct u0. destruct X1. 
    subst. apply X0. assumption.
- apply FormTop.gle_left with (b0, b). split; simpl.
  assumption. reflexivity.
  apply IHGCov.
- apply (FormTop.ginfinity) with (PLeft i b).
  intros. simpl in X1. destruct u. destruct X1. 
  subst. apply X0. assumption.
Qed.
*)

Axiom undefined : forall A, A.

Definition Prodt : IGt :=
  {| IGS := Prod
   ; IGPO := PO
   ; IGpos := undefined _ (*Pos*)
  |}.


Definition proj (ix : Ix) : Cont.map Prodt (X ix) :=
  fun (out : X ix) => ⇓ eq ([MkSomeOpen ix out] : Prod).

Lemma slice_cov_top (ix : Ix) (a : Prodt)
  : a <|[Prodt] union (fun _ : X ix => True)
                (fun out : X ix =>
                 eq [{| SOIx := ix; SOOpen := out |}]).
Proof.
eapply (@FormalSpace.trans Prodt).
apply (@ig_ax_cov Prodt _ (DimUnion a ix)).
simpl. intros s Cs.
inv Cs. clear H.
eapply FormTop.glle_left with [{| SOIx := ix; SOOpen := u |}].
apply FSubset_le.
apply FSubset_cons. apply FSubset_nil.
apply FormTop.glrefl.
eexists. unfold In. auto.
reflexivity.
Qed.

Lemma ext_le_cov (ix : Ix) {aix : X ix} 
  {U : Open (X ix)} (Hc : aix <|[X ix] U) (xs : Prodt)
  : (MkSomeOpen ix aix :: xs) <|[Prodt] ExtSubset xs U.
Proof.
induction Hc.
- apply FormTop.refl. constructor. assumption.
- eapply FormTop.le_left.
  eapply (le_app_r [MkSomeOpen ix a] [MkSomeOpen ix b]).
  eapply le_singleton.
  econstructor. eassumption. simpl app.
  assumption.
- pose proof (FormTop.gle_infinity (A := Prodt) 
    (MkSomeOpen ix a :: xs) (ExtSubset xs U) _ (@Slice (MkSomeOpen ix b) i xs))
    as H.
  eapply H; clear H. apply le_cons.
  econstructor. eassumption. reflexivity.
  intros. destruct X1.
  le_downH d.  destruct d0. induction i0. simpl in l0.
  (* I think this won't go through without rule 2 from 
   page xv. *)
Admitted.


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
Lemma prod_stable (ix : Ix) (a a' : X ix) (xs : S') :
  (MkSomeOpen ix a :: MkSomeOpen ix a' :: xs)
  <|[Prodt] ExtSubset xs (eq a ↓ eq a').
Proof.
Admitted.

Lemma le_cons_r {xs ys : Prodt} {a : SomeOpen}
  (Ha : xs <=[Prod] [a]) (Hys : xs <=[Prod] ys)
  : xs <=[Prod] (a :: ys).
Proof.
simpl. unfold le', Each.
intros x mem. inv mem.
- apply Ha. constructor.
- apply Hys. assumption.
Qed.

Lemma t_proj (ix : Ix) : Cont.t Prodt (X ix) (proj ix).
Proof.
constructor; intros; unfold proj in *.
- eapply FormTop.monotone. 2: apply slice_cov_top.
  apply union_monotone.
  intros out. apply downset_included.
- le_down. le_downH X1. etransitivity; eassumption.
- le_downH X0. le_downH X1.
  pose proof (prod_stable ix c b a).
  assert (a <=[Prod] ({| SOIx := ix; SOOpen := c |}
       :: {| SOIx := ix; SOOpen := b |} :: a)).
  apply le_cons_r. eassumption. apply le_cons_r.
  eassumption. reflexivity.
  apply (FormTop.le_left (A := Prodt) _ _ _ X3) in X2.  
  clear X0 X1 X3.
  eapply FormTop.trans. eapply X2.
  clear X2.
  intros. induction X0. simpl.
  apply (FormTop.refl (A := Prodt)).
  destruct c0. eexists. split; eassumption.
  le_down. apply FSubset_le. apply FSubset_cons.
  apply FSubset_nil.
- le_downH X0.
  pose proof (ext_le_cov ix X1 a) as X2.
  eapply FormTop.le_left. etransitivity. eapply app_le. eapply X0.
  eapply le_app_swap. simpl app.
  eapply FormTop.trans. eapply X2. clear X2.
  intros. destruct X2.
  eapply FormTop.refl. eexists. eassumption.
  le_down. apply FSubset_le. apply FSubset_cons. apply FSubset_nil. 
Qed.

Variable A : FormalSpace.t.
Variable f : forall ix, Cont.map A (X ix).
Variable f_cont : forall ix, IGCont.t A (X ix) (f ix).

Definition univ : Cont.map A Prodt :=
  fun (out : Prodt) (a : A) => 
  Each (fun x : SomeOpen => let (ix, uix) := x in
    (f ix) uix a) out.

Existing Instances FormalSpace.isFT.

Lemma univ_le_left (a : A) (b : Prodt) (c : A)
  : a <=[PreSpace.S A] c -> univ b c -> univ b a.
Proof.
unfold univ. intros H H'. unfold Each. intros x mem.
destruct x as (ix & uix).
specialize (H' _ mem). simpl in H'. 
eapply (IGCont.le_left (f_cont ix)); eassumption.
Qed.

Lemma le_app_each (l x y : Prodt)
  (lx : l <=[Prodt] x) (ly : l <=[Prodt] y)
  : l <=[Prodt] (x ++ y).
Proof.
simpl. unfold le', Each. intros u mem.
apply member_app in mem. destruct mem.
- apply lx. assumption.
- apply ly. assumption.
Qed.

Lemma down_app (b c : Prodt) : (eq b ↓ eq c) === ⇓ (eq (b ++ c) : Prodt -> Prop).
Proof.
apply Same_set_iff.
intros bc. split; intros.
- destruct X0. le_downH d. le_downH d0.
  le_down.
  apply le_app_each; assumption.
- le_downH X0. split; le_down.
  etransitivity. eassumption. apply FSubset_le.
  apply FSubset_app_l.
  etransitivity. eassumption. apply FSubset_le. 
  apply FSubset_app_r.
Qed.

Lemma univ_app {a b c}
  (Hb : univ b a)
  (Hc : univ c a)
  : univ (b ++ c) a.
Proof.
unfold univ in *. 
apply Each_app; split; assumption.
Qed.

Lemma univ_cov (a : A)
 : forall l : Prodt, univ l a -> a <|[A] union (⇓ eq l) univ.
Proof.
intros xs H. eapply FormTop.refl.
eexists. 2: eassumption. 
eexists. reflexivity. reflexivity.
Qed.

Existing Instances FormalSpace.PO.

Theorem univ_cont : IGCont.t A Prodt univ.
Proof.
econstructor; intros.
- eapply FormTop.refl. exists []. unfold In. auto.
  unfold univ. unfold Each. intros x mem. inv mem.
- eapply FormTop.monotone.
  eapply union_idx_monotone. eapply Same_set_Included.
  eapply down_app.
  pose proof (univ_app X0 X1) as H. clear X0 X1.
  generalize dependent (b ++ c). clear b c.
  apply univ_cov.
- eapply univ_le_left; eassumption.
- unfold univ in *. intros x mem. 
  specialize (X1 _ mem). simpl in X1.
  induction X1. specialize (X0 _ S_member).
  simpl in X0. induction S_holds.
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
    instantiate (1 := MkSomeOpen ix a1 :: t). 
    apply le_cons. econstructor. eassumption.
    intros x mem. apply (X0 _ (there mem)).
    apply FSubset_le. apply (FSubset_app_r [_]).
    intros x mem. inv mem.
    eapply (IGCont.le_left (f_cont ix)). eassumption. eassumption.
    pose proof (univ_le_left _ _ _ d X1) as H.
    specialize (H _ X3). simpl in H. apply H.
  + pose proof (IGCont.here (f_cont i) a) as H'.
    apply FormTop.le_right_eq in H'.
    eapply FormTop.trans. eapply H'.
    intros u Pu. destruct Pu. le_downH d. destruct d0.
    destruct i0. destruct i0.
    eapply FormTop.refl.
    eexists. split. le_down.
    Focus 2. eexists. econstructor. 
    auto. instantiate (1 := a1).
    instantiate (1 := MkSomeOpen i a1 :: t).
    apply le_cons. econstructor. reflexivity. eassumption.
    apply FSubset_le. apply (FSubset_app_r [_]).
    intros x mem.
    inv mem. eapply (IGCont.le_left (f_cont i)).  2: eassumption. 
    assumption. 
    specialize (X1 _ X2). simpl in X1.
    destruct x as (ix & uix).
    eapply (IGCont.le_left (f_cont ix)). eapply d. assumption.
Qed.

End Product.
End Product.
