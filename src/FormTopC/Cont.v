Require Import 
  Basics
  CMorphisms
  FormTopC.FormTop
  Algebra.SetsC
  Algebra.OrderC
  Algebra.FrameC
  Prob.StdLib.

Set Universe Polymorphism.
Local Open Scope Subset.
Local Open Scope FT.

(** Continuous maps. *)
Module Cont.

Definition map@{AS PS XS AT PT XT PS'} 
  (S : PreSpace.t@{AS PS XS})
  (T : PreSpace.t@{AT PT XT}) : Type@{PS'} 
  := T -> Subset@{AS PS} S.

Section Cont.
Universes AS PS XS AT PT XT PS'.
Context {S : PreSpace.t@{AS PS XS}}
        {T : PreSpace.t@{AT PT XT}}.

Record t@{} {F_ : map@{AS PS XS AT PT XT PS'} S T} : Type :=
  { here : forall a, a <|[S] (union@{AT AS PT PS} (fun _ : T => True) F_) 
  ; le_left : forall a b c, a <=[S] c -> F_ b c -> F_ b a
  ; local : forall {a b c}, F_ b a -> F_ c a
    -> a <|[S] union@{AT AS PT PS} (eq b ↓ eq c) F_
  ; cov : forall {a b} V, F_ b a -> b <|[T] V
    -> a <|[S] union@{AT AS PT PS} V F_ 
  }.

Arguments t F_ : clear implicits.

Definition Sat@{} (F_ : map@{AS PS XS AT PT XT PS'} S T) 
  : map@{AS PS XS AT PT XT PS'} S T := fun t s =>
  s <|[S] F_ t.

Definition func_LE@{} 
  (F_ G_ : map@{AS PS XS AT PT XT PS'} S T) : Type@{PS'} :=
  RelIncl@{AT AS PS PS'} (Sat F_) (Sat G_).

Definition func_EQ@{} (F_ G_ : map S T) : Type@{PS'} :=
  RelSame@{AT AS PS PS'} (Sat F_) (Sat G_).

Context {POS : PreO.t@{AS PS} (le S)}
        {POT : PreO.t@{AT PT} (le T)}.

Global Instance func_LE_PreOrder : CRelationClasses.PreOrder func_LE.
Proof.
constructor; unfold Reflexive, Transitive, func_LE; intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Global Instance func_EQ_Equivalence : Equivalence func_EQ.
Proof.
constructor; unfold Reflexive, Transitive, Symmetric, func_EQ; intros.
- reflexivity.
- symmetry; assumption.
- etransitivity; eassumption.
Qed.

Lemma func_LE_antisym : forall (F F' : map S T),
  func_LE F F' -> func_LE F' F -> func_EQ F F'.
Proof.
unfold func_LE, func_EQ. intros.
apply RelIncl_RelSame; assumption.
Qed.

Lemma func_EQ_LE F F' : func_EQ F F' -> func_LE F F'.
Proof.
unfold func_EQ, func_LE. intros. apply RelSame_RelIncl.
assumption.
Qed.

Record pt {F : Subset T} :=
  { pt_here : Inhabited F
  ; pt_local : forall {b c}, F b -> F c -> Inhabited ((eq b ↓ eq c) ∩ F)
  ; pt_cov : forall {b V}, F b -> b <| V -> Inhabited (F ∩ V)
  }.

Arguments pt F : clear implicits.

(** Convert a continuous map for formal topologies to a 
    frame homomorphism (i.e., continuous map on locales)
  *)
Definition frame (F_ : map S T) (U : Subset T) : Subset S :=
  union U F_.

Hypothesis FTS : FormTop.t S. 
Hypothesis FTT : FormTop.t T.

Lemma Sat_mono2 (F_ : map S T) : F_ ⊑ Sat F_.
Proof.
unfold RelIncl. intros. unfold Sat.
unfold Included, pointwise_rel, arrow; intros.
apply FormTop.refl. assumption.
Qed.

Lemma Sat_mono (F_ G_ : map S T) : 
  F_ ⊑ G_ -> 
  Sat F_ ⊑ Sat G_.
Proof.
unfold RelIncl, Sat; intros.
unfold Included, pointwise_rel, arrow; intros.
eapply FormTop.monotone. apply X. assumption.
Qed.

Lemma Sat_idempotent (F_ : map S T) :
  Sat F_ ==== Sat (Sat F_).
Proof.
apply RelIncl_RelSame. apply Sat_mono2.
unfold RelIncl, Included, pointwise_rel, arrow, Sat.
intros.
eapply FormTop.trans. eassumption.
intros. assumption.
Qed.

Lemma func_EQ_Sat (F_ G_ : map S T)
  : func_EQ F_ G_ -> func_EQ (Sat F_) (Sat G_).
Proof.
unfold func_EQ. intros.
rewrite <- !Sat_idempotent. assumption.
Qed.

Section DirectedSup.
Context {Ix : Type} `{JoinLat.t Ix}.
Variable (f : Ix -> map S T).
Variable (fmono : forall i j, JoinLat.le i j -> f i ⊑ f j).
Definition func_Dsup : map S T := fun t s =>
  { i : Ix & f i t s }.

Lemma oneIncl i : f i ⊑ func_Dsup.
Proof.
intros. unfold RelIncl, Included, pointwise_rel, arrow; intros.
exists i. assumption.
Qed.

Lemma single_Dsup : forall i a U,
 a <| union U (f i) ->
 a <| (union U func_Dsup).
Proof.
intros. eapply FormTop.Cov_Proper.
reflexivity. apply union_monotone. apply (oneIncl i).
assumption.
Qed.

Variable nonempty : Ix.

Lemma func_Dsup_Cont : (forall i, Cont.t (f i)) -> Cont.t func_Dsup.
Proof.
intros iCont. constructor; intros.
- eapply single_Dsup. apply (Cont.here (iCont nonempty)).
- unfold func_Dsup in *. destruct X0.
  exists x. eapply (Cont.le_left (iCont x)); eassumption.
- destruct X, X0.
  pose (x' := JoinLat.max x x0).
  apply single_Dsup with x'.
  apply (Cont.local (iCont x')).
  eapply fmono; (apply JoinLat.max_ok || assumption).
  eapply fmono. eapply PreO.max_r. apply JoinLat.max_ok. 
  assumption.
- destruct X. apply single_Dsup with x.
  eapply (Cont.cov (iCont x)). eassumption. assumption.
Qed.

End DirectedSup.

End Cont.

Arguments t : clear implicits.
Arguments pt : clear implicits.


(** I might have broken this tactic. *)
Ltac ecov := match goal with
 | [ H : In (?f _) ?a, X : t ?S _ ?F  
      |- ?Cov ?S ?a (union _ ?F) ] => 
    eapply (cov X _ H)
  end.


Section Morph.

Context {S : PreSpace.t}.
Context {POS : PreO.t (le S)}
        {FTS : FormTop.t S}.

Definition id (x y : S) := (y <= x)%FT.

Theorem t_id : t S S id.
Proof.
constructor; intros; unfold id in *.
- eapply FormTop.refl. exists a; eauto. unfold In. constructor. 
  reflexivity.
- eapply PreO.le_trans; eassumption.
- apply FormTop.refl. exists a. 
  apply down_eq.
split; eassumption.
  reflexivity.
- eapply FormTop.le_left; try eassumption.
  clear X. FormTop.trans X0.
  apply FormTop.refl. econstructor. eassumption.
  reflexivity.
Qed.

Context {T : PreSpace.t}.
Context {POT : PreO.t (le T)}
        {FTT : FormTop.t T}.

Context {U : PreSpace.t}.
Context {POU : PreO.t (le U)}
        {FTU : FormTop.t U}.

(*
Everything in s maps to u
iff there is some subset T such that
  everything in s maps to T and
  everything in T maps to u
*)

Theorem t_compose : forall (F : map S T) (G : map T U),
    t S T F
  -> t T U G
  -> t S U (compose G F).
Proof.
intros. constructor; intros.
- pose proof (here X a) as X1.
  FormTop.trans X1. destruct X1. destruct i.
  pose proof (here X0 a0).
  pose proof (cov X _ f X1).
  refine (FormTop.monotone _ _ _ _ X2).
  apply Same_set_Included. symmetry.
  apply union_compose.
- unfold compose in *.
  intros. 
  destruct X2 as [t1 [Fat1 Gt1b]]. 
  exists t1. split. eassumption. eapply (le_left X). eassumption.
  assumption.
- destruct X1 as [t1 [Gt1b Fat1]]. 
  destruct X2 as [t2 [Gt2b Fat2]].
  pose proof (local X Fat1 Fat2).
  eapply FormTop.trans.
  eassumption. simpl. intros.
  destruct X2 as [tt downtt].
  apply (FormTop.monotone)
  with (union (union (eq b ↓ eq c) G) F). 
  apply Same_set_Included. symmetry.
  apply union_compose.
  eapply (cov X). eassumption.
  apply down_eq in downtt.
  destruct downtt as [tt1 tt2].
  apply (local X0).
  eapply (le_left X0). eapply tt1. eassumption.
  eapply (le_left X0). eapply tt2. eassumption.
- destruct X1 as [t [Gtb Fat]].
  apply (FormTop.monotone) with (union (union V G) F).
  apply Same_set_Included. symmetry. apply union_compose.
  apply (cov X _ Fat).
  apply (cov X0 _ Gtb). assumption.
Qed.

Lemma compose_proper_LE : forall (F F' : map S T) (G G' : map T U),
  Cont.t S T F' ->
  func_LE (S := S) F F' -> func_LE (S := T) G G' -> 
  func_LE (S := S) (compose G F) (compose G' F').
Proof.
unfold func_LE, compose. 
intros F F' G G' ContF X X0. unfold RelSame.
intros. unfold RelIncl, Included, pointwise_rel, arrow.
unfold Sat, In.
intros. unfold In in *.
FormTop.trans X1. destruct X1. destruct p. 
  apply (Sat_mono2 (S := T)) in g.
  apply (Sat_mono2 (S := S)) in f.
  apply X0 in g. apply X in f.
  unfold Sat in g, f. FormTop.etrans.
  pose proof (fun a b => Cont.cov ContF (a := a) (b := b)).
  specialize (X1 _ _ _ f g). clear f.
  FormTop.etrans. destruct X1. 
  apply FormTop.refl. exists a1. split; assumption.
  eassumption. eassumption.
Qed.

Lemma compose_proper : forall (F F' : map S T) (G G' : map T U),
  Cont.t S T F ->
  Cont.t S T F' ->
  func_EQ (S := S) F F' -> func_EQ (S := T) G G' -> 
  func_EQ (S := S) (compose G F) (compose G' F').
Proof.
intros. apply func_LE_antisym; apply compose_proper_LE;
  repeat (assumption || apply func_EQ_LE || symmetry).
Qed.

End Morph.
End Cont.

Arguments Cont.t : clear implicits.


Module IGCont.
Section IGCont.

Context {S : PreSpace.t}.
Context {T : PreISpace.t}.

Context {POS : PreO.t (le S)}
        {POT : PreO.t (le T)}.

Record t {F_ : Cont.map S T} :=
  { here : forall a, a <|[S] union (fun _ : T => True) F_
  ; local : forall a b c, F_ b a -> F_ c a ->
       a <|[S] union (eq b ↓ eq c) F_
  ; le_left : forall a b c, a <=[S] c -> F_ b c -> F_ b a
  ; le_right :  forall a b c, F_ b a -> b <=[T] c -> F_ c a
  ; ax_right : forall a t t' (j : PreISpace.Ix T t'),
     t <= t' -> F_ t a -> 
     a <|[S] union (eq t ↓ PreISpace.C T t' j) F_
  }.

Arguments t : clear implicits.

Context {FTS : FormTop.t S}.

(** Lemma 2.28 of "Exponentiation of unary topologies over 
    inductively generated formal topologies" *)
Theorem cont : forall F, t F -> Cont.t S T F.
Proof.
intros. constructor; intros.
- apply (here X).
- eapply le_left; eassumption.
- apply local; assumption.
- generalize dependent a. induction X1; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply IHX1. eapply le_right; eassumption.
  + pose proof (ax_right X _ _ _ i l X1) as X2.
    clear X1.
    FormTop.etrans. destruct X2. 
    eapply X0; eassumption.
Qed.

(** I should look at Lemma 2.19 of dexplong.pdf *)
Lemma pos F (H : t F) `{FormTop.tPos S} `{FormTop.gtPos T} : forall (t : T) (s : S),
  F t s -> Pos s -> gPos t.
Proof.
intros.
Admitted.

Existing Instances union_Proper FormTop.Cov_Proper.

Lemma Cov_Sat : forall a U (F : Cont.map S T), 
  a <|[S] union U F ->
  a <|[S] union U (@Cont.Sat S T F).
Proof.
intros. 
eapply (FormTop.Cov_Proper _ _). reflexivity. 
  eapply union_monotone.
  eapply (@Cont.Sat_mono2 S T). eassumption. assumption.
Qed.

Theorem converse : forall F, Cont.t S T F 
  -> t (@Cont.Sat S T F).
Proof.
intros. 
constructor; intros.
- apply Cov_Sat. apply (Cont.here X).
- unfold Cont.Sat in *. 
  apply Cov_Sat. FormTop.ejoin. FormTop.etrans.
  destruct X2. destruct d, d0.
  apply (Cont.local X); eapply (Cont.le_left X). 
  apply l. assumption. apply l0. assumption.
- unfold Cont.Sat in *. 
  eapply FormTop.le_left; eassumption.
- unfold Cont.Sat in *.
  FormTop.etrans.
  assert (b <|[T] eq c).
  eapply FormTop.glle_left. eassumption.
  apply FormTop.glrefl. reflexivity.
  pose proof (Cont.cov X (a := a) (b := b) (eq c)).
  eapply FormTop.monotone. Focus 2. apply X3.
  assumption. assumption.
  apply union_eq.
- unfold Cont.Sat in X1. FormTop.etrans.
  apply Cov_Sat. Cont.ecov.
  apply FormTop.gle_infinity with _ j. assumption.
  intros. apply FormTop.glrefl. assumption.
Qed.

Record pt {F : Subset T} := 
  { pt_here : Inhabited F
  ; pt_local : forall {b c}, F b -> F c -> Inhabited ((eq b ↓ eq c) ∩ F)
  ; pt_le_right : forall {a b}, F a -> a <=[T] b -> F b
  ; pt_cov : forall t t' (j : PreISpace.Ix T t'),
     t <= t' -> F t -> 
     Inhabited (F ∩ (eq t ↓ PreISpace.C T t' j))
  }.

Arguments pt : clear implicits.

Lemma pt_cont F : pt F -> Cont.pt T F.
Proof.
intros H. constructor; intros.
- apply (pt_here H).
- apply (pt_local H); assumption.
- induction X0. 
  + exists a; split; assumption.
  + apply IHX0. eapply (pt_le_right H); eassumption.
  + destruct (pt_cov H _ _ i l X). destruct i0.
    eapply X0; eassumption.
Qed.

Lemma pt_cont_converse F : Cont.pt T F -> pt F.
Proof.
intros H. constructor; intros.
- apply (Cont.pt_here H).
- apply (Cont.pt_local H); assumption.
- pose proof (Cont.pt_cov H X (V := eq b)).
  destruct X1. eapply FormTop.glle_left. eassumption.
  apply FormTop.glrefl. reflexivity.
  destruct i. subst. assumption.
- pose (eq t0 ↓ PreISpace.C T t' j) as V. 
  pose proof (Cont.pt_cov H X0 (V := V)).
  eapply X1.
  apply FormTop.gle_infinity with _ j. eassumption.
  intros.  apply FormTop.glrefl. assumption.
Qed.

End IGCont.

Arguments pt : clear implicits.
Arguments t : clear implicits.


End IGCont.

Module IGLCont.
Section IGLCont.

Context {S : PreSpace.t}.
Context {T : PreISpace.t}.

Context {POS : PreO.t (le S)}
        {POT : PreO.t (le T)}.

Record pt {F : Subset T} := 
  { pt_here : Inhabited F
  ; pt_local : forall {b c}, F b -> F c -> Inhabited ((eq b ↓ eq c) ∩ F)
  ; pt_le_right : forall {a b}, F a -> a <=[T] b -> F b
  ; pt_cov : forall t (i : PreISpace.Ix T t), F t -> 
     Inhabited (F ∩ PreISpace.C T t i)
  }.

Arguments pt : clear implicits.

Lemma localized_pt_impl {F : Subset T}
  {loc : localized T} (ptF : pt F) : IGCont.pt T F.
Proof.
econstructor.
- apply (pt_here ptF).
- intros b c. apply (pt_local ptF).
- intros a b. apply (pt_le_right ptF).
- intros. 
  pose proof (loc t t' X j).
  destruct X1.
  pose proof (pt_cov ptF t x X0).
  destruct X1.
  destruct i0.
  eexists. split. eassumption.
  apply i. assumption.
Qed.

End IGLCont.
End IGLCont.