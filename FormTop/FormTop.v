Require Import Frame Algebra.Sets Morphisms.
Set Asymmetric Patterns.

Require Import Basics.
(** Formal topologies. *)

(** Formal topologies as defined in

    [1]
    Inductively generated formal topologies.
    Thierry Coquand, Giovanni Sambin, Jan Smith, Silvio Valentini.
    2000.
    http://www.math.unipd.it/~silvio/papers/WorkInProg/tig000615.pdf

    I highly suggest reading their paper alongside this module!
    I will refer to it as [1].
*)

Definition compose {S T U} (F : S -> T -> Prop)
  (G : T -> U -> Prop) (s : S) (u : U) : Prop :=
    exists t, F s t /\ G t u.

Local Open Scope Ensemble.

Module FormTop.

Generalizable All Variables.


Section Defn.


(** We assume we have some type [S] equipped
    with a partial order. *)
Context {S} {le : S -> S -> Prop} {PO : PreO.t le}.
Context {Cov : S -> Ensemble S -> Prop}.

Infix "<|" := Cov (at level 60) : FT_scope.
Local Infix "<=" := le.

Notation "U <<| V" := (forall a, In U a -> Cov a V) (at level 60) : FT_scope.
Local Open Scope FT_scope.


(** States that [c] is less than or equal to the minimum of
    [a] and [b]. *)
Definition down (a b c : S) : Prop :=
  le c a /\ le c b.

Definition downset (U : Ensemble S) : Ensemble S :=
  union U (flip le).

(** Definition 2.1 of [1].
    Definition of when the [Cov] relation is indeed a formal cover.
    Here, the [Cov] relation means the little triangle that is
    seen in the literature. *)
Class t :=
  { refl : forall (a : S) (U : Ensemble S), In U a -> a <| U
  ; trans : forall (a : S) (U V : Ensemble S), 
       a <| U 
     -> U <<| V
     -> a <| V
  ; le_left : forall (a b : S) (U : Ensemble S)
     , a <= b -> b <| U -> a <| U
  ; le_right : forall (a : S) (U V : Ensemble S)
    , a <| U -> a <| V
    -> a <| downset U ∩ downset V
  }.

Arguments t : clear implicits.

(** Definition of a formal cover that also has a positivity predicate. *)
Record tPos {Pos : S -> Prop} :=
  { cov :> t
  ; mono : forall a U, Pos a -> a <| U -> Inhabited (U ∩ Pos)
  ; positive : forall a U, (Pos a -> a <| U) -> a <| U
  }.

Arguments tPos : clear implicits.

Definition stable :=
  forall a b U V, a <| U -> b <| V
  -> forall c, c <= a -> c <= b ->
    c <| downset U ∩ downset V.

Context `{H : t}.

Lemma monotone : forall (U V : S -> Prop)
  , U ⊆ V -> forall a : S, a <| U -> a <| V.
Proof.
intros. eapply trans. eassumption. intros. apply refl.
apply H0. assumption.
Qed.

Lemma subset_equiv : forall (U V : S -> Prop), U === V
  -> forall a, a <| U <-> a <| V.
Proof.
intros. split; apply monotone; firstorder.
Qed.

End Defn.

Arguments t {S} le Cov : clear implicits.
Arguments down {S} le a b c : clear implicits.
Arguments downset {S} le U _ : clear implicits.
Arguments stable {S} le Cov : clear implicits.

Section IGDefn.

Context {S} {le : S -> S -> Prop}.
Hypothesis PO : PreO.t le.

(** Inductively generated formal topologies. See section
    3 of [1]. *)

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (S -> Prop).

(** Given the axiom set [I] and [C], this generates the
    formal cover corresponding to that axiom set. *)
Inductive GCov : S -> (S -> Prop) -> Prop :=
  | grefl : forall (a : S) (U : S -> Prop), U a -> GCov a U
  | gle_left : forall (a b : S) (U : S -> Prop)
     , le a b -> GCov b U -> GCov a U
  | ginfinity : forall (a : S) (i : I a) (U : S -> Prop),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Inductive GCovL : S -> (S -> Prop) -> Prop :=
  | glrefl : forall (a : S) (U : S -> Prop), U a -> GCovL a U
  | glle_left : forall (a b : S) (U : S -> Prop)
    , le a b -> GCovL b U -> GCovL a U
  | gle_infinity : forall (a b : S) (i : I b) (U : S -> Prop)
    , le a b -> (forall u, (exists u', C b i u' /\ down le a u' u) -> GCovL u U)
    -> GCovL a U.

Lemma Lmore : forall a U, GCov a U -> GCovL a U.
Proof.
intros. induction H.
- apply glrefl. assumption.
- apply glle_left with b; assumption.
- apply (gle_infinity a a i _ (PreO.le_refl _)).
  intros. destruct H1 as (u' & Caiu' & (ua & uu')).
  apply glle_left with u'. assumption. apply H0.
  assumption.
Qed.

Lemma gmonotone : forall (a : S) (U V : S -> Prop),
  U ⊆ V -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gle_left. eassumption. apply IHGCov.
  assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gmonotoneL : forall a (U V : S -> Prop),
  U ⊆ V -> GCovL a U -> GCovL a V.
Proof.
intros. induction H0.
- apply glrefl. apply H. assumption.
- eapply glle_left. eassumption. apply IHGCovL. assumption.
- eapply gle_infinity. eassumption. intros. apply H2.
  apply H3. apply H.
Qed.

Lemma gsubset_equiv : forall (U V : S -> Prop), U === V
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
Qed.

Definition localized := forall (a c : S),
  le a c -> forall (i : I c),
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ down le a u s).

Hypothesis loc : localized. 

(** Proposition 3.5 of [1] *)
Lemma le_infinity : forall (a c : S), le a c ->
  forall (i : I c) (U : S -> Prop), 
  (forall u v, C c i v -> down le a v u -> GCov u U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros. destruct (loc a c H i).
apply (ginfinity _ x).
intros.
specialize (H1 u H2).
destruct H1. destruct H1.
eapply H0; eassumption.
Qed.

Lemma GCov_stable : stable le GCov.
Proof.
unfold localized in loc.
unfold stable. intros. generalize dependent c.
induction H.
- induction H0; intros.
  + apply grefl. constructor; econstructor; eassumption.
  + apply IHGCov. apply H2. 
    eapply PreO.le_trans; eassumption.
  + pose proof (loc c a0 H3 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ j).

    intros. specialize (loc' u H4).
    destruct loc'. destruct H5. destruct H6.
    eapply H1. eassumption.
    eapply PreO.le_trans. apply H6. assumption.
    assumption.
- intros. 
  apply IHGCov. eapply PreO.le_trans. apply H2. apply H. 
  apply H3.
- intros. pose proof (loc c a H2 i) as loc1.
  destruct loc1 as [j loc'].
  apply (ginfinity _ j).

  intros. specialize (loc' u H4).
  destruct loc'. destruct H5. destruct H6.
  eapply H1. eassumption. assumption.
  eapply PreO.le_trans. apply H6. assumption.
Qed.

(** Theorem 3.6 of [1].
    In fact, the formal cover that we defined based on the axiom set 
    indeed satistifes the requirements of being a formal topology. *)
Instance GCov_formtop : t le GCov.
Proof.
unfold localized in loc.
constructor.
- apply grefl.
- intros. induction H.
  + apply H0. assumption.
  + eapply gle_left. apply H. apply IHGCov.
    apply H0.
  + apply (ginfinity _ i). intros. apply H1; assumption.
- apply gle_left.
- intros.
  pose proof GCov_stable as stab.
  unfold stable in stab.
  eapply GCov_stable. eassumption. eassumption.
  apply PreO.le_refl. apply PreO.le_refl.
Qed.


End IGDefn.

Arguments localized {S} le {I} C : clear implicits.
Arguments GCov {S} le {I} C _ _ : clear implicits.
Arguments GCovL {S} le {I} C _ _ : clear implicits.

Require Import Morphisms RelationClasses Basics.
Instance t_proper {S : Type} : 
  Proper ((eq ==> eq ==> iff) ==> (eq ==> eq ==> iff) ==> iff) (@t S).
Proof.
Admitted.


Section Localize.

Context {S : Type} {le : S -> S -> Prop}.
Context {PO : PreO.t le}.
Context {Ix : S -> Type}.
Variable (C : forall s, Ix s -> (S -> Prop)).

Definition IxL (a : S) := 
  { i : sigT Ix | match i with
    | existT c _ => le a c end }.

Definition CL (a : S) : IxL a -> S -> Prop := 
  fun i => match i with
  | exist (existT c k) _ => fun z => exists u, C c k u /\ down le a u z
  end.

Theorem Llocalized : localized le CL.
Proof.
unfold localized.
intros. destruct i. simpl in *. destruct x.
exists (exist (fun i' => match i' with existT c k => le a c end) 
  (existT _ x i) (PreO.le_trans _ _ _ H y)).
simpl. intros.
destruct H0 as (u & Cxiu & downaus).
exists s. split. exists u. split. assumption. unfold down in *.
  destruct downaus.
  split. eapply PreO.le_trans. apply H0. apply H.
  assumption.
  unfold down in *. destruct downaus.
  split; [assumption | apply PreO.le_refl].
Qed.

Theorem cov_equiv : forall a U,
  GCovL le C a U <-> GCov le CL a U.
Proof.
intros. split; intros.
- induction H.
  + apply grefl. assumption.
  + apply gle_left with b; assumption.
  + pose (exist (fun j : sigT Ix => match j with existT c _ => le a c end)
       (existT Ix b i) H : IxL a).
  apply ginfinity with i0.
  intros. apply H1.
  unfold CL in H2.
  simpl in H2. destruct H2 as (u' & Caiu' & (ua & uu')).
  exists u'. split. assumption. split; eassumption.
- induction H.
  + apply glrefl. assumption.
  + apply glle_left with b; assumption.
  + destruct i as ((c & i) & ac).
    simpl in *.
    apply (gle_infinity _ _ a c i). assumption.
    intros. apply H0. apply H1.
Qed.

End Localize.

Section ToFrame.
Context {S : Type}.
Variable (le : S -> S -> Prop) (Cov : S -> Ensemble S -> Prop).

Definition Sat (U : Ensemble S) : Ensemble S :=
  fun s => Cov s U.

Definition leA (U V : Ensemble S) : Prop := Included (Sat U) (Sat V).

Definition eqA (U V : S -> Prop) : Prop := Same_set (Sat U) (Sat V).

Definition minA (U V : Ensemble S) : Ensemble S :=
  downset le U ∩ downset le V.

Inductive supA I (f : I -> Ensemble S) : Ensemble S := 
  MksupA : forall i s, f i s -> In (supA I f) s.

Definition LOps : Lattice.Ops (S -> Prop) :=
  {| Lattice.le := leA
  ;  Lattice.eq := eqA
  ;  Lattice.max := Union
  ;  Lattice.min := minA
  |}.

Instance LOps' : Lattice.Ops (Ensemble S) := LOps.

Definition FOps : Frame.Ops (Ensemble S) := 
  {| Frame.LOps := LOps
   ; Frame.sup := supA
  |}.

Instance FOps' : Frame.Ops (Ensemble S) := FOps.

Hypothesis PO : PreO.t le.
Hypothesis tS : t le Cov. 

Theorem FramePreO : @PreO.t (Ensemble S) leA.
Proof.
constructor; unfold leA; intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Theorem FramePO : @PO.t (Ensemble S) leA eqA.
Proof.
constructor; unfold eqA; intros.
- apply FramePreO.
- unfold leA. unfold Proper, respectful. 
  intros. rewrite H, H0. reflexivity.
- unfold leA in *. constructor; auto.
Qed.

Instance Cov_Proper  :
  Proper (le --> Included ==> impl) Cov.
Proof.
unfold Proper, respectful, impl. intros.
unfold flip in *. 
eapply le_left; try eassumption. 
eapply (monotone _); eassumption.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iff) Cov.
Proof.
unfold Proper, respectful. intros. subst.
destruct H0. split; intros. rewrite <- H. assumption.
rewrite <- H0. assumption.
Qed.

Theorem Sat_Intersection : forall U V,
  Sat (U ∩ V) ⊆ Sat U ∩ Sat V.
Proof.
intros. constructor; unfold Sat, In in *.
  rewrite <- Intersection_Included_l; eassumption.
  rewrite <- Intersection_Included_r; eassumption.
Qed.

Theorem Sat_Union : forall U V,
  Sat U ∪ Sat V ⊆ Sat (U ∪ V).
Proof.
intros. unfold Included; intros. 
destruct H; unfold In, Sat in *. 
rewrite <- Union_Included_l. assumption. 
rewrite <- Union_Included_r. assumption. 
Qed.

Theorem Sat_mono : forall U, U ⊆ Sat U.
Proof.
intros. unfold Included. intros; unfold Sat, In; apply refl.
assumption.
Qed.

Theorem Sat_mono2 : forall U V, U ⊆ V -> Sat U ⊆ Sat V.
Proof.
intros. unfold Included, In, Sat. 
intros. rewrite <- H. assumption.
Qed.

Theorem Cov_Sat : forall a U, Cov a U <-> Cov a (Sat U).
Proof.
intros. split; intros. rewrite <- Sat_mono. assumption.
eapply trans. eassumption. intros. apply H0.
Qed.

Theorem Sat_downset : forall U, Sat U === Sat (downset le U).
Proof.
intros. split.
- apply Sat_mono2. unfold Included, In, downset.
  intros. econstructor. eassumption. reflexivity.
- unfold Included, Sat, In, downset.
  intros. eapply trans. eassumption. intros.
  destruct H0. unfold flip in H1. rewrite H1. apply refl. assumption.
Qed.

Theorem FrameLatt : Lattice.t (Ensemble S) LOps.
Proof.
constructor; intros.
- apply FramePO.
- simpl. unfold Proper, respectful, eqA. intros.
  destruct H, H0.
  split; unfold Included, In, Sat; intros.
  + apply Cov_Sat. rewrite <- Sat_Union.
    rewrite <- H, <- H0.
    rewrite <- !Sat_mono. assumption.
  + apply Cov_Sat. rewrite <- Sat_Union. 
    rewrite <- H1, <- H2. rewrite <- !Sat_mono. assumption. 
- constructor.
  + simpl. unfold leA. apply Sat_mono2. 
    apply Union_Included_l.
  + simpl. unfold leA. apply Sat_mono2.
    apply Union_Included_r.
  + simpl. unfold leA. intros.
    unfold Sat, Included, In. intros.
    apply trans with (l ∪ r). assumption. 
    intros. rewrite Cov_Sat. destruct H2.
    * rewrite <- H, <- Cov_Sat. apply refl. assumption.
    * rewrite <- H0, <- Cov_Sat. apply refl. assumption.
- simpl. unfold Proper, respectful, eqA, minA. intros.
  split; intros.
  + rewrite Sat_Intersection. rewrite <- !Sat_downset.
    rewrite H, H0. unfold Included; intros.
    destruct H1. unfold Sat, In in *.
    apply le_right; assumption.
  + rewrite Sat_Intersection. rewrite <- !Sat_downset. 
    rewrite <- H, <- H0. unfold Included; intros. 
    destruct H1. unfold Sat, In in *. 
    apply le_right; assumption.
- simpl. constructor; unfold leA, minA; intros.
  + unfold Sat, Included, In; intros. 
    eapply trans. eassumption.
    intros. destruct H0. destruct H0.
    unfold flip in H2. rewrite H2. apply refl. apply H0.
  + unfold Sat, Included, In; intros. 
    eapply trans. eassumption. intros. 
    destruct H0. destruct H1. unfold flip in H2. 
    rewrite H2. apply refl. assumption.
  + unfold Sat, Included, In; intros. eapply trans. eassumption. 
    intros.
    apply le_right. rewrite Cov_Sat, <- H, <- Cov_Sat.
    apply refl. assumption.
    rewrite Cov_Sat, <- H0, <- Cov_Sat. apply refl.  assumption.
Qed.

Theorem Frame : Frame.t (Ensemble S) FOps.
Proof.
constructor; intros.
- apply FrameLatt.
- simpl. unfold eqA, pointwise_relation. 
  unfold Proper, respectful. intros.
  split; intros.
  + unfold Included, Sat, In; intros.
    eapply trans. eassumption.
    intros. destruct H1.
    apply trans with (y i).
    rewrite Cov_Sat, <- (H i), <- Cov_Sat. 
    apply refl. assumption. specialize (H i).
    intros. apply refl. econstructor. apply H2. 
  + unfold Included, Sat, In; intros.
    eapply trans. eassumption.
    intros. destruct H1.
    apply trans with (x i).
    rewrite Cov_Sat, (H i), <- Cov_Sat.
    apply refl. assumption. intros.
    apply refl. econstructor; apply H2.
- simpl. constructor; unfold leA; intros.
  + apply Sat_mono2. unfold Included, In; intros. 
    econstructor; eassumption. 
  + unfold Included, In, Sat; intros.
    eapply trans. eassumption.
    intros. destruct H1. 
    rewrite Cov_Sat, <- (H i), <- Cov_Sat.
    apply refl. assumption.
- simpl. unfold minA, eqA.
  split; apply Sat_mono2.
  + unfold Included. intros. destruct H.
    destruct H0. destruct H0.
    repeat (econstructor; try eassumption).
  + unfold Included. intros. destruct H.
    destruct H. constructor. assumption.
    destruct H0. repeat (econstructor; try eassumption).
Qed. 

End ToFrame.

End FormTop.

Module Subspace.

Section Defn.
Context {S : Type} {leS : S -> Ensemble S}.
Hypothesis POS : PreO.t leS.
Variable CovS : S -> (Ensemble S) -> Prop.

Definition Cov (V : Ensemble S) (a : S)
  (U : Ensemble S) : Prop := CovS a (V ∪ U).


Context {FTS : FormTop.t leS CovS}.

Instance Cov_Proper : Proper (leS --> Included ==> Basics.impl) CovS := 
  FormTop.Cov_Proper _ _ _.

Theorem t (V : Ensemble S) : FormTop.t leS (Cov V).
Proof.
constructor; unfold Cov; intros.
- apply FormTop.refl. right. assumption.
- eapply FormTop.trans. apply H. clear H. simpl. intros.
  destruct H. apply FormTop.refl. left. assumption.
  apply H0. assumption.
- apply FormTop.le_left with b; assumption.
- pose proof (FormTop.le_right a _ _ H H0). 
  eapply FormTop.trans. apply H1.
  clear H1. simpl. intros.
  destruct H1. destruct H1, H2.
  destruct H1. unfold flip in H3. rewrite H3. 
  apply FormTop.refl. left. assumption. 
  destruct H2. unfold flip in H4. rewrite H4.
  apply FormTop.refl. left. assumption. 
  rewrite <- Union_Included_r.
  apply FormTop.le_right.
  unfold flip in H3. rewrite H3. apply FormTop.refl. assumption.
  unfold flip in H4. rewrite H4. apply FormTop.refl. assumption.
Qed.

End Defn.

Arguments Cov {S} CovS V a U : clear implicits.

Section IGDefn.
Context {S} {leS : S -> Ensemble S}.
Hypothesis POS : PreO.t leS.
Context {Ix : S -> Type}.
Variable C : forall a, Ix a -> (Ensemble S).

Variable V : Ensemble S. 

Definition SIx (a : S) : Type :=
  (Ix a + { I : True | V a })%type.

Definition SC (a : S) (i : SIx a) : Ensemble S := 
  match i with
  | inl i' => C a i'
  | inr _ => fun _ => False
  end.

Theorem same : forall a U,
  FormTop.GCovL leS SC a U <-> Cov (FormTop.GCovL leS C) V a U.
Proof.
intros. unfold Cov. split; intros.
- induction H.
  + apply FormTop.glrefl. right. assumption.
  + apply FormTop.glle_left with b. assumption.
    assumption.
  + destruct i.
    * apply (FormTop.gle_infinity _ _ a b i).
      assumption. intros. apply H1. simpl. apply H2.
    * destruct s. apply FormTop.glle_left with b. assumption.
      apply FormTop.glrefl. left. assumption.
- remember (V ∪ U) as U' in H. induction H; subst.
  + destruct H.
    * eapply FormTop.gmonotoneL. Focus 2.
    pose proof (FormTop.gle_infinity SIx SC x x (inr (exist (fun _ => V x) I H)) (fun _ => False) 
       (PreO.le_refl _)).
    apply H0. intros. simpl in *.
    destruct H1 as (u' & bot & downau). contradiction. simpl.
    intros. unfold Included, In; intros; contradiction.
    * apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b. assumption. apply IHGCovL.
    reflexivity.
  + apply (FormTop.gle_infinity SIx SC a b (inl i)).
    assumption. intros.
    apply H1. apply H2. reflexivity.
Qed.

End IGDefn.

End Subspace.


(** Information bases, which are the predicative versions of
    Scott domains. Perhaps, see Definition 1.9 of [2].
    Though my formulation is a little different; I build off
    of a pre-existing notion of a meet semi-lattice.

    Also, I directly show that this formal topology is
    inductively generated by generating it with an axiom set. *)
Module InfoBase. 
Section InfoBase.

Generalizable All Variables.

Context {S : Type} `{PO : PO.t S leS eqS}.

(** The axiom set essentially says that if [s <= t], then
    [s] is covered by the singleton set [{t}]. *)
Definition Ix (s : S) : Type := { t : S & leS s t }.
Definition C (s : S) (s' : Ix s) s'' : Prop := eqS (projT1 s') s''.

(** This axiom set is localized. *)
Definition loc : FormTop.localized leS C.
Proof.
pose proof (@PO.t_equiv _ _ _ PO) as eqEquiv.
unfold FormTop.localized. intros. simpl.
unfold Ix, C in *.
destruct i. simpl.
assert (leS a a).
apply PreO.le_refl.
exists (existT _ a H0).
intros.  simpl in *. 
exists x. split. reflexivity.
split. 
rewrite H1. apply PreO.le_refl.
rewrite <- H1.
eapply PreO.le_trans. eapply H. eassumption.
Qed.

Definition Cov (s : S) (U : Ensemble S) : Prop :=
  In (FormTop.downset leS U) s.

(** The covering relation for information bases,
    which we derive from the axiom set above. *)
Definition GCov := @FormTop.GCov _ leS Ix C.

Require Import Morphisms SetoidClass.
Theorem CovEquiv : forall s U, Cov s U <-> GCov s U.
Proof.
intros. unfold Cov, GCov. split; intros.
- destruct H as [t Ut st].
  apply FormTop.ginfinity with (existT _ t st).
  unfold C. simpl. intros.
  apply FormTop.gle_left with t.
  rewrite H. apply PreO.le_refl.
  apply FormTop.grefl. assumption.
- induction H. 
  + exists a. assumption. unfold flip. apply PreO.le_refl.
  + destruct IHGCov as [t Ut bt].
    exists t. assumption. unfold flip. eapply PreO.le_trans; eassumption.
  + destruct i. unfold C in *. simpl in *.
    assert (eqS x x) as eqx. reflexivity.
    specialize (H x eqx).
    specialize (H0 x eqx). destruct H0 as [t Ut xt].
    exists t. assumption. unfold flip in *. eapply PreO.le_trans; eassumption.
Qed.

(** The proof that [Cov] is a valid formal topology. *)
Instance isCovG : FormTop.t leS GCov := 
  FormTop.GCov_formtop _ Ix C loc.

Require Import Morphisms.
Instance isCov : FormTop.t leS Cov.
Proof.
assert ((eq ==> eq ==> iff)%signature Cov GCov).
pose proof CovEquiv.
simpl_relation. rewrite H. apply isCovG.
Qed.

End InfoBase.
End InfoBase.

(** A definition of concrete topological spaces. These are formal topologies
    which are related to a type of points in the expected way, through a
    relation which I call [In]. See Definition 1.2 in [1]. Their relation
    which I call [In] looks like [||-], and they read as "lies in" or
    "forces".
*)
Module Concrete. 
Section Concrete.

Variable X S : Type.
Variable In : X -> Ensemble S.

Definition le := (map_op (fun (s : S) (x : X) => In x s)
            (pointwise_op (fun (_ : X) (P Q : Prop) => P -> Q))).

Instance SPO : @PO.t S le _ := PO.map (fun s x => In x s) (PO.subset X).

Instance SubsetFrameOps : Frame.Ops (X -> Prop) := Frame.subset_ops X.

Record t : Type :=
  { here : forall x, { s | In x s }
  ; local : forall (a b : S) x, In x a -> In x b 
          -> { c | In x c /\ FormTop.down (map_op (fun s x => In x s) L.le) a b c }
  }.

(** Every concrete topological space can be presented as an
    inductively generated formal topology. See Section 4.4
    of [1]. *)
Definition Ix (a : S) : Type := sig (fun (g : forall (x : X), In x a -> S) 
  => forall (x : X) (prf : In x a), In x (g x prf)).

Definition C (a : S) (i : Ix a) : Ensemble S := match i with
  | exist g _ => fun s => exists (x : X) (prf : In x a), s = g x prf
  end.

Theorem loc : t -> FormTop.localized (map_op (fun s x => In x s) L.le) C.
Proof.
intros conc. destruct conc.
unfold FormTop.localized. simpl.
intros. unfold Ix in *. destruct i as [g Pg].
assert (forall x prf, In x (g x (H x prf))) as Pg'.
intros. apply Pg.
pose (fun x xina => local0 a (g x (H x xina)) x xina
  (Pg' x xina)) as g'.
assert (forall x prf, In x (proj1_sig (g' x prf))) as Pg''.
intros. destruct (g' x prf).
simpl. destruct a0. assumption.
exists (exist _ (fun x prf => proj1_sig (g' x prf)) Pg''). 

unfold C. intros.
destruct H0 as [x [prf img]].
exists (g x (H x prf)). split. exists x. exists (H x prf).
reflexivity.
destruct (g' x prf). simpl in *. destruct a0. subst.
assumption. 
Qed.

End Concrete.
End Concrete.

(** An inductively generated formal topology for the Cantor space.
    See Section 4.1 of [1]. *)
Module Cantor.

Variable A : Type.

Definition S := list A.

Definition Ix (s : S) := True.

Require Import Coq.Lists.List.

Definition C (s : S) (_ : True) (s' : S) : Prop := exists b,
  s' = s ++ (b :: nil).

Definition LE {A} (xs ys : list A) : Prop := exists zs,
  xs = ys ++ zs.

Lemma LE_PO {A : Type} : @PO.t (list A) LE eq.
Proof.
constructor; intros.
- constructor; unfold LE; intros.
  + exists nil. rewrite app_nil_r. reflexivity.
  + destruct H. destruct H0.
    exists (x1 ++ x0). rewrite H. rewrite H0.
    rewrite app_assoc. reflexivity.
- unfold Morphisms.Proper, Morphisms.respectful. 
  unfold LE in *. intros. subst. reflexivity. 
- unfold LE in *.  destruct H. destruct H0.
  rewrite H0 in H. rewrite <- app_assoc in H.
  rewrite <- app_nil_r in H at 1.
  apply app_inv_head in H.
  symmetry in H. apply app_eq_nil in H.
  destruct H.  subst. rewrite app_nil_r.
  reflexivity.
Defined.

Definition Cov := FormTop.GCov LE C.

Theorem loc : FormTop.localized LE C.
Proof.
unfold FormTop.localized.
intros.  unfold Ix in *. destruct i. exists I.
intros. unfold C in *. destruct H0.
simpl in H.
unfold LE in H. destruct H.
destruct x0.
- subst.
  exists (c ++ x :: nil). split. exists x. reflexivity.
  unfold FormTop.down. split; simpl; unfold LE.
  exists (x :: nil). reflexivity.
  exists nil. repeat rewrite app_nil_r. reflexivity.
- exists (c ++ a0 :: nil). split. exists a0. reflexivity.
  unfold FormTop.down. split; simpl; unfold LE.
  exists (x :: nil). assumption. exists (x0 ++ x :: nil).
  rewrite <- app_assoc. simpl.
  rewrite H0. rewrite H. rewrite <- app_assoc. reflexivity.
Qed.

End Cantor.

(** Product spaces for inductively generated formal topologies.
    See Section 4.3 of [1]. *)
Module Product.

Generalizable All Variables.
Section Product.

Variable S T : Type.
Context `{POS : PreO.t S leS}. 
Context `{POT : PreO.t T leT}.
Variable IS : S -> Type.
Variable IT : T -> Type.
Variable CS : forall s, IS s -> (Ensemble S).
Variable CT : forall t, IT t -> (T -> Prop).

Definition Ix (p : S * T) : Type := match p with
  (s, t) => (IS s * T + S * IT t)%type end.

Definition C (p : S * T) : Ix p -> S * T -> Prop
  := match p as p' return Ix p' -> S * T -> Prop with (a, b) =>
  fun pI open => let (z, w) := open in match pI with
    | inl (sI, t) => CS a sI z /\ w = b
    | inr (s, tI) => z = a /\ CT b tI w
    end
  end.

Definition PO := PreO.product POS POT.

Theorem loc : 
    FormTop.localized leS CS
  -> FormTop.localized leT CT
  -> FormTop.localized (prod_op leS leT) C.
Proof.
intros. unfold FormTop.localized in *.
intros. destruct a as [sa ta], c as [sc tc]. 
destruct H1.
simpl in H1, H2, i.
destruct i as [[sI t]|[s tI]].
- specialize (H sa sc H1 sI).
  destruct H. unfold Ix in *.
  exists (inl (x, t)).
  intros. destruct s as [su tu].
  simpl in H3. destruct H3.
  specialize (H _ H3).
  destruct H as [u [CSu downu]].
  simpl. exists (u, tc). split. split. assumption. reflexivity.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. assumption. apply PreO.le_refl.
  simpl. split. assumption. assumption.
- specialize (H0 ta tc H2 tI).
  destruct H0. unfold Ix in *.
  exists (inr (s, x)).
  intros. destruct s0 as [su tu].
  simpl in H3. destruct H3.
  specialize (H0 _ H4).
  destruct H0 as [u [CTu downu]].
  simpl. exists (sc, u). split. split. reflexivity. assumption.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. apply PreO.le_refl. assumption.
  simpl. red. eauto. 
Qed.

Definition Cov := FormTop.GCov (prod_op leS leT) C.

Hypothesis locS : FormTop.localized leS CS.
Hypothesis locT : FormTop.localized leT CT.

Theorem isCov : FormTop.t (prod_op leS leT) Cov.
Proof.
apply (@FormTop.GCov_formtop (S * T) (prod_op leS leT)
  PO Ix C (loc locS locT)).
Qed.

Let CovS := FormTop.GCov leS CS.
Let CovT := FormTop.GCov leT CT.

Lemma factors : forall a b U V, CovS a U -> CovT b V -> 
  Cov (a, b) (fun p => let (a', b') := p in U a' /\ V b').
Proof.
intros. induction H.
- induction H0.
  + apply FormTop.grefl. split; assumption.
  + eapply FormTop.gle_left. 2:apply IHGCov.
    split; simpl. apply PreO.le_refl. assumption.
  + apply FormTop.ginfinity with (inr (a, i)).
    intros. simpl in H2. destruct u. destruct H2. 
    subst. apply H1. assumption.
- apply FormTop.gle_left with (b0, b). split; simpl.
  assumption. apply PreO.le_refl.
  apply IHGCov.
- apply FormTop.ginfinity with (inl (i, b)).
  intros. simpl in H2. destruct u. destruct H2. 
  subst. apply H1. assumption.
Qed.

Lemma unfactors1 : forall ab U, Cov ab U
  -> CovS (fst ab) (fun s => exists b', U (s, b')).
Proof.
intros. induction H.
- apply FormTop.grefl. destruct a. exists t. assumption.
- destruct a, b, H. simpl in *. 
  apply FormTop.gle_left with s0. assumption.
  assumption.
- destruct a. destruct i.
  + destruct p. apply FormTop.ginfinity with i.
    intros. apply (H0 (u, t)). simpl. simpl in H1.
    intuition.
  + destruct p. simpl.

pose proof locS. pose proof locT.
Admitted.

Lemma unfactors2 : forall ab U, Cov ab U
  -> CovT (snd ab) (fun t' => exists a', U (a', t')).
Proof.
intros. induction H.
- apply FormTop.grefl. destruct a. exists s. assumption.
- destruct a, b, H. simpl in *. 
  apply FormTop.gle_left with t0. assumption.
  assumption.
- destruct a. destruct i.
  + destruct p. simpl. 
    pose proof locS. pose proof locT.
    admit.
  + destruct p. apply FormTop.ginfinity with i.
    intros. apply (H0 (s, u)). simpl. simpl in H1.
    intuition.
Admitted.


End Product.
End Product.

(** Continuous maps. *)
Module Cont.
Generalizable All Variables.

Section Cont.

Context {S} `{POS : PreO.t S leS}.
Context {T} `{POT : PreO.t T leT}.

Context {CovS : S -> (Ensemble S) -> Prop}.
Context {CovT : T -> Ensemble T -> Prop}.

Record t {F : S -> T -> Prop} : Prop :=
  { here : forall a, CovS a (fun s => Inhabited (F s))
  ; le_left : forall a b c, leS a c -> F c b -> F a b
  ; local : forall {a b c}, F a b -> F a c
    -> CovS a (fun s => exists bc, FormTop.down leT b c bc /\ F s bc)
  ; cov : forall {a b} V, F a b -> CovT b V
    -> CovS a (union V (fun t s => F s t))
  }.

Arguments t F : clear implicits.

Record pt {F : T -> Prop} :=
  { pt_here : exists t, F t
  ; pt_local : forall {b c}, F b -> F c -> exists d, FormTop.down leT b c d /\ F d
  ; pt_cov : forall {b V}, F b -> CovT b V -> Inhabited (F ∩ V)
  }.

Arguments pt F : clear implicits.

(** Convert a continuous map for formal topologies to a 
    frame homomorphism (i.e., continuous map on locales)
  *)
Definition frame (F : S -> T -> Prop) (U : Ensemble T) : Ensemble S :=
  union U (fun t s => F s t).

Hypothesis FTS : FormTop.t leS CovS. 
Hypothesis FTT : FormTop.t leT CovT.


Let FrameS := FormTop.Frame leS CovS POS FTS.
Let FrameT := FormTop.Frame leT CovT POT FTT.

Variable F : S -> T -> Prop.
Hypothesis cont : t F.

Instance POFS : @PO.t (Ensemble S) (FormTop.leA CovS) (FormTop.eqA CovS).
Proof.
eapply FormTop.FramePO.
Qed.

Instance POFT : @PO.t (T -> Prop) (FormTop.leA CovT) (FormTop.eqA CovT).
Proof.
eapply FormTop.FramePO.
Qed.

Theorem monotone : PreO.morph (FormTop.leA CovT) (FormTop.leA CovS)
   (frame F).
Proof.
unfold PreO.morph. intros. unfold frame.
simpl. unfold FormTop.leA, FormTop.Sat.
unfold Included, In.
intros. simpl in H. unfold FormTop.leA, FormTop.Sat in H.
apply (FormTop.trans _ _ _ H0). intros.
destruct H1 as [t' at' Fa't'].
apply (cov cont _ Fa't'). apply H. unfold In. apply FormTop.refl.
assumption.
Qed.

Require Import Morphisms SetoidClass.

Instance Cov_Proper : Proper (leS --> Included ==> impl) CovS.
Proof.
 apply FormTop.Cov_Proper. assumption.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iff) CovS.
Proof.
 eapply FormTop.Cov_Proper2; eassumption.
Qed.

Theorem Sat_Proper : forall A `{PreO.t A leA} (Cov : A -> Ensemble A -> Prop)
  `{FormTop.t _ leA Cov},
  Proper (Same_set ==> Same_set) (FormTop.Sat Cov).
Proof.
intros. unfold Proper, respectful. intros. unfold FormTop.Sat.
apply Same_set_iff. intros. apply FormTop.subset_equiv.
assumption.
Qed.


Theorem toLattice : 
   L.morph (FormTop.LOps leT CovT) (FormTop.LOps leS CovS) (frame F).
Proof.
constructor.
  + constructor.
     * apply monotone.
     * repeat intro. split; apply monotone; simpl in H;
       rewrite H; apply PreO.le_refl.
  + intros. unfold frame. simpl. unfold FormTop.eqA.
    eapply Sat_Proper; try eassumption.
    symmetry. apply Union_union.
  + intros. unfold frame. simpl. apply PO.le_antisym;
    unfold FormTop.leA, FormTop.Sat, Included, In; intros.
    * apply (FormTop.trans _ _ _ H). clear x H.
      intros. unfold FormTop.minA in H.
      destruct H. destruct H. destruct H, H1.
      unfold flip in *. 
      unfold FormTop.minA.
      apply FormTop.le_right;
      apply (cov cont _ H0).
      apply FormTop.le_left with a1. assumption.
      apply FormTop.refl. assumption.
      apply FormTop.le_left with a2. assumption.
      apply FormTop.refl. assumption.
    * apply (FormTop.trans _ _ _ H). clear x H.
      intros. unfold FormTop.minA in *.
      destruct H. destruct H, H0. destruct H, H0.
      unfold flip in *.
      pose proof (le_left cont _ _ _ H1 H3) as Fat1.
      pose proof (le_left cont _ _ _ H2 H4) as Fat2.
      pose proof (local cont Fat1 Fat2).
      refine (FormTop.monotone _ _ _ _ H5).
      unfold Included; intros.
      destruct H6 as (bc & (a0bc & a1bc) & fabc).
      exists bc. split; econstructor; eassumption. assumption.
Qed.

Theorem toFrame : Frame.morph 
  (FormTop.FOps leT CovT) (FormTop.FOps leS CovS) (frame F).
Proof.
constructor.
- apply toLattice.
- unfold frame. simpl. intros.
  unfold FormTop.eqA. eapply Sat_Proper; try eassumption.
  intros; split; unfold Included, In; intros.
  + destruct H. destruct H. repeat econstructor; eauto.
  + destruct H. destruct H. repeat econstructor; eauto. 
- unfold frame. simpl. unfold FormTop.eqA, FormTop.Sat.
  intros. split; unfold Included, In; intros.
  + apply FormTop.refl. exists (fun _ => True). constructor.
  + pose proof (here cont x).
    eapply FormTop.trans. apply H0. clear H0. intros. 
    destruct H0. apply FormTop.refl. 
    repeat (econstructor; try eassumption).
Qed.

Definition toCmap : Frame.cmap (FormTop.FOps leS CovS)
  (FormTop.FOps leT CovT) :=
  {| Frame.finv := frame F
   ; Frame.cont := toFrame |}.


End Cont.

Arguments t {S} leS {T} leT CovS CovT F : clear implicits.
Arguments pt {T} leT CovT F : clear implicits.

Section Morph.

Context {S} `{POS : PreO.t S leS}.
Context `{FTS : FormTop.t S leS CovS}.

Definition id (s t : S) := leS s t.

Theorem t_id : t leS leS CovS CovS id.
Proof.
constructor; intros; unfold id in *.
- eapply FormTop.refl. exists a. unfold In. reflexivity.
- eapply PreO.le_trans; eassumption.
- apply FormTop.refl. exists a. split.
  split; eassumption. apply PreO.le_refl.
- eapply FormTop.trans with (fun b' => b = b').
  eapply FormTop.le_left. eassumption.
  apply FormTop.refl. reflexivity. unfold In.  
  intros. subst. eapply FormTop.monotone.
  2:eassumption. intros. unfold Included, In; intros. 
  exists x. assumption. apply PreO.le_refl.
Qed.

Context {T} `{POT : PreO.t T leT}.
Context {U} `{POU : PreO.t U leU}.
Context `{FTT : FormTop.t T leT CovT}.
Context `{FTU : FormTop.t U leU CovU}.

(*
Everything in s maps to u
iff there is some subset T such that
  everything in s maps to T and
  everything in T maps to u
*)

Theorem t_compose : forall (F : S -> T -> Prop) (G : T -> U -> Prop),
    t leS leT CovS CovT F
  -> t leT leU CovT CovU G
  -> t leS leU CovS CovU (compose F G).
Proof.
intros. constructor; intros.
- pose proof (here H a).
  eapply FormTop.trans. eassumption.
  simpl. intros. destruct H2. 
  pose proof (here H0 x).
  pose proof (cov H _ H2 H3).
  refine (FormTop.monotone _ _ _ _ H4).
  unfold Included, In.
  intros. destruct H5. destruct H5. 
  exists x1. unfold In.  unfold compose. exists a1. split; assumption.
- unfold compose in *.
  intros. 
  destruct H2 as [t1 [Fat1 Gt1b]]. 
  exists t1. split. eapply (le_left H). eassumption.
  assumption. assumption.
- unfold compose in *.
  destruct H1 as [t1 [Fat1 Gt1b]]. 
  destruct H2 as [t2 [Fat2 Gt2b]].
  pose proof (local H Fat1 Fat2).
  eapply FormTop.trans.
  eassumption. simpl. intros.
  destruct H2 as (tt & downtt & Fatt).
  apply (FormTop.monotone)
  with (union (fun t'' => exists bc : U, FormTop.down leU b c bc /\ G t'' bc) (fun t s => F s t)). unfold Included, In; intros. destruct H2. firstorder.
  eapply (cov H). eassumption.
  destruct downtt.
  apply (local H0).
  eapply (le_left H0). eapply H2. eassumption.
  eapply (le_left H0). eapply H3. eassumption.
- unfold compose. intros.
  destruct H1 as [t [Fat Gtb]].
  apply (FormTop.monotone)
    with (union (fun t => exists u, V u /\ G t u) (fun t s => F s t)).
  unfold Included, In; intros. destruct H1. 
  destruct H1.  destruct H1. econstructor. apply H1.
  exists a0; eauto.
  apply (cov H _ Fat).
  apply FormTop.monotone with
     (union V (fun u t => G t u)).
  unfold Included, In; intros. destruct H1. unfold In in *.
  exists a0; eauto.
  apply (cov H0 _ Gtb). assumption.
Qed.

End Morph.

Section Products. 
Context {S} `{POS : PreO.t S leS}.
Context {IS} {CS : forall (s : S), IS s -> (Ensemble S)}.
Variable locS : FormTop.localized leS CS.
Let CovS := FormTop.GCov leS CS.

Definition diagonal (p : S) (out : S * S) : Prop :=
  let (out1, out2) := out in leS p out1 /\ leS p out2.

Lemma t_diagonal : t leS (prod_op leS leS)
  CovS (@Product.Cov _ _ leS leS IS IS CS CS) diagonal.
Proof.
pose proof (FormTop.GCov_formtop _ IS CS locS) as FTS.
constructor; intros; unfold diagonal, CovS in *.
- apply FormTop.refl. exists (a, a). split; apply PreO.le_refl.
- destruct b. destruct H0.
  split; eauto using PreO.le_trans. 
- destruct b, c. destruct H, H0.
  apply FormTop.refl. exists (a, a).
  split. split; unfold prod_op; simpl; split; assumption.
  split; apply PreO.le_refl.
- generalize dependent a. induction H0; intros.
  + apply FormTop.refl. exists a. assumption. assumption. 
  + apply IHGCov. destruct a, b, H. simpl in *. 
    destruct H1. split; eauto using PreO.le_trans.
  + destruct a. simpl in *. destruct H1. destruct i.
    * destruct p. unfold FormTop.localized in locS. 
      specialize (locS a0 s H1 i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (H3 _ H4).
      destruct H3. destruct H3. 
      apply H0 with (x0, s0).
      auto. destruct H5. eauto using PreO.le_trans.
    * destruct p. unfold FormTop.localized in locS. 
      specialize (locS a0 s0 H2 i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (H3 _ H4).
      destruct H3. destruct H3. 
      apply H0 with (s, x0).
      auto. destruct H5. eauto using PreO.le_trans.
Qed.
  

Context {T} `{POT : PreO.t T leT}.
Context {IT} {CT : forall (t : T), IT t -> (T -> Prop)}.
Variable locT : FormTop.localized leT CT.
Let CovT := FormTop.GCov leT CT.

Definition proj_L (p : S * T) (out : S) : Prop :=
  let (s1, t1) := p in leS s1 out.

Lemma t_proj_L : t (prod_op leS leT) leS 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovS proj_L.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_L in *.
- apply FormTop.refl. destruct a. exists s. unfold In. reflexivity.
- destruct c, a.  destruct H. simpl in H, H1. 
  eapply PreO.le_trans; eassumption.
- destruct a. apply FormTop.refl. 
  exists s. split. split; assumption. apply PreO.le_refl. 
- destruct a. generalize dependent s. induction H0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (b, t0).
    split; simpl. eapply PreO.le_trans; eassumption. 
    apply PreO.le_refl.
    apply IHGCov. apply PreO.le_refl.
  + unfold FormTop.localized in locS. 
    specialize (locS _ _ H1 i).
    destruct locS.
    apply FormTop.ginfinity with (inl (x, t0)). 
    intros. simpl in *. destruct u. destruct H3.
    subst.
    specialize (H2 _ H3). destruct H2 as (u & Caiu & downu).
    eapply H0. eassumption.
    destruct downu. assumption.
Qed.

Definition proj_R (p : S * T) (out : T) : Prop :=
  let (s1, t1) := p in leT t1 out.

Lemma t_proj_R : t (prod_op leS leT) leT 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovT proj_R.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_R in *.
- apply FormTop.refl. destruct a. exists t0. unfold In. reflexivity.
- destruct c, a.  destruct H. simpl in H, H1. 
  eauto using PreO.le_trans.
- destruct a. apply FormTop.refl. 
  exists t0. split. split; assumption. apply PreO.le_refl. 
- destruct a. generalize dependent t0. induction H0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (s, b).
    (** We would like
        eauto using (PreO.le_refl, PreO.le_trans)
        to work here, but it is dumb! *)
    split; simpl. apply PreO.le_refl. 
    eapply PreO.le_trans; eassumption. 
    apply IHGCov. apply PreO.le_refl.
  + unfold FormTop.localized in locT. 
    specialize (locT _ _ H1 i).
    destruct locT.
    apply FormTop.ginfinity with (inr (s, x)). 
    intros. simpl in *. destruct u. destruct H3.
    subst.
    specialize (H2 _ H4). destruct H2 as (u & Caiu & downu).
    eapply H0. eassumption.
    destruct downu. assumption.
Qed.

Context {A} `{POA : PreO.t A leA}.
Context {IA} {CA : forall (t : A), IA t -> (A -> Prop)}.
Variable locA : FormTop.localized leA CA.
Let CovA := FormTop.GCov leA CA.

Context {B} `{POB : PreO.t B leB}.
Context {IB} {CB : forall (t : B), IB t -> (B -> Prop)}.
Variable locB : FormTop.localized leB CB.
Let CovB := FormTop.GCov leB CB.

Definition parallel (F : S -> A -> Prop) (G : T -> B -> Prop)
  (p : S * T) (out : A * B) : Prop :=
  let (s, t) := p in let (a, b) := out in
   F s a /\ G t b.

(** Broken
Theorem t_parallel (F : S -> A -> Prop) (G : T -> B -> Prop)
  : t leS leA CovS CovA F
  -> t leT leB CovT CovB G
  -> t (prod_op leS leT) (prod_op leA leB)
      (@Product.Cov _ _ leS leT IS IT CS CT)
      (@Product.Cov _ _ leA leB IA IB CA CB)
      (parallel F G).
Proof.
intros ContF ContG.
constructor; intros; unfold parallel in *.
- apply FormTop.gmonotone with
  (fun s : S * T => let (s', t') := s in 
  (fun s'' => exists a, F s'' a) s' /\ (fun t'' => exists b, G t'' b) t').
  intros. destruct a, a0. 
  destruct H as ((? & ?) & (? & ?)). exists (x, x0).
  intuition. destruct a. apply Product.factors; try assumption.
  apply (here ContF). apply (here ContG).
- destruct c, b, a. destruct H; simpl in *.
  destruct H0. split.
  eapply (le_left ContF); eassumption.
  eapply (le_left ContG); eassumption.
- destruct a, b, c.
  destruct H, H0.
  pose proof (local ContF H H0).
  pose proof (local ContG H1 H2).
Admitted.
*)

End Products.
End Cont.

Arguments Cont.t {S} leS {T} leT CovS CovT F : clear implicits.

Module One.
Section One.

Definition Cov (_ : True) (U : True -> Prop) : Prop := U I.

Require Import Morphisms.
Theorem CovEquiv : (eq ==> eq ==> iff)%signature Cov (@InfoBase.Cov _ (fun _ _ => True)).
Proof.
simpl_relation.
intros. unfold Cov, InfoBase.Cov. split; intros.
- exists I; unfold flip; tauto.
- destruct H as [[] Ut _]. assumption.
Qed.

Instance MLOne : MeetLat.t True MeetLat.one_ops := MeetLat.one.
Instance POOne : @PO.t True (fun _ _ => True) (fun _ _ => True) := @MeetLat.PO _ _ MLOne.

Instance FTOne : FormTop.t (@MeetLat.le _ MeetLat.one_ops) Cov.
Proof.
rewrite CovEquiv.
apply InfoBase.isCov.
Qed.

Instance one_ops : MeetLat.Ops True := MeetLat.one_ops.

Require Import Morphisms.
Definition FTtoFrame : 
  Frame.morph (FormTop.FOps MeetLat.le Cov) Frame.prop_ops (fun U => U I).
Proof.
simpl. unfold Cov.
constructor.
- constructor.
  + constructor. simpl. unfold FormTop.leA, FormTop.Sat, Cov.
    unfold PreO.morph. intros. 
    unfold Included, In in H. auto.
    simpl_relation. simpl in *. unfold FormTop.eqA, FormTop.Sat in *.
    unfold Same_set in *. destruct H.
    unfold Included, In in *. split; auto.
  + simpl. intros. split. intros. destruct H; tauto.
    intros. destruct H. left. assumption. right. assumption.
  + simpl. unfold FormTop.minA. unfold FormTop.downset, flip. intros.
    split; intros. destruct H. destruct H, H0.
    destruct x, a0, a1. auto.
    destruct H. constructor; econstructor; eauto. 
- simpl. intros. split; intros. destruct H. destruct s. 
  exists i. assumption. destruct H. econstructor; eauto.
- simpl. split; intros []; intros. 
  exists True. constructor. constructor 1 with (fun _ => True). constructor.
Qed.

Context {S} {leS eqS : S -> Ensemble S} {POS : PO.t leS eqS}.
Variable CovS : S -> (Ensemble S) -> Prop.

Definition Point (f : Ensemble S) := Cont.t MeetLat.le leS Cov CovS (fun _ => f).

Hypothesis FTS : FormTop.t leS CovS.

Instance FrameS : Frame.t (Ensemble S) (FormTop.FOps leS CovS)
  := FormTop.Frame leS CovS _ FTS.

Instance FrameOne : Frame.t (True -> Prop) (FormTop.FOps MeetLat.le Cov)
  := FormTop.Frame MeetLat.le Cov _ FTOne.

Definition toFPoint (f : Ensemble S) (pointf : Point f) :
  Frame.cmap Frame.prop_ops (FormTop.FOps leS CovS) :=
  {| Frame.finv := fun x => Cont.frame (fun _ => f) x I 
  ; Frame.cont := Frame.morph_compose _ _
    (Cont.toFrame FTOne FTS (fun _ => f) pointf) FTtoFrame |}.

End One.
End One.

Module InfoBaseCont.
Section InfoBaseCont.

Generalizable All Variables.

Require Import Morphisms.

Context {S} `{MLS : MeetLat.t S}.
Context {T} `{MLT : MeetLat.t T}.

Record pt {F : Ensemble T} : Prop :=
  { pt_local : forall {a b}, F a -> F b -> F (MeetLat.min a b)
  ; pt_le_right : forall a b, MeetLat.le a b -> F a -> F b
  ; pt_here : Inhabited F
  }.

Arguments pt : clear implicits.

Instance pt_proper : Proper ((eq ==> iff) ==> iff) pt.
Proof.
Admitted.


(** I have no idea whether this is in fact
    a good definition *)
Record t {F : S -> T -> Prop} :=
  { le_left : forall a b c, MeetLat.le a b -> F b c -> F a c
  ; le_right :  forall a b c,  F a b -> MeetLat.le b c -> F a c
  ; local : forall {a b c}, F a b -> F a c -> F a (MeetLat.min b c)
  ; here : forall s, Inhabited (F s)
  }.

Arguments t : clear implicits.


Let CovS : S -> (Ensemble S) -> Prop := @InfoBase.Cov _ MeetLat.le.
Let CovT : T -> (T -> Prop) -> Prop := @InfoBase.Cov _ MeetLat.le.

Theorem cont : forall (F : S -> T -> Prop),
  t F
  -> Cont.t MeetLat.le MeetLat.le CovS CovT F.
Proof.
intros. constructor; intros.
- unfold CovS, InfoBase.Cov. exists a. 
  apply (here H). unfold flip. apply PreO.le_refl.
- eapply (le_left H); eassumption. 
- unfold CovS, InfoBase.Cov. exists a. 
  exists (MeetLat.min b c). split. 
  split; apply MeetLat.min_ok. apply local; assumption.
  unfold flip. reflexivity.
- unfold CovT, CovS, InfoBase.Cov in *. 
  destruct H1 as [t0 Vt0 bt0].
  exists a. exists t0. assumption.
  apply (le_right H) with b; assumption.
  unfold flip. reflexivity.
Qed.

End InfoBaseCont.

Arguments t {_} {_} {_} {_} F.
Arguments pt {_} {_} F.

Section Compose.

Context {S : Type} {SOps} {MLS : MeetLat.t S SOps}.

Instance OneOps : MeetLat.Ops True := MeetLat.one_ops.

Theorem to_pt : forall (F : True -> Ensemble S), t F ->
  pt (F I).
Proof.
intros. constructor; intros.
- apply (local H); assumption. 
- eapply (le_right H); eassumption. 
- apply (here H).
Qed.

Theorem from_pt : forall (F : Ensemble S), pt F -> t (fun _ => F).
Proof.
intros. constructor; intros.
- assumption.
- eapply (pt_le_right H); eassumption.
- apply (pt_local H); assumption.
- apply (pt_here H).
Qed.

Context {T TOps} {MLT : MeetLat.t T TOps}.
Context {U UOps} {MLU : MeetLat.t U UOps}.

Theorem t_compose (F : S -> T -> Prop) (G : T -> U -> Prop)
  : t F -> t G
  -> t (compose F G).
Proof.
intros HF HG.
constructor; unfold compose; intros.
- destruct H0 as (t & Fbt & Gtc).
  exists t. split. 
  + eapply (le_left HF); eassumption.
  + assumption.
- destruct H as (t & Fat & Gtb).
  exists t. split. assumption. eapply (le_right HG); eassumption.
- destruct H as (t & Fat & Gtb).
  destruct H0 as (t' & Fat' & Gt'c).
  exists (MeetLat.min t t'). split. 
  + apply (local HF); assumption.
  + apply (local HG); eapply (le_left HG). 
    apply MeetLat.min_l. assumption. 
    apply MeetLat.min_r. assumption. 
- destruct (here HF s). destruct (here HG x).
  exists x0. exists x. auto.
Qed.

End Compose.

Section EvalPt.

Context {S SOps} {MLS : MeetLat.t S SOps}.
Context {T TOps} {MLT : MeetLat.t T TOps}.

Definition eval (F : S -> T -> Prop) (x : Ensemble S) (t : T) : Prop :=
  exists s, x s /\ F s t.

Require Import Morphisms.
Theorem eval_pt (F : S -> T -> Prop) (x : Ensemble S)
  : pt x -> t F -> pt (eval F x).
Proof.
intros Hx HF.
pose proof (t_compose (fun _ => x) F (from_pt _ Hx) HF).
apply to_pt in H. 
eapply pt_proper. 2: eassumption. simpl_relation.
Qed.

End EvalPt.

End InfoBaseCont.

Arguments InfoBaseCont.t {S} SOps {T} TOps F : rename, clear implicits.

Module IGCont.
Section IGCont.
Generalizable All Variables.
Context {S} `{POS : PreO.t S leS}.
Context {CovS : S -> Ensemble S -> Prop}.
Variable FTS : FormTop.t leS CovS.

Context {T} `{POT : PreO.t T leT}.
Context {IT : T -> Type}.
Variable CT : forall (t : T), IT t -> (T -> Prop).
Variable locT : FormTop.localized leT CT.
Let CovT := FormTop.GCov leT CT.

Record t {F : S -> T -> Prop} :=
  { here : forall s, Inhabited (F s)
  ; local : forall a b c, F a b -> F a c ->
       CovS a (fun s => exists d, FormTop.down leT b c d /\ F s d)
  ; le_left : forall a b c, leS a c -> F c b -> F a b
  ; le_right :  forall a b c,  F a b -> leT b c -> F a c
  ; ax_right : forall a b (j : IT b), F a b -> 
     CovS a (fun s => exists d, CT b j d /\ F s d)
  }.

Arguments t : clear implicits.

Theorem cont : forall F, t F -> Cont.t leS leT CovS CovT F.
Proof.
intros. constructor; intros.
- apply FormTop.refl. apply (here H).
- eapply le_left; eassumption.
- apply local; assumption.
- generalize dependent a. induction H1; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply IHGCov. eapply le_right; eassumption.
  + pose proof (ax_right H _ _ i H2).
    apply (@FormTop.trans S leS CovS FTS _ _ _ H3).  
    intros. destruct H4 as (d & CTaid & Fad).
    eapply H1; eassumption.
Qed.

Theorem converse : forall F, Cont.t leS leT CovS CovT F -> t F.
Proof.
intros.
constructor; intros.
Abort. 

End IGCont.
End IGCont.

Arguments IGCont.t {S} leS CovS
                   {T} leT {IT} CT F : clear implicits.

Module Discrete.
Section Discrete.

Generalizable All Variables.

Variable A : Type.

Hypothesis deceq : forall a a' : A, {a = a'} + {a <> a'}.

Definition Ix := @InfoBase.Ix _ (@Logic.eq A).
Definition C := @InfoBase.C _ (@Logic.eq A).
Definition CovI := @InfoBase.Cov _ (@Logic.eq A).

(** Woops I should have a positivity predicate to say that the
    "None" is covered by nothing *)
Definition Cov (a : A) (U : A -> Prop) : Prop := U a.

Require Import Morphisms.
Theorem CovEquiv : (eq ==> eq ==> iff)%signature CovI Cov.
Proof.
simpl_relation. unfold Cov, CovI, InfoBase.Cov.
split; intros.
- destruct H as [x t xt leat]. unfold flip in *. subst. assumption. 
-  exists y; unfold flip; auto.
Qed.

Instance FTproper : Proper _ FormTop.t := @FormTop.t_proper A.
Instance discretePO : PO.t Logic.eq Logic.eq := PO.discrete A.

Instance isCov : FormTop.t Logic.eq Cov.
Proof.
rewrite <- CovEquiv.
apply InfoBase.isCov.
Qed.

End Discrete.

Section FinFunc.

Context {A B : Type}.
Hypothesis deceqA : forall a a' : A, {a = a'} + {a <> a'}.
Hypothesis deceqB : forall b b' : B, {b = b'} + {b <> b'}.

Definition discrF (f : A -> B) (x : A) (y : B) : Prop := f x = y.

Instance POB : PO.t Logic.eq Logic.eq := PO.discrete B.

Ltac inv H := inversion H; clear H; subst.

Theorem fCont (f : A -> B) :
  Cont.t Logic.eq Logic.eq (Cov A) (Cov B) (discrF f).
Proof.
constructor; unfold Cov; intros.
- exists (f a). constructor.
- subst. assumption.
- inv H. inv H0. exists (f a). split.
  split; reflexivity. constructor.
- exists b; unfold In; auto.
Qed.

End FinFunc.

End Discrete.

Module ConcFunc.
Section ConcFunc.
Generalizable All Variables.
Context {S} `{Conc1 : Concrete.t A S In1}.
Context {T} `{Conc2 : Concrete.t B T In2}.

Let leS := Concrete.le A S In1.
Let CovS := @FormTop.GCov S leS
   (Concrete.Ix A S In1) (Concrete.C A S In1).

Let leT := Concrete.le B T In2.
Let CovT := @FormTop.GCov T leT
   (Concrete.Ix B T In2) (Concrete.C B T In2).

Definition cmap (f : A -> B) (g : S -> T -> Prop) := 
  forall (t : T) (a : A), In2 (f a) t <-> (exists s, g s t /\ In1 a s).

Theorem cont : forall f g, cmap f g
  -> Cont.t leS leT CovS CovT g.
Proof.
intros. unfold cmap in H. constructor; intros.
Abort.

End ConcFunc.
End ConcFunc.


Module Bundled.

Delimit Scope loc_scope with loc.
Open Scope loc.

(* Inductively-generated formal topology *)
Class IGT {S : Type} : Type :=
  { le : S -> Ensemble S
  ; PO :> PreO.t le
  ; Ix : S -> Type
  ; C : forall s, Ix s -> (Ensemble S)
  ; localized : FormTop.localized le C
  }.

Arguments IGT : clear implicits.

Generalizable All Variables.

Definition Cov `(X : IGT A) := FormTop.GCov le C.

Instance IGTFT `(X : IGT A) : FormTop.t le (Cov X) :=
  @FormTop.GCov_formtop _ _ PO _ _ localized.

Definition InfoBase {A : Type} {ops : MeetLat.Ops A}
  (ML : MeetLat.t A ops) : IGT A :=
  {| PO := PO.PreO
  ; localized := @InfoBase.loc _ _ _ MeetLat.PO
  |}.

Definition One : IGT _ := InfoBase MeetLat.one.

Definition times `(LA : IGT A) `(LB : IGT B) : IGT _ :=
  {| PO := Product.PO A B
  ; localized := Product.loc _ _ _ _ _ _ localized localized
  |}.

Infix "**" := times (at level 80) : loc_scope.

Record cmap `{LA : IGT A} `{LB : IGT B} : Type :=
  { mp : A -> B -> Prop
  ; mp_ok : Cont.t le le (Cov LA) (Cov LB) mp
  }.

Arguments cmap {A} LA {B} LB : clear implicits.

Infix "~>" := cmap (at level 60) : loc_scope.

Definition id `{LA : IGT A} : LA ~> LA := 
  {| mp := Cont.id
  ; mp_ok := Cont.t_id |}.

Definition comp `{LA : IGT A} 
  `{LB : IGT B} `{LD : IGT D} (f : LA ~> LB) (g : LB ~> LD) : LA ~> LD :=
  {| mp := compose (mp f) (mp g)
  ; mp_ok := Cont.t_compose (mp f) (mp g) (mp_ok f) (mp_ok g)
  |}.

End Bundled.