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
  union U (fun x y => y <= x).

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
Context `{PO : PreO.t S le}.

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

Section AxiomSetRefine.

Context {S} {le : S -> S -> Prop}.
Context `{PO : PreO.t S le}.

Definition AxiomSetRefine {I I' : S -> Type} 
  (C : forall s, I s -> Ensemble S) (C' : forall s, I' s -> Ensemble S) :=
  forall s (i : I s), exists (j : I' s), C s i === C' s j.

Lemma AxRefineCov {I I'} (C : forall s, I s -> Ensemble S) 
  (C' : forall s, I' s -> Ensemble S) :
  AxiomSetRefine C C' -> forall a U, GCovL le C a U -> GCovL le C' a U.
Proof.
intros. unfold AxiomSetRefine in H.
induction H0.
- apply glrefl. assumption.
- apply glle_left with b; assumption.
- destruct (H b i).
  apply gle_infinity with b x. assumption.
  intros.  destruct H4 as (u' & Gbxu' & downau'u).
  apply H2. exists u'. split. unfold Included, In in H3.
  eapply H3. apply Gbxu'. assumption.
Qed.

End AxiomSetRefine.

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

Theorem GCovL_formtop : t le (GCovL le C).
Proof.
eapply t_proper. reflexivity.
unfold Proper, respectful; intros. subst. apply cov_equiv.
apply GCov_formtop. apply Llocalized.
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
    pose proof (FormTop.gle_infinity _ SC x x (inr (exist (fun _ => V x) I H)) (fun _ => False) 
       (PreO.le_refl _)).
    apply H0. intros. simpl in *.
    destruct H1 as (u' & bot & downau). contradiction. simpl.
    intros. unfold Included, In; intros; contradiction.
    * apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b. assumption. apply IHGCovL.
    reflexivity.
  + apply (FormTop.gle_infinity _ SC a b (inl i)).
    assumption. intros.
    apply H1. apply H2. reflexivity.
Qed.

End IGDefn.

End Subspace.



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
