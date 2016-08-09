Require Import Algebra.FrameC Algebra.SetsC CMorphisms CRelationClasses.
Set Asymmetric Patterns.
Set Universe Polymorphism.

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

Local Open Scope Subset.

Module FormTop.

Generalizable All Variables.


Section Defn.

(** We assume we have some type [S] equipped
    with a partial order. *)
Context {S} {le : crelation S} {PO : PreO.t le}.
Context {Cov : S -> Subset S -> Type}.

Infix "<|" := Cov (at level 60) : FT_scope.
Local Infix "<=" := le.

Notation "U <<| V" := (forall a, In U a -> Cov a V) (at level 60) : FT_scope.
Local Open Scope FT_scope.

(** States that [c] is less than or equal to the minimum of
    [a] and [b]. *)
Definition down (a b c : S) : Type :=
  le c a * le c b.

Definition downset (U : Subset S) : Subset S :=
  union U (fun x y => y <= x).

Lemma down_downset : forall (x y : S) (U V : Subset S),
  In U x -> In V y -> 
  down x y ⊆ downset U ∩ downset V.
Proof.
intros x y U V Ux Vy. 
unfold Included, pointwise_rel, arrow; intros a downa.
destruct downa. econstructor; econstructor; eauto.
Qed.

Lemma downset_included : forall V,
   V ⊆ downset V.
Proof.
intros. unfold Included, pointwise_rel, arrow; intros.
econstructor. eassumption. reflexivity.
Qed.

(** Definition 2.1 of [1].
    Definition of when the [Cov] relation is indeed a formal cover.
    Here, the [Cov] relation means the little triangle that is
    seen in the literature. *)
Class t : Type :=
  { refl : forall (a : S) (U : Subset S), In U a -> a <| U
  ; trans : forall {a U}, a <| U 
     -> forall V, U <<| V
     -> a <| V
  ; le_left : forall (a b : S) (U : Subset S)
     , a <= b -> b <| U -> a <| U
  ; le_right : forall {a : S} {U V : Subset S}
    , a <| U -> a <| V
    -> a <| downset U ∩ downset V
  }.

Arguments t : clear implicits.

(** Definition of a formal cover that also has a positivity predicate. *)
(** We bundle the positivity predicate, because if there is one,
    it's unique. *)
Class tPos :=
  { Pos : Subset S
  ; mono : forall a U, Pos a -> a <| U -> Inhabited (U ∩ Pos)
  ; positive : forall a U, (Pos a -> a <| U) -> a <| U
  }.

Arguments tPos : clear implicits.

Lemma mono_le `{t} `{tPos} : forall a b, le a b -> Pos a -> Pos b.
Proof.
intros. 
destruct (mono a (eq b) X0).
eapply le_left. eassumption. apply refl.
reflexivity. destruct i. subst. assumption.
Qed.

Definition stable :=
  forall a b U V, a <| U -> b <| V
  -> forall c, c <= a -> c <= b ->
    c <| downset U ∩ downset V.

Context `{FTS : t}.

Lemma monotone (U V : Subset S)
  : U ⊆ V -> forall a : S, a <| U -> a <| V.
Proof.
intros UV a CovaU. eapply trans; try eassumption.
intros. apply refl. apply UV. assumption.
Qed.

Lemma subset_equiv : forall (U V : Subset S), U === V
  -> forall a, iffT (a <| U) (a <| V).
Proof.
intros. split; apply monotone; firstorder.
Qed.

End Defn.

Arguments t {S} le Cov : clear implicits.
Arguments tPos {S} Cov : clear implicits.
Arguments down {S} le a b c : clear implicits.
Arguments downset {S} le U _ : clear implicits.
Arguments stable {S} le Cov : clear implicits.

Ltac trans H := apply (trans H); let T := type of H in 
  match constr:(T) with
  | _ ?a _ => clear a H; intros a H
  end.

Ltac etrans := match goal with
     | [ H : ?Cov ?a _  |- ?Cov ?a _ ] => try (trans H)
     end. 

Ltac join H1 H2 := let H := fresh H1 in
  pose proof (FormTop.le_right H1 H2) as H; clear H1 H2.

Ltac ejoin := repeat match goal with
  | [ H1 : ?Cov ?a _, H2 : ?Cov ?a _  |- ?Cov ?a _ ] => join H1 H2
  end.

Section IGDefn.

Context {S} {le : crelation S}.
Context `{PO : PreO.t S le}.

(** Inductively generated formal topologies. See section
    3 of [1]. *)

Context {I : S -> Type}.
Context {C : forall (s : S), I s -> Subset S}.

(** Given the axiom set [I] and [C], this generates the
    formal cover corresponding to that axiom set. *)
Inductive GCov (a : S) (U : Subset S) : Type :=
  | grefl : U a -> GCov a U
  | gle_left : forall (b : S)
     , le a b -> GCov b U -> GCov a U
  | ginfinity : forall (i : I a),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Inductive GCovL (a : S) (U : Subset S) : Type :=
  | glrefl : U a -> GCovL a U
  | glle_left : forall (b : S), le a b -> GCovL b U -> GCovL a U
  | gle_infinity : forall (b : S) (i : I b)
    , le a b -> (forall u, { u' : S & (C b i u' * down le a u' u)%type } -> GCovL u U)
    -> GCovL a U.

Lemma Lmore a U : GCov a U -> GCovL a U.
Proof.
intros aU. induction aU.
- apply glrefl. assumption.
- apply glle_left with b; assumption.
- apply (gle_infinity a _ a i (PreO.le_refl _)).
  intros. destruct X0 as (u' & Caiu' & (ua & uu')).
  apply glle_left with u'. assumption. apply X.
  assumption.
Qed.

Lemma gmonotone (a : S) (U V : Subset S) :
  U ⊆ V -> GCov a U -> GCov a V.
Proof.
intros UV aU. induction aU.
- apply grefl. apply UV. assumption.
- eapply gle_left. eassumption. apply IHaU.
  assumption.
- eapply ginfinity. eauto.
Qed.

Lemma gmonotoneL a (U V : Subset S) :
  U ⊆ V -> GCovL a U -> GCovL a V.
Proof.
intros UV aU. induction aU.
- apply glrefl. apply UV. assumption.
- eapply glle_left. eassumption. apply IHaU. assumption.
- eapply gle_infinity. eassumption. intros. apply X; eassumption.
Qed.

Lemma gsubset_equiv (U V : Subset S) : U === V
  -> forall a, iffT (GCov a U) (GCov a V).
Proof.
intros UV a. split; apply gmonotone; intros; rewrite UV; reflexivity.
Qed.

Class gtPos :=
  { gPos : Subset S
  ; gmono_le : forall a b, le a b -> gPos a -> gPos b
  ; gmono_ax : forall a (i : I a), gPos a -> Inhabited (C a i ∩ gPos)
  ; gpositive : forall a U, (gPos a -> GCov a U) -> GCov a U
  }.

Lemma GCov_Pos `{gtPos} : tPos GCov.
Proof.
unshelve econstructor.
- exact gPos.
- intros. induction X0.
  + exists a. split; assumption.
  + apply IHX0. eapply gmono_le; eassumption.
  + destruct (gmono_ax a i X). destruct i0.
    eapply X0; eassumption.
- apply gpositive.
Qed.

Class localized := 
  IsLocalized : forall (a c : S),
  le a c -> forall (i : I c),
  { j : I a  & 
  (forall s, C a j s -> { u : S & (C c i u * down le a u s) } )}%type.

Context `{loc : localized}. 

(** Proposition 3.5 of [1] *)
Lemma le_infinity (a c : S) : le a c ->
  forall (i : I c) (U : Subset S), 
  (forall u v, C c i v -> down le a v u -> GCov u U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros ac i U H. 
destruct (loc a c ac i) as (i' & s).
apply (ginfinity _ _ i').
intros u Caxu.
specialize (s u Caxu).
destruct s as (u' & (cciu & downu)).
eapply H; eassumption.
Qed.

Lemma GCov_stable : stable le GCov.
Proof.
unfold localized in loc.
unfold stable. 
intros a b U V aU bV. 
induction aU.
- induction bV; intros.
  + apply grefl. constructor; econstructor; eassumption.
  + apply IHbV. assumption. 
    etransitivity; eassumption.
  + pose proof (loc c a0 X1 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ _ j).

    intros. specialize (loc' u0 X2).
    destruct loc'. destruct p. destruct d.
    eapply X. eassumption.
    transitivity c; eassumption. assumption.
- intros c ca cb. 
  apply IHaU. transitivity a; eassumption. assumption.
- intros c ca cb. pose proof (loc c a ca i) as loc1.
  destruct loc1 as [j loc'].
  apply (ginfinity _ _ j).

  intros. specialize (loc' u X0).
  destruct loc'. destruct p. destruct d.
  eapply X. eassumption. assumption.
  transitivity c; assumption.
Qed.

(** Theorem 3.6 of [1].
    In fact, the formal cover that we defined based on the axiom set 
    indeed satistifes the requirements of being a formal topology. *)
Instance GCov_formtop : t le GCov.
Proof.
unfold localized in loc.
constructor.
- apply grefl.
- intros a U aU V H. induction aU.
  + auto.
  + eapply gle_left. eassumption. apply IHaU.
    assumption.
  + apply (ginfinity _ _ i). intros. apply X; assumption.
- intros; eapply gle_left; eassumption.
- intros.
  pose proof GCov_stable as stab.
  unfold stable in stab.
  eapply GCov_stable; (eassumption || reflexivity).
Qed.

End IGDefn.

Arguments localized {S} le {I} C : clear implicits.
Arguments GCov {S} le {I} C _ _ : clear implicits.
Arguments GCovL {S} le {I} C _ _ : clear implicits.
Arguments gtPos {S} le {I} C : clear implicits.

Section AxiomSetRefine.

Context {S} {le : crelation S}.
Context `{PO : PreO.t S le}.

Definition AxiomSetRefine {I I' : S -> Type} 
  (C : forall s, I s -> Subset S) (C' : forall s, I' s -> Subset S) :=
  forall s (i : I s), { j : I' s  &  C s i === C' s j }.

Lemma AxRefineCovL {I I'} (C : forall s, I s -> Subset S) 
  (C' : forall s, I' s -> Subset S) :
  AxiomSetRefine C C' -> forall a U, GCovL le C a U -> GCovL le C' a U.
Proof.
intros CC' a U aU. unfold AxiomSetRefine in CC'.
induction aU.
- apply glrefl. assumption.
- apply glle_left with b; assumption.
- destruct (CC' b i).
  apply gle_infinity with b x. assumption.
  intros.  destruct X0 as (u' & Gbxu' & downau'u).
  apply X. exists u'. split. apply s. apply Gbxu'. assumption.
Qed.

Lemma AxRefineCov {I I'} (C : forall s, I s -> Subset S) 
  (C' : forall s, I' s -> Subset S) :
  AxiomSetRefine C C' -> forall a U, GCov le C a U -> GCov le C' a U.
Proof.
intros CC' a U aU. unfold AxiomSetRefine in CC'.
induction aU.
- apply grefl. assumption.
- apply gle_left with b; assumption.
- destruct (CC' a i).
  apply ginfinity with x.
  intros. apply X. apply s. assumption. 
Qed.

End AxiomSetRefine.

Lemma downset_Proper_impl {A} : Proper ((eq ==> eq ==> arrow) ==> Included ==> Included)
  (@downset A).
Proof.
unfold Proper, respectful.
intros. unfold Included, In, pointwise_rel, arrow.
intros. destruct X1. econstructor.
apply X0. eassumption. unfold arrow in X.
eapply X; try reflexivity. assumption.
Qed.

Lemma Same_set_Included {A} (U V : Subset A) : U === V -> ((U ⊆ V) * (V ⊆ U))%type.
Proof.
intros H. split; rewrite H; reflexivity. 
Qed.

Instance downset_Proper {A} : Proper ((eq ==> eq ==> iffT) ==> Same_set ==> Same_set) (@downset A).
Proof.
unfold Proper, respectful. intros.
apply Same_set_Included in X0. destruct X0. 
apply Included_Same_set; apply downset_Proper_impl; try assumption;
  unfold respectful, arrow; intros; subst.
eapply (fst (X _ _ eq_refl _ _ eq_refl)). assumption.
eapply (snd (X _ _ eq_refl _ _ eq_refl)). assumption.
Qed.

Lemma t_proper_impl {S : Type} : 
  Proper ((eq ==> eq ==> iffT) ==> (eq ==> Same_set ==> iffT) ==> arrow) (@t S).
Proof.
unfold Proper, respectful, arrow; intros.
destruct X1. constructor; intros.
- rewrite <- X0; try reflexivity. apply refl0. eassumption.
- rewrite <- X0; try reflexivity. eapply trans0. 
  rewrite X0; try reflexivity. eassumption. 
  intros. rewrite X0; try reflexivity. apply X2. assumption.
- rewrite <- X0; try reflexivity. eapply le_left0. 
  rewrite X; try reflexivity. eassumption.
  rewrite X0; try reflexivity. assumption.
- rewrite <- X0. 2: reflexivity. Focus 2.
  apply Intersection_Proper. apply downset_Proper.
  unfold respectful. apply X. reflexivity.
  apply downset_Proper. unfold respectful. apply X.
  reflexivity. 
  apply le_right0; rewrite X0; try reflexivity; assumption.
Qed.

Instance t_proper {S : Type} : 
  Proper ((eq ==> eq ==> iffT) ==> (eq ==> Same_set ==> iffT) ==> iffT) (@t S).
Proof.
pose proof (@t_proper_impl S).
unfold Proper, respectful, arrow in X. 
unfold Proper, respectful. intros.
split; intros;
eapply X; try eassumption.
intros. symmetry. apply X0; symmetry; assumption.
intros. symmetry. apply X1; symmetry; assumption.
Qed.

Section Properness.
Context {S : Type}.
Variable (le : crelation S) (Cov : S -> Subset S -> Type).
Context `{PO : PreO.t S le}.
Context `{tS : t S le Cov}. 


Instance Cov_Proper  :
  Proper (le --> Included ==> arrow) Cov.
Proof.
unfold Proper, respectful, arrow. intros.
unfold flip in *. 
eapply le_left; try eassumption.
eapply monotone; eassumption.
Qed.

(** This is just a flipped version of what's above. It
    shouldn't be needed. *)

Instance Cov_Proper3  :
  Proper (le ==> Included --> flip arrow) Cov.
Proof.
unfold Proper, respectful, arrow, flip. intros.
eapply le_left; try eassumption.
eapply monotone; eassumption.
Qed.


Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) Cov.
Proof.
unfold Proper, respectful. intros x y xy x' y' xy'. subst.
split; intros. apply (monotone x'). 
apply Included_subrelation. assumption. assumption.
apply (monotone y'). apply Included_subrelation. symmetry. assumption.
assumption.
Qed.

End Properness.


Section Localize.

Context {S : Type}.
Variable (le : crelation S).
Context {Ix : S -> Type}.
Variable (C : forall s, Ix s -> Subset S).

Definition IxL (a : S) := 
  { i : sigT Ix & match i with
    | existT c _ => le a c end }.

Definition CL (a : S) : IxL a -> Subset S := 
  fun i => match i with
  | existT (existT c k) _ => fun z => { u : S & C c k u * down le a u z }%type
  end.

Context {PO : PreO.t le}.

Local Instance Llocalized : localized le CL.
Proof.
unfold localized.
intros. destruct i. simpl in *. destruct x.
exists (existT (fun i' => match i' with existT c k => le a c end) 
  (existT _ x i) (PreO.le_trans _ _ _ X y)).
simpl. intros s X'.
destruct X' as (u & Cxiu & downaus).
exists s. split. exists u. split. assumption. unfold down in *.
  destruct downaus.
  split. transitivity a; assumption. assumption.
  destruct downaus.
  split; [assumption | reflexivity].
Qed.

Theorem cov_equiv : forall a U,
  iffT (GCovL le C a U) (GCov le CL a U).
Proof.
intros a U. split; intros H.
- induction H.
  + apply grefl. assumption.
  + apply gle_left with b; assumption.
  + pose (existT (fun j : sigT Ix => match j with existT c _ => le a c end)
       (existT Ix b i) l : IxL a).
  apply ginfinity with i0.
  intros u X0. apply X.
  unfold CL in X0.
  simpl in X0. destruct X0 as (u' & Caiu' & (ua & uu')).
  exists u'. split. assumption. split; eassumption.
- induction H.
  + apply glrefl. assumption.
  + apply glle_left with b; assumption.
  + destruct i as ((c & i) & ac).
    simpl in *.
    apply (gle_infinity a _ c i). assumption.
    intros. auto.
Qed.

Local Instance GCov_Proper : Proper (le --> Included ==> arrow)
  (GCov le CL). 
Proof. 
apply Cov_Proper. apply GCov_formtop.
Qed.

Theorem GCovL_formtop : t le (GCovL le C).
Proof.
eapply t_proper. reflexivity.
unfold Proper, respectful; intros.
2: apply GCov_formtop.
split; intros; subst.
eapply GCov_Proper. reflexivity. rewrite <- X. reflexivity.
apply cov_equiv. assumption.
apply cov_equiv. eapply GCov_Proper. reflexivity.
rewrite X. reflexivity. assumption.
Qed.

End Localize.

Section ToFrame.
Context {S : Type}.
Variable (le : crelation S) (Cov : S -> Subset S -> Type).

Definition Sat (U : Subset S) : Subset S :=
  fun s => Cov s U.

Definition leA (U V : Subset S) : Type := Included (Sat U) (Sat V).

Definition eqA (U V : Subset S) : Type := Same_set (Sat U) (Sat V).

Definition minA (U V : Subset S) : Subset S :=
  downset le U ∩ downset le V.

Inductive supA I (f : I -> Subset S) : Subset S := 
  MksupA : forall i s, f i s -> In (supA I f) s.

Definition LOps : Lattice.Ops (Subset S) :=
  {| Lattice.le := leA
  ;  Lattice.eq := eqA
  ;  Lattice.max := Union
  ;  Lattice.min := minA
  |}.

Instance LOps' : Lattice.Ops (Subset S) := LOps.

Definition FOps : Frame.Ops (Subset S) := 
  {| Frame.LOps := LOps
   ; Frame.sup := supA
  |}.

Instance FOps' : Frame.Ops (Subset S) := FOps.

Context `{PO : PreO.t S le}.
Context `{tS : t S le Cov}. 

Theorem FramePreO : @PreO.t (Subset S) leA.
Proof.
constructor; unfold leA; intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Theorem FramePO : @PO.t (Subset S) leA eqA.
Proof.
constructor; unfold eqA; intros.
- apply FramePreO.
- unfold leA. unfold Proper, respectful. 
  intros. rewrite X, X0. reflexivity.
- unfold leA in *. split; intros.
  apply X. assumption. apply X0. assumption.
Qed.

Existing Instances Cov_Proper Cov_Proper2 Cov_Proper3.

Theorem Sat_Intersection : forall U V,
  Sat (U ∩ V) ⊆ Sat U ∩ Sat V.
Proof.
intros. constructor; unfold Sat, In in *.
  rewrite <- (Intersection_Included_l _ U V); eassumption.
  rewrite <- (Intersection_Included_r _ U V); eassumption.
Qed.

Theorem Sat_Union : forall U V,
  Sat U ∪ Sat V ⊆ Sat (U ∪ V).
Proof.
intros. unfold Included, pointwise_rel, arrow; intros a H. 
destruct H; unfold In, Sat in *. 
rewrite <- Union_Included_l. assumption. 
rewrite <- Union_Included_r. assumption. 
Qed.

Theorem Sat_mono : forall U, U ⊆ Sat U.
Proof.
intros. unfold Included, pointwise_rel, arrow, Sat. 
intros. apply refl. assumption.
Qed.

Theorem Sat_mono2 : forall U V, U ⊆ V -> Sat U ⊆ Sat V.
Proof.
intros U V H. unfold Included, pointwise_rel, arrow, Sat. 
intros a X. rewrite <- H. assumption.
Qed.

Theorem Cov_Sat : forall a U, iffT (Cov a U) (Cov a (Sat U)).
Proof.
intros. split; intros. rewrite <- Sat_mono. assumption.
etrans. assumption.
Qed.

Theorem Sat_downset : forall U, Sat U === Sat (downset le U).
Proof.
intros. split.
- apply Sat_mono2. unfold Included, In, downset.
  intros. econstructor. eassumption. reflexivity.
- unfold Included, Sat, In, downset.
  intros H. etrans. destruct H. 
  rewrite l. apply refl. assumption.
Qed.

Existing Instances Union_Proper_le_flip Union_Proper_eq.

Theorem FrameLatt : Lattice.t (Subset S) LOps.
Proof.
constructor; intros.
- apply FramePO.
- simpl. unfold Proper, respectful, eqA. intros x y H x0 y0 H0.
  split; unfold Included, In, Sat; intros.
  + apply Cov_Sat. rewrite <- Sat_Union.
    rewrite <- H, <- H0.
    rewrite <- !Sat_mono. assumption.
  + apply Cov_Sat. rewrite <- Sat_Union. 
    rewrite H, H0. rewrite <- !Sat_mono. assumption. 
- constructor.
  + simpl. unfold leA. apply Sat_mono2. 
    apply Union_Included_l.
  + simpl. unfold leA. apply Sat_mono2.
    apply Union_Included_r.
  + simpl. unfold leA. intros.
    unfold Sat, Included, pointwise_rel, arrow. 
    intros a H. etrans. rewrite Cov_Sat. destruct H.
    * rewrite <- X, <- Cov_Sat. apply refl. assumption.
    * rewrite <- X0, <- Cov_Sat. apply refl. assumption.
- simpl. unfold Proper, respectful, eqA, minA.
  intros x y H x0 y0 H0.
  apply Included_Same_set.
  + rewrite Sat_Intersection. rewrite <- !Sat_downset.
    rewrite H, H0. unfold Included, pointwise_rel, arrow; 
    intros a H1.
    destruct H1. unfold Sat, In in *.
    join s s0. assumption.
  + rewrite Sat_Intersection. rewrite <- !Sat_downset.
    rewrite <- H, <- H0. unfold Included, pointwise_rel, arrow; 
    intros a H1.
    destruct H1. unfold Sat, In in *.
    join s s0; assumption.
- simpl. constructor; unfold leA, minA; intros.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H.
    etrans. destruct H as (H0 & H1). destruct H0.
    rewrite l0. apply refl. assumption.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H.
    etrans. destruct H as (H0 & H1). destruct H1. 
    rewrite l0. apply refl. assumption.
  + unfold Sat, Included, pointwise_rel, arrow; intros a H. 
    etrans. apply le_right. rewrite Cov_Sat, <- X, <- Cov_Sat.
    apply refl. assumption.
    rewrite Cov_Sat, <- X0, <- Cov_Sat. apply refl.  assumption.
Qed.

Theorem Frame : Frame.t (Subset S) FOps.
Proof.
constructor; intros.
- apply FrameLatt.
- simpl. unfold eqA, pointwise_relation. 
  unfold Proper, respectful. intros.
  split; unfold Included, Sat; intros.
  + etrans. destruct X0.
    apply (trans (U := y i)).
    rewrite Cov_Sat, <- (X i), <- Cov_Sat. 
    apply refl. assumption. specialize (X i).
    intros. apply refl. econstructor. eassumption. 
  + etrans. destruct X0.
    apply (trans (U := x i)).
    rewrite Cov_Sat, (X i), <- Cov_Sat.
    apply refl. assumption. intros.
    apply refl. econstructor; eassumption.
- simpl. constructor; unfold leA; intros.
  + apply Sat_mono2. unfold Included, pointwise_rel, arrow; intros. 
    econstructor; eassumption. 
  + unfold Included, Sat, pointwise_rel, arrow; intros.
    etrans. destruct X0. 
    rewrite Cov_Sat, <- (X i), <- Cov_Sat.
    apply refl. assumption.
- simpl. unfold minA, eqA.
  split; apply Sat_mono2.
  + unfold Included, pointwise_rel, arrow. 
    intros a0 H. destruct H as (H & H0).
    destruct H0. destruct i.
    repeat (econstructor; try eassumption).
  + unfold Included, pointwise_rel, arrow. 
    intros a0 H. destruct H. destruct i0.
    constructor. assumption. destruct d0. 
    repeat (econstructor; try eassumption).
Qed. 

End ToFrame.

End FormTop.

Module Subspace.

Section Defn.
Context {S : Type} {leS : crelation S}.
Hypothesis POS : PreO.t leS.
Variable CovS : S -> (Subset S) -> Type.

Definition Cov (V : Subset S) (a : S)
  (U : Subset S) : Type := CovS a (V ∪ U).


Context {FTS : FormTop.t leS CovS}.

Existing Instances FormTop.Cov_Proper FormTop.Cov_Proper2 FormTop.Cov_Proper3.

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
  destruct i. rewrite l. apply FormTop.refl. left.  assumption.
  destruct i0. rewrite l0. apply FormTop.refl. left. assumption.
  rewrite <- Union_Included_r.
  apply FormTop.le_right. 
  rewrite l. apply FormTop.refl. assumption.
  rewrite l0. apply FormTop.refl. assumption.
Qed.

End Defn.

Arguments Cov {S} CovS V a U : clear implicits.

Section IGDefn.
Context {S} {leS : crelation S}.
Hypothesis POS : PreO.t leS.
Context {Ix : S -> Type}.
Variable C : forall a, Ix a -> (Subset S).

Variable V : Subset S. 

Definition SIx (a : S) : Type :=
  (Ix a + { I : True & V a })%type.

Definition SC (a : S) (i : SIx a) : Subset S := 
  match i with
  | inl i' => C a i'
  | inr _ => fun _ => False
  end.

Theorem same : forall a U,
  iffT (FormTop.GCovL leS SC a U) (Cov (FormTop.GCovL leS C) V a U).
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



(** An inductively generated formal topology for the Cantor space.
    See Section 4.1 of [1]. *)
Module Cantor.

Variable A : Type.

Definition S := list A.

Definition Ix (s : S) := True.

Require Import Coq.Lists.List.

Definition C (s : S) (_ : True) (s' : S) : Type := 
  { b | s' = s ++ (b :: nil) }.

Definition LE {A} (xs ys : list A) : Type := { zs |
  xs = ys ++ zs }.

Lemma LE_PO {A : Type} : @PO.t (list A) LE eq.
Proof.
constructor; intros.
- constructor; unfold LE; intros.
  + exists nil. rewrite app_nil_r. reflexivity.
  + destruct X, X0.
    exists (x1 ++ x0). rewrite e, e0.
    rewrite app_assoc. reflexivity.
- unfold Proper, respectful. 
  unfold LE in *. intros. subst. reflexivity. 
- unfold LE in *.  destruct X, X0.
  rewrite e0 in e. rewrite <- app_assoc in e.
  rewrite <- app_nil_r in e at 1.
  apply app_inv_head in e.
  symmetry in e. apply app_eq_nil in e.
  destruct e. subst. rewrite app_nil_r.
  reflexivity.
Defined.

Definition Cov := FormTop.GCov LE C.

Theorem loc : FormTop.localized LE C.
Proof.
unfold FormTop.localized.
intros a c H i. unfold Ix in *. destruct i. exists I.
intros s H0. unfold C in *. destruct H0.
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
  rewrite e. rewrite e0. rewrite <- app_assoc. reflexivity.
Qed.

End Cantor.
