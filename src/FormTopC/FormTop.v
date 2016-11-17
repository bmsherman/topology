Require Import 
  Algebra.OrderC
  Algebra.FrameC
  Algebra.SetsC
  CMorphisms
  CRelationClasses.
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

Record PreOrder :=
  { PO_car :> Type
    (** The type of basic opens, i.e., observable property *)
  ; le : crelation PO_car
    (** a preorder on [S] which indicates when one basic open lies in another,
       i.e., one observable property implies another *)
   }.

Infix "<=" := (le _) : FT_scope.
Notation "a <=[ X ] b" := (le X a b) (at level 40, format "a  <=[ X ]  b").

Definition Open (A : PreOrder) := Subset A.
Delimit Scope FT_scope with FT.

Local Open Scope FT.

(** States that [c] is less than or equal to the minimum of
    [a] and [b]. *)
Definition down {A : PreOrder} (a b c : A) : Type :=
  (c <= a)%FT * (c <= b)%FT.

Infix "↓" := (down) (at level 30).

Definition downset {A} (U : Open A) : Open A :=
  union U (fun x y => y <= x).

Notation "⇓ U" := (downset U) (at level 30).

Lemma down_downset {A : PreOrder} (x y : A) (U V : Open A) :
  In U x -> In V y -> 
  x ↓ y ⊆ ⇓U ∩ ⇓V.
Proof.
intros Ux Vy. 
unfold Included, pointwise_rel, arrow; intros a downa.
destruct downa. econstructor; econstructor; eauto.
Qed.

Lemma downset_included {A} {PO : PreO.t (le A)} : forall (V : Open A),
   V ⊆ ⇓ V.
Proof.
intros. unfold Included, pointwise_rel, arrow; intros.
econstructor. eassumption. reflexivity.
Qed.

Lemma downset_Proper_impl {A} : Proper (Included ==> Included)
  (@downset A).
Proof.
unfold Proper, respectful.
intros. unfold Included, In, pointwise_rel, arrow.
firstorder. unfold downset. exists a0. apply X. assumption. assumption.
Qed.

Instance downset_Proper {A} : Proper (Same_set ==> Same_set) (@downset A).
Proof.
unfold Proper, respectful. intros.
apply Same_set_Included in X. destruct X. 
apply Included_Same_set; apply downset_Proper_impl; try assumption;
  unfold respectful, arrow; intros; subst.
Qed.

Module PreSpace.
Record t :=
  { S :> PreOrder
  ; Cov : S -> Subset S -> Type }.
End PreSpace.

Infix "<|" := (PreSpace.Cov _) (at level 60) : FT_scope.
Notation "U <<| V" := (forall a, In U a -> a <| V) (at level 60) : FT_scope.
Notation "a <|[ X ] U" := (PreSpace.Cov X a U) (at level 63, format "a  <|[ X ]  U") : FT_scope.
Notation "U <<|[ X ] V" := (forall a, In U a -> a <|[X] V) (at level 60) : FT_scope.
Coercion PreSpace.S : PreSpace.t >-> PreOrder.

Local Open Scope FT.

Section Defn.
(** We assume we have some type [S] equipped
    with a partial order. *)
Context {A : PreSpace.t}.

(** Definition 2.1 of [1].
    Definition of when the [Cov] relation is indeed a formal cover.
    Here, the [Cov] relation means the little triangle that is
    seen in the literature. *)
Class t : Type :=
  { refl : forall (a : PreSpace.S A) (U : Open A), In U a -> a <| U
  ; trans : forall {a : PreSpace.S A} {U : Open A}, a <| U 
     -> forall V, U <<| V
     -> a <| V
  ; le_left : forall (a b : PreSpace.S A) (U : Open A)
     , a <= b -> b <| U -> a <| U
  ; le_right : forall {a : PreSpace.S A} {U V : Open A}
    , a <| U -> a <| V
    -> a <| downset U ∩ downset V
  }.

Arguments t : clear implicits.

(** Definition of a formal cover that also has a positivity predicate. *)
(** We bundle the positivity predicate, because if there is one,
    it's unique. *)
Class tPos :=
  { Pos : Subset A
  ; mono : forall a U, Pos a -> a <| U -> Inhabited (U ∩ Pos)
  ; positive : forall a U, (Pos a -> a <| U) -> a <| U
  }.

Arguments tPos : clear implicits.

Lemma mono_le `{t} `{tPos} : forall a b, a <= b -> Pos a -> Pos b.
Proof.
intros. 
destruct (mono a (eq b) X0).
eapply le_left. eassumption. apply refl.
reflexivity. destruct i. subst. assumption.
Qed.

Lemma all_Pos : 
  (forall (a : A) U, a <| U -> Inhabited U) -> tPos.
Proof.
unshelve econstructor.
- exact (fun _ => True).
- simpl. intros.
  destruct (X a U X0) as [x P].
  exists x. split. assumption. auto.
- simpl. intros. auto.
Qed.

Definition stable :=
  forall (a b : A) U V, a <| U -> b <| V
  -> forall c, c <= a -> c <= b ->
    c <| downset U ∩ downset V.

Context `{FTS : t}.

Lemma monotone (U V : Open A)
  : U ⊆ V -> forall a : A, a <| U -> a <| V.
Proof.
intros UV a CovaU. eapply trans; try eassumption.
intros. apply refl. apply UV. assumption.
Qed.

Lemma subset_equiv : forall (U V : Open A), U === V
  -> forall a, (a <| U) <--> (a <| V).
Proof.
intros. split; apply monotone; firstorder.
Qed.

Instance Cov_Proper  :
  Proper (le A --> Included ==> arrow) (PreSpace.Cov A).
Proof.
unfold Proper, respectful, arrow. intros.
unfold flip in *. 
eapply le_left; try eassumption.
eapply monotone; eassumption.
Qed.

Instance Cov_Proper3  :
  Proper (le A ==> Included --> flip arrow) (PreSpace.Cov A).
Proof.
unfold Proper, respectful, arrow, flip. intros.
eapply le_left; try eassumption.
eapply monotone; eassumption.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) (PreSpace.Cov A).
Proof.
unfold Proper, respectful. intros x y xy x' y' xy'. subst.
split; intros. apply (monotone x'). 
apply Included_subrelation. assumption. assumption.
apply (monotone y'). apply Included_subrelation. symmetry. assumption.
assumption.
Qed.

End Defn.

Arguments t : clear implicits.
Arguments tPos : clear implicits.
Arguments down : clear implicits.
Arguments downset : clear implicits.
Arguments stable : clear implicits.

Ltac trans H := apply (trans H); let T := type of H in 
  match constr:(T) with
  | ?Cov _ ?a _ => clear a H; intros a H
  end.

Ltac etrans := match goal with
     | [ H : ?Cov _ ?a _  |- ?Cov _ ?a _ ] => try (trans H)
     end. 

Ltac join H1 H2 := let H := fresh H1 in
  pose proof (le_right H1 H2) as H; clear H1 H2.

Ltac ejoin := repeat match goal with
  | [ H1 : ?Cov _ ?a _, H2 : ?Cov _ ?a _  |- ?Cov _ ?a _ ] => join H1 H2
  end.

Module PreISpace.
Record t :=
  { S :> PreOrder
  ; Ix : S -> Type
    (** For each observable property, a type of indexes or addresses or names of
        covering axioms for subsets of basic opens which conspire to cover
        the given observable property. This type should be inductively
        generated, or similarly phrased, the axioms should be countable *)
  ; C : forall (s : S), Ix s -> Subset S 
    (** For each axiom index/name/address, this gives us a subset of basic
        opens whose union covers the given basic open *)
  }.
End PreISpace.
Coercion PreISpace.S : PreISpace.t >-> PreOrder.

Section IGDefn.

Local Open Scope FT.

Context {A : PreISpace.t}.
(** Inductively generated formal topologies. See section
    3 of [1]. *)

(** Given the axiom set [I] and [C], this generates the
    formal cover corresponding to that axiom set. *)
Inductive GCov (a : A) (U : Open A) : Type :=
  | grefl : U a -> GCov a U
  | gle_left : forall (b : A)
     , a <= b -> GCov b U -> GCov a U
  | ginfinity : forall (i : PreISpace.Ix A a),
     (forall u, PreISpace.C A a i u -> GCov u U) -> GCov a U.

Inductive GCovL (a : A) (U : Open A) : Type :=
  | glrefl : U a -> GCovL a U
  | glle_left : forall (b : A), a <= b -> GCovL b U -> GCovL a U
  | gle_infinity : forall (b : A) (i : PreISpace.Ix _ b)
    , a <= b -> (forall u, { u' : A & (PreISpace.C A b i u' * down A a u' u)%type } -> GCovL u U)
    -> GCovL a U.

Context {PO : PreO.t (le A)}.

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

Lemma gmonotone (a : A) (U V : Open A) :
  U ⊆ V -> GCov a U -> GCov a V.
Proof.
intros UV aU. induction aU.
- apply grefl. apply UV. assumption.
- eapply gle_left. eassumption. apply IHaU.
  assumption.
- eapply ginfinity. eauto.
Qed.

Lemma gmonotoneL a (U V : Open A) :
  U ⊆ V -> GCovL a U -> GCovL a V.
Proof.
intros UV aU. induction aU.
- apply glrefl. apply UV. assumption.
- eapply glle_left. eassumption. apply IHaU. assumption.
- eapply gle_infinity. eassumption. intros. apply X; eassumption.
Qed.

Lemma gsubset_equiv (U V : Open A) : U === V
  -> forall a, GCov a U <--> GCov a V.
Proof.
intros UV a. split; apply gmonotone; intros; rewrite UV; reflexivity.
Qed.

Class gtPos :=
  { gPos : Subset A
  ; gmono_le : forall a b, a <= b -> gPos a -> gPos b
  ; gmono_ax : forall a (i : PreISpace.Ix A a), gPos a -> Inhabited (PreISpace.C A a i ∩ gPos)
  ; gpositive : forall a U, (gPos a -> GCov a U) -> GCov a U
  }.

Definition toPreSpace : PreSpace.t :=
  {| PreSpace.S := A
   ; PreSpace.Cov := GCov |}.

Lemma GCov_Pos `{gtPos} : tPos toPreSpace.
Proof.
unshelve econstructor.
- exact gPos.
- intros. induction X0.
  + exists a. split; assumption.
  + apply IHX0. eapply gmono_le; eassumption.
  + destruct (gmono_ax a i X). destruct i0.
    eapply X0; eassumption.
- intros. apply gpositive. assumption.
Defined.

Lemma gall_Pos : 
  (forall a (i : PreISpace.Ix A a), Inhabited (PreISpace.C _ a i)) -> gtPos.
Proof.
intros H.
unshelve econstructor.
- exact (fun _ => True).
- simpl. auto.
- simpl. intros. destruct (H a i) as [x P].
  exists x. split. assumption. auto.
- simpl. intros. auto.
Qed.

Class localized := 
  IsLocalized : forall (a c : A),
  a <= c -> forall (i : PreISpace.Ix _ c),
  { j : PreISpace.Ix _ a  & 
  (forall s, PreISpace.C _ a j s -> { u : A & (PreISpace.C A c i u * down A a u s) } )}%type.

Context `{loc : localized}. 

(** Proposition 3.5 of [1] *)
Lemma le_infinity (a c : A) : a <= c ->
  forall (i : PreISpace.Ix _ c) (U : Open A), 
  (forall u v, PreISpace.C _ c i v -> down A a v u -> GCov u U)
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

Lemma GCov_stable : stable toPreSpace.
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
Instance GCov_formtop : t toPreSpace.
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

Arguments localized : clear implicits.
Arguments GCov : clear implicits.
Arguments GCovL : clear implicits.
Arguments gtPos : clear implicits.
Arguments toPreSpace : clear implicits.

Coercion toPreSpace : PreISpace.t >-> PreSpace.t.

Section AxiomSetRefine.

Context {A : PreOrder}.
Context {PO : PreO.t (le A)}.

Definition AxiomSetRefine {I I' : A -> Type} 
  (C : forall s, I s -> Open A) (C' : forall s, I' s -> Open A) :=
  forall s (i : I s), { j : I' s  &  C s i === C' s j }.

Definition SpaceWith I C := PreISpace.Build_t A I C.

Lemma AxRefineCovL {I I'} (C : forall s, I s -> Open A) 
  (C' : forall s, I' s -> Open A) :
  AxiomSetRefine C C' -> forall a U, GCovL (SpaceWith I C)  a U 
                             -> GCovL (SpaceWith I' C') a U.
Proof.
intros CC' a U aU. unfold AxiomSetRefine in CC'.
induction aU.
- apply glrefl. assumption.
- simpl in b. apply glle_left with b; assumption.
- destruct (CC' b i). simpl in *.
  apply gle_infinity with b x. assumption.
  intros.  destruct X0 as (u' & Gbxu' & downau'u).
  apply X. exists u'. split. apply s. apply Gbxu'. assumption.
Qed.

Lemma AxRefineCov {I I'} (C : forall s, I s -> Open A) 
  (C' : forall s, I' s -> Open A) :
  AxiomSetRefine C C' -> forall a U, GCov (SpaceWith I C) a U -> GCov (SpaceWith I' C') a U.
Proof.
intros CC' a U aU. unfold AxiomSetRefine in CC'.
induction aU.
- apply grefl. assumption.
- simpl in *. apply gle_left with b; assumption.
- destruct (CC' a i).
  apply ginfinity with x.
  intros. apply X. apply s. assumption. 
Qed.

End AxiomSetRefine.

(*
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
*)

Section Localize.

Variable (A : PreISpace.t).

Inductive IxL {a : A} : Type :=
  | MkIxL : forall c (ix : PreISpace.Ix A c), a <= c -> IxL.

Arguments IxL : clear implicits.

Definition CL (a : A) (i : IxL a) : Subset A :=
  match i with
  | MkIxL c k _ => fun z => { u : A & PreISpace.C A c k u * down A a u z }%type
  end.

Definition Localized : PreISpace.t :=
  {| PreISpace.S := A
   ; PreISpace.Ix := IxL
   ; PreISpace.C := CL
  |}.

Context {PO : PreO.t (le A)}.

Local Instance Llocalized : localized Localized.
Proof.
unfold localized.
intros. destruct i. simpl in *.
exists (MkIxL c0 ix (PreO.le_trans _ _ _ X l)).
simpl. intros s X'.
destruct X' as (u & Cxiu & downaus).
exists s. split. exists u. split. assumption. unfold down in *.
  destruct downaus.
  split. transitivity a; assumption. assumption.
  destruct downaus.
  split; [assumption | reflexivity].
Qed.

Theorem cov_equiv : GCovL A ==== GCov Localized.
Proof.
intros a U. split; intros H.
- induction H.
  + apply grefl. assumption.
  + eapply gle_left; eassumption.
  + pose (MkIxL b i l : IxL a).
  apply ginfinity with i0.
  intros u X0. apply X.
  unfold CL in X0.
  simpl in X0. destruct X0 as (u' & Caiu' & (ua & uu')).
  exists u'. split. assumption. split; eassumption.
- induction H.
  + apply glrefl. assumption.
  + eapply glle_left; eassumption.
  + destruct i as [c i ac].
    simpl in *.
    apply (gle_infinity a _ c i). assumption.
    intros. auto.
Qed.

Local Instance GCov_Proper : Proper (le A --> Included ==> arrow)
  (GCov Localized). 
Proof. 
unshelve eapply (@Cov_Proper (@toPreSpace Localized)). 
eapply GCov_formtop.
Qed.

Theorem GCovL_formtop : t (@toPreSpace Localized).
Proof.
apply GCov_formtop.
Qed.

End Localize.

Arguments IxL : clear implicits.
