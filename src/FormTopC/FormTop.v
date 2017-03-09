Require Import 
  Algebra.OrderC
  Algebra.FrameC
  Algebra.SetsC
  CMorphisms
  CRelationClasses
  Prob.StdLib.
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

Definition Open@{A P} (A : PreOrder@{A P}) := Subset@{A P} A.
Delimit Scope FT_scope with FT.

Local Open Scope FT.

Set Printing Universes.

Definition downset@{A P} {A : PreOrder@{A P}} (U : Open A) : Open A :=
  union U (fun x y => y <= x).

Notation "⇓ U" := (downset U) (at level 30).

Definition down@{A P} {A : PreOrder@{A P}} (U V : Open A) : Open A :=
  ⇓ U ∩ ⇓ V.

Infix "↓" := (down) (at level 30).

Section Down_Props.
Context {A : PreOrder}.

Lemma downset_included {PO : PreO.t (le A)} : forall (V : Open A),
   V ⊆ ⇓ V.
Proof.
intros. unfold Included, pointwise_rel, arrow; intros.
econstructor. eassumption. reflexivity.
Qed.

Lemma downset_Proper_impl : Proper (Included ==> Included)
  (@downset A).
Proof.
unfold Proper, respectful.
intros. unfold Included, In, pointwise_rel, arrow.
firstorder. unfold downset. exists a0. apply X. assumption. assumption.
Qed.

Instance downset_Proper : Proper (Same_set ==> Same_set) (@downset A).
Proof.
unfold Proper, respectful. intros.
apply Same_set_Included in X. destruct X. 
apply Included_Same_set; apply downset_Proper_impl; try assumption;
  unfold respectful, arrow; intros; subst.
Qed.

Context {PO : PreO.t (le A)}.

Lemma down_intersection {U V : Subset A} :
  U ∩ V ⊆ U ↓ V.
Proof.
apply Included_impl. intros. destruct X.
unfold down. split; exists x;
  (assumption || reflexivity).
Qed.

Lemma downset_down_incl {U V : Subset A} :
  ⇓ (U ↓ V) === ⇓ (U ∩ V).
Proof.
Abort.

Lemma downset_down {U V : Subset A} :
  ⇓ (U ↓ V) === U ↓ V.
Proof.
apply Included_Same_set.
- unfold down. apply Intersection_Included.
  + apply Included_impl; intros. destruct X.
    destruct i. destruct d.
    eexists. eassumption. etransitivity; eassumption.
  + apply Included_impl; intros. destruct X.
    destruct i. destruct d0. eexists. eassumption.
    etransitivity; eassumption.
- apply downset_included.
Qed.

Lemma down_assoc {U V W : Subset A} :
  (U ↓ V) ↓ W === U ↓ (V ↓ W).
Proof.
unfold down at 1 3.
rewrite !downset_down. unfold down.
symmetry.
apply Intersection_assoc.
Qed.

Lemma le_down {a b : A} : a <=[A] b
  -> eq a ↓ eq b === ⇓ (eq a).
Proof.
intros H. apply Included_Same_set.
- unfold down. apply Intersection_Included_l.
- apply Included_impl. intros. destruct X.
  unfold In in i. subst. split.
  eexists. reflexivity. eassumption. eexists.
  reflexivity. etransitivity; eassumption.
Qed.

Lemma down_eq {a b : A}
 : forall c : A, ((c <= a) * (c <= b))%type <--> (eq a ↓ eq b) c.
Proof.
intros. split; intros. 
- destruct X. split; (eexists; [reflexivity | eassumption]).
- destruct X. destruct d, d0. unfold In in *. subst. 
  split; assumption. 
Qed.

Lemma down_Proper {U V U' V' : Subset A} :
  U ⊆ U' -> V ⊆ V' -> U ↓ V ⊆ U' ↓ V'.
Proof.
intros HU HV. unfold down.
apply Intersection_Included.
- etransitivity. apply Intersection_Included_l. 
  apply downset_Proper_impl. assumption.
- etransitivity. apply Intersection_Included_r.
  apply downset_Proper_impl; assumption.
Qed.

Lemma down_comm {U V : Subset A}
  : U ↓ V === V ↓ U.
Proof.
unfold down. apply Intersection_comm.
Qed.

End Down_Props.

Module PreSpace.
Record t@{A P X} :=
  { S :> PreOrder@{A P}
  ; Cov : S -> Open@{A P} S -> Type@{X} }.
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
Universes A P X.
Context {A : PreSpace.t@{A P X}}.

Set Printing Universes.

(** Definition 2.1 of [1].
    Definition of when the [Cov] relation is indeed a formal cover.
    Here, the [Cov] relation means the little triangle that is
    seen in the literature. *)
Class t@{} : Type :=
  { refl : forall (a : PreSpace.S A) (U : Open A), In U a -> a <| U
  ; trans : forall {a : PreSpace.S A} {U : Open A}, a <| U 
     -> forall V, U <<| V
     -> a <| V
  ; le_left : forall (a b : PreSpace.S A) (U : Open A)
     , a <= b -> b <| U -> a <| U
  ; le_right : forall {a : PreSpace.S A} {U V : Open A}
    , a <| U -> a <| V
    -> a <| U ↓ V
  }.

Arguments t : clear implicits.

(** Definition of a formal cover that also has a positivity predicate. *)
(** We bundle the positivity predicate, because if there is one,
    it's unique. *)
Class tPos@{} :=
  { Pos : Subset@{A P} A
  ; mono : forall a U, Pos a -> a <| U -> Inhabited@{A P} (U ∩ Pos)
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
    c <| U ↓ V.

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
Record t@{A P I} :=
  { S :> PreOrder@{A P}
  ; Ix : S -> Type@{I}
    (** For each observable property, a type of indexes or addresses or names of
        covering axioms for subsets of basic opens which conspire to cover
        the given observable property. This type should be inductively
        generated, or similarly phrased, the axioms should be countable *)
  ; C : forall (s : S), Ix s -> Open@{A P} S 
    (** For each axiom index/name/address, this gives us a subset of basic
        opens whose union covers the given basic open *)
  }.
End PreISpace.
Coercion PreISpace.S : PreISpace.t >-> PreOrder.

Section IGDefn.

Local Open Scope FT.

Universes A P I API.
Context {A : PreISpace.t@{A P I}}.
(** Inductively generated formal topologies. See section
    3 of [1]. *)

(** Given the axiom set [I] and [C], this generates the
    formal cover corresponding to that axiom set. *)
Inductive GCov@{} (a : A) (U : Open@{A P} A) : Type :=
  | grefl : U a -> GCov a U
  | gle_left : forall (b : A)
     , a <= b -> GCov b U -> GCov a U
  | ginfinity : forall (i : PreISpace.Ix A a),
     (forall u, PreISpace.C A a i u -> GCov u U) -> GCov a U.

Inductive GCovL@{} (a : A) (U : Open@{A P} A) : Type :=
  | glrefl : U a -> GCovL a U
  | glle_left : forall (b : A), a <= b -> GCovL b U -> GCovL a U
  | gle_infinity : forall (b : A) (i : PreISpace.Ix _ b)
    , a <= b
    -> (forall u, (eq a ↓ PreISpace.C A b i) u -> GCovL u U)
    -> GCovL a U.

Context {PO : PreO.t@{A P} (le A)}.

Axiom undefined : forall A, A.

Lemma Lmore_MUniv a U : GCov a U -> GCovL a U.
Proof.
intros aU. induction aU.
- apply glrefl. assumption.
- apply glle_left with b; assumption.
- apply (gle_infinity a _ a i (PreO.le_refl _)).
  intros. destruct X0. destruct d, d0.
  apply glle_left with a1. assumption. apply X.
  assumption.
Qed.

Definition Lmore@{} a U : GCov a U -> GCovL a U
  := Lmore_MUniv@{API} a U.

Lemma gmonotone_MUniv (a : A) (U V : Open@{A P} A) :
  U ⊆ V -> GCov a U -> GCov a V.
Proof.
intros UV aU. induction aU.
- apply grefl. apply UV. assumption.
- eapply gle_left. eassumption. apply IHaU.
  assumption.
- eapply ginfinity. eauto.
Qed.

Definition gmonotone@{} (a : A) (U V : Open@{A P} A) :
  U ⊆ V -> GCov a U -> GCov a V
  := gmonotone_MUniv@{API} a U V.

Lemma gmonotoneL_MUniv a (U V : Open A) :
  U ⊆ V -> GCovL a U -> GCovL a V.
Proof.
intros UV aU. induction aU.
- apply glrefl. apply UV. assumption.
- eapply glle_left. eassumption. apply IHaU. assumption.
- eapply gle_infinity. eassumption. intros. apply X; eassumption.
Qed.

Definition gmonotoneL@{} a (U V : Open A) :
  U ⊆ V -> GCovL a U -> GCovL a V
  := gmonotoneL_MUniv@{API} a U V.

Ltac equivalence := repeat (reflexivity || assumption || symmetry).

Lemma gsubset_equiv_MUniv (U V : Open A) : U === V
  -> forall a, GCov a U <--> GCov a V.
Proof.
intros UV a. split; apply gmonotone; intros; 
  apply (Same_set_Included@{A P API});
  equivalence.
Qed.

Definition gsubset_equiv (U V : Open A) : U === V
  -> forall a, GCov a U <--> GCov a V
  := gsubset_equiv_MUniv@{API API} U V.

Class gtPos@{} :=
  { gPos : Subset@{A P} A
  ; gmono_le : forall a b, a <= b -> gPos a -> gPos b
  ; gmono_ax : forall b (i : PreISpace.Ix A b), forall a, a <= b ->
    gPos a -> Inhabited@{A P} ((eq a ↓ PreISpace.C A b i) ∩ gPos)
  ; gpositive : forall a U, (gPos a -> GCovL a U) -> GCovL a U
  }.

Definition toPreSpace@{} : PreSpace.t@{A P I} :=
  {| PreSpace.S := A
   ; PreSpace.Cov := GCovL |}.

Definition toPreSpaceUL@{} : PreSpace.t@{A P I} :=
  {| PreSpace.S := A
   ; PreSpace.Cov := GCov
  |}.

Lemma GCov_Pos@{} `{gtPos} : tPos toPreSpace.
Proof.
unshelve econstructor.
- exact gPos.
- intros. induction X0.
  + exists a. split; assumption.
  + apply IHX0. eapply gmono_le; eassumption.
  + destruct (gmono_ax b i a l X). destruct i0.
    eapply X0. 2: eapply g0.  assumption.
- intros. apply gpositive. assumption.
Defined.

Lemma gall_Pos@{} : 
  (forall b (i : PreISpace.Ix A b), forall a, a <= b ->
   Inhabited (eq a ↓ PreISpace.C _ b i)) -> gtPos.
Proof.
intros H.
unshelve econstructor.
- exact (fun _ => True).
- simpl. auto.
- simpl. intros. destruct (H b i a X) as [x P].
  exists x. split. assumption. auto.
- simpl. intros. auto.
Qed.

Class localized@{} := 
  IsLocalized : forall (a c : A),
  a <= c -> forall (i : PreISpace.Ix _ c),
  { j : PreISpace.Ix _ a  & 
  (PreISpace.C _ a j ⊆ eq a ↓ PreISpace.C _ c i)}%type.

Context {loc : localized}. 

(** Proposition 3.5 of [1] *)
Lemma le_infinity@{} (a c : A) : a <= c
  -> forall (i : PreISpace.Ix _ c) (U : Open A)
  , (forall u, (eq a ↓ PreISpace.C A c i) u -> GCov u U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros ac i U H. 
destruct (loc a c ac i) as (i' & s).
apply (ginfinity _ _ i').
intros u Caxu.
specialize (s u Caxu).
eapply H. assumption.
Qed.

Lemma GCov_stable@{} : stable toPreSpaceUL.
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
    destruct loc'. destruct d, d0.
    unfold In in i0. subst.
    eapply X. eassumption.
    transitivity a1; eassumption. assumption.
- intros c ca cb. 
  apply IHaU. transitivity a; eassumption. assumption.
- intros c ca cb. pose proof (loc c a ca i) as loc1.
  destruct loc1 as [j loc'].
  apply (ginfinity _ _ j).

  intros. specialize (loc' u X0).
  destruct loc'. destruct d, d0. unfold In in i0. subst.
  eapply X. eassumption. assumption.
  transitivity a0; assumption.
Qed.

(** Theorem 3.6 of [1].
    In fact, the formal cover that we defined based on the axiom set 
    indeed satistifes the requirements of being a formal topology. *)
Instance GCov_formtop@{} : t toPreSpaceUL.
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
  intros.
  apply X. destruct X0. destruct d, d0. 
  unfold In in i0. subst. split. exists a0. reflexivity. 
  apply l0. exists a1. apply s; assumption. assumption.
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


Lemma t_Proper@{A P I AP API} {X : PreOrder@{A P}} (Cov Cov' : X -> Open@{A P} X -> Type@{I})
  : RelSame@{A AP I API} Cov Cov' -> t (PreSpace.Build_t X Cov) -> t (PreSpace.Build_t X Cov').
Proof.
intros H tC.
constructor; simpl; intros.
- apply H. apply (@refl _ tC). assumption.
- apply H. apply H in X0.
  apply (@trans _ tC a U X0 V).
  simpl. intros. apply H. apply X1. assumption.
- apply H. apply H in X1.
  apply (@le_left _ tC a b U X0 X1).
- apply H. apply H in X0. apply H in X1.
  apply (@le_right _ tC a U V X0 X1).
Qed.


Section Localize.

Universes A P I API.
Variable (A : PreISpace.t@{A P I}).

Inductive IxL@{} {a : A} : Type :=
  | MkIxL : forall c (ix : PreISpace.Ix A c), a <= c -> IxL.

Arguments IxL : clear implicits.

Definition CL@{} (a : A) (i : IxL a) : Subset A :=
  match i with
  | MkIxL c k _ => eq a ↓ PreISpace.C _ c k
  end.

Definition Localized@{} : PreISpace.t@{A P I} :=
  {| PreISpace.S := A
   ; PreISpace.Ix := IxL
   ; PreISpace.C := CL
  |}.

Context {PO : PreO.t@{A P} (le A)}.



Lemma Llocalized_UMore : localized@{A P I API} Localized.
Proof.
unfold localized.
intros. destruct i. simpl in *.
exists (MkIxL c0 ix (PreO.le_trans _ _ _ X l)).
etransitivity.
Focus 2.
eapply Same_set_Included. symmetry. eapply down_assoc.
simpl. apply down_Proper.
apply Included_impl. intros. subst.
split. exists x; reflexivity. exists c. reflexivity.
assumption. reflexivity.
Qed.

Instance Llocalized@{} : localized Localized :=
  Llocalized_UMore@{API API API}.

Theorem cov_equiv_UMore : GCovL A ==== GCov Localized.
Proof.
intros a U. split; intros H.
- induction H.
  + apply grefl. assumption.
  + eapply gle_left; eassumption.
  + pose (MkIxL b i l : IxL a).
  apply ginfinity with i0.
  intros u X0. apply X.
  unfold CL in X0.
  simpl in X0. assumption.
- induction H.
  + apply glrefl. assumption.
  + eapply glle_left; eassumption.
  + destruct i as [c i ac].
    simpl in *.
    apply (gle_infinity a _ c i). assumption.
    intros. auto.
Qed.

Definition cov_equiv : GCovL A ==== GCov Localized
  := cov_equiv_UMore@{API API API API API}.


Local Instance GCov_Proper : Proper (le A --> Included ==> arrow)
  (GCov Localized). 
Proof. 
unshelve eapply (@Cov_Proper (@toPreSpaceUL Localized)). 
eapply GCov_formtop.
Qed.

Theorem Localized_formtop@{} : t (@toPreSpaceUL@{A P I API} Localized).
Proof.
apply GCov_formtop.
Qed.

Theorem GCovL_formtop_UMore : t (@toPreSpace@{A P I API} A).
Proof.
eapply t_Proper@{A P I API API}. 2: apply Localized_formtop.
symmetry. apply cov_equiv.
Qed.

Definition GCovL_formtop@{API'} : t (@toPreSpace@{A P I API} A)
  := GCovL_formtop_UMore@{API API' API'}.


End Localize.

Arguments IxL : clear implicits.
