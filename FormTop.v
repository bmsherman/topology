Require Import Frame.
Set Asymmetric Patterns.

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
Module FormTop.

Generalizable All Variables.

Section Defn.

(** We assume we have some type [S] equipped
    with a partial order. *)
Context {S} {le : S -> S -> Prop} {PO : PreO.t S le}.

(** States that [c] is less than or equal to the minimum of
    [a] and [b]. *)
Definition down (a b c : S) : Prop :=
  le c a /\ le c b.

(** Definition 2.1 of [1].
    Definition of when the [Cov] relation is indeed a formal cover.
    Here, the [Cov] relation means the little triangle that is
    seen in the literature. *)
Class t { Cov : S -> (S -> Prop) -> Prop } :=
  { refl : forall (a : S) (U : S -> Prop), U a -> Cov a U
  ; trans : forall (a : S) (U V : S -> Prop), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; le_left : forall (a b : S) (U : S -> Prop)
     , le a b -> Cov b U -> Cov a U
  ; le_right : forall (a : S) (U V : S -> Prop)
    , Cov a U -> Cov a V
    -> Cov a (fun c => exists u v, U u /\ V v /\ down u v c)
  }.

Arguments t : clear implicits.

(** Definition of a formal cover that also has a positivity predicate. *)
Record tPos { Cov : S -> (S -> Prop) -> Prop } {Pos : S -> Prop} :=
  { cov :> t Cov
  ; mono : forall a U, Pos a -> Cov a U -> exists b, U b /\ Pos b
  ; positive : forall a U, (Pos a -> Cov a U) -> Cov a U
  }.

Arguments tPos : clear implicits.

Lemma monotone {Cov} : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a -> V a)
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. eauto using trans, refl.
Qed.

Lemma subset_equiv {Cov} : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, Cov a U <-> Cov a V.
Proof.
intros. split; apply monotone; firstorder.
Qed.

(** Inductively generated formal topologies. See section
    3 of [1]. *)

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (S -> Prop).

Definition stable (Cov : S -> (S -> Prop) -> Prop) :=
  forall a b U V, Cov a U -> Cov b V
  -> forall c, le c a -> le c b ->
    Cov c (fun s => exists u v, U u /\ V v /\ down u v s).

Definition localized := forall (a c : S),
  le a c -> forall (i : I c),
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ down a u s).

(** Given the axiom set [I] and [C], this generates the
    formal cover corresponding to that axiom set. *)
Inductive GCov : S -> (S -> Prop) -> Prop :=
  | grefl : forall (a : S) (U : S -> Prop), U a -> GCov a U
  | gle_left : forall (a b : S) (U : S -> Prop)
     , le a b -> GCov b U -> GCov a U
  | ginfinity : forall (a : S) (i : I a) (U : S -> Prop),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Hypothesis loc : localized. 

Lemma gmonotone : forall (a : S) (U V : S -> Prop),
  (forall u, U u -> V u) -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gle_left. eassumption. apply IHGCov.
  assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gsubset_equiv : forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
Qed.

(** Proposition 3.5 of [1] *)
Lemma le_infinity : forall (a c : S), le a c ->
  forall (i : I c) (U : S -> Prop), 
  (forall u v, C c i v -> down a v u -> GCov u U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros. destruct (loc a c H i).
apply (ginfinity _ x).
intros.
specialize (H1 u H2).
destruct H1. destruct H1.
eapply H0. 2:eassumption. assumption.
Qed.

Lemma GCov_stable : stable GCov.
Proof.
unfold localized in loc.
unfold stable. intros. generalize dependent c.
induction H.
- induction H0; intros.
  + apply grefl. exists a. exists a0. unfold down. intuition.
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
Theorem GCov_formtop : t GCov.
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


End Defn.

Section Localize.

Context {S : Type} {le : S -> S -> Prop}.
Variable (PO : PreO.t S le).
Variable (Ix : S -> Type) (C : forall s, Ix s -> (S -> Prop)).

Definition IxL (a : S) := 
  { i : sigT (fun c => Ix c) | match i with
    | existT c k => le a c end }.

Definition CL (a : S) : IxL a -> S -> Prop := 
  fun i => match i with
  | exist (existT c k) _ => fun z => exists u, C c k u /\ @down _ le a u z
  end.

Theorem Llocalized : @localized _ le IxL CL.
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

End Localize.

End FormTop.

Arguments FormTop.t {_} _ _.





(** Formal topologies presented with a minimum operation
    rather than just a partial order. Most of the material
    is pretty similar to the module above.

    One good reference for this presentation is

    [2]
    Formal topology and domains.
    Giovanni Sambin.
    2000.
    http://www.math.unipd.it/~sambin/txt/ftd.pdf
 *)
Module FormTopM.

Generalizable All Variables.

Section Defn.
Context {S} {dotS : S -> S -> S}.

Definition ops : MeetLat.Ops S :=
  {| MeetLat.le := fun x y => dotS x y = x
   ; MeetLat.eq := eq
   ; MeetLat.min := dotS
  |}.

Instance ops' : MeetLat.Ops S := ops.

Definition le := MeetLat.le.
Definition dot := MeetLat.min.

Context {ML : @MeetLat.t S ops}.

Require Import SetoidClass Morphisms.

Class t { Cov : S -> (S -> Prop) -> Prop } :=
  { refl : forall (a : S) (U : S -> Prop), U a -> Cov a U
  ; trans : forall (a : S) (U V : S -> Prop), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; dot_left : forall (a b : S) (U : S -> Prop)
     , Cov a U -> Cov (dot a b) U
  ; dot_right : forall (a : S) (U V : S -> Prop)
    , Cov a U -> Cov a V
    -> Cov a (fun c => exists u v, U u /\ V v /\ MeetLat.eq c (dot u v))
  }.

Arguments t : clear implicits.

Lemma monotone {Cov} : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a -> V a)
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. eauto using trans, refl.
Qed.

Lemma subset_equiv {Cov} : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, Cov a U <-> Cov a V.
Proof.
intros. split; apply monotone; firstorder.
Qed.

Definition asFormTop `(tCov : t Cov) : FormTop.t le Cov.
Proof.
constructor; intros.
- apply refl. assumption.
- eapply trans. eassumption. assumption.
- assert (MeetLat.min a b = a). apply (PO.le_antisym (le := MeetLat.le)). 
  + apply (@PreO.min_l _ _ _ b).
    apply MeetLat.min_ok.
  + apply (@PreO.min_greatest _ _ a b).
    apply MeetLat.min_ok. apply PreO.le_refl. assumption.
  + rewrite <- H1. rewrite MeetLat.min_comm. 
    apply dot_left. assumption. 
- pose (UV := (fun c => exists u v, U u /\ V v /\ MeetLat.eq c (MeetLat.min u v))).
  apply monotone with UV. assumption.
  unfold UV. intros.
  destruct H1 as [u [v [Uv [Vv downP]]]].
  exists u. exists v. split. assumption. split. assumption.
  unfold FormTop.down. repeat rewrite downP.
  split. apply MeetLat.min_ok. apply MeetLat.min_ok. 
  unfold UV. apply dot_right; assumption.
Qed.

(** Inductively generated formal topologies for this formulation. *)

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (S -> Prop).

Definition stable (Cov : S -> (S -> Prop) -> Prop) :=
  forall a b U V, Cov a U -> Cov b V
  -> Cov (dot a b) (fun s => exists u v, U u /\ V v /\ MeetLat.eq s (dot u v)).

Definition localized := forall (b c : S),
  forall (i : I c), let a := dot b c in
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ MeetLat.le s (dot a u)).

Inductive GCov : S -> (S -> Prop) -> Prop :=
  | grefl : forall (a : S) (U : S -> Prop), U a -> GCov a U
  | gdot_left : forall (a b : S) (U : S -> Prop)
     , GCov a U -> GCov (dot a b) U
  | ginfinity : forall (a : S) (i : I a) (U : S -> Prop),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Hypothesis loc : localized.

Lemma localized_asFormTop : @FormTop.localized S MeetLat.le I C.
Proof.
unfold FormTop.localized, localized in *.
intros.
specialize (loc a c i).
unfold dot, MeetLat.min in *. simpl in *.
rewrite H in loc.
destruct loc.
exists x. intros. specialize (H0 s H1).
destruct H0. exists x0. destruct H0. split. assumption.
unfold FormTop.down.
unfold dot in x. simpl in x.
change dotS with (MeetLat.min) in *.
change (@eq S) with (MeetLat.eq) in *.
split.
apply PO.le_antisym. apply MeetLat.min_l. apply MeetLat.min_ok.
apply PreO.le_refl. rewrite <- H2. rewrite MeetLat.min_comm.
rewrite <- MeetLat.min_assoc. apply MeetLat.min_l.
apply PO.le_antisym. apply MeetLat.min_l. apply MeetLat.min_ok.
apply PreO.le_refl. rewrite <- H2. rewrite MeetLat.min_assoc.
apply MeetLat.min_r.
Qed.

Lemma gmonotone : forall (a : S) (U V : S -> Prop),
  (forall u, U u -> V u) -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gdot_left. apply IHGCov. assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gsubset_equiv : forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
Qed.

Lemma dot_infinity : forall (b c : S), let a := dot b c in
  forall (i : I c) (U : S -> Prop), 
  (forall v, C c i v -> GCov (dot a v) U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros. destruct (loc b c i).
apply (ginfinity _ x).
intros.
specialize (H0 u H1).
destruct H0. destruct H0.
simpl in H2. 
replace dotS with MeetLat.min in H2 by reflexivity.
rewrite <- H2.
rewrite MeetLat.min_comm.
apply gdot_left. 
apply H. assumption.
Qed.


Lemma GCov_stable : stable GCov.
Proof.
unfold localized in loc.
unfold stable. intros.
induction H.
- induction H0; intros.
  + apply grefl. exists a. exists a0. intuition.
  + unfold dot. rewrite MeetLat.min_assoc. 
    apply gdot_left. apply IHGCov.
  + pose proof (loc a a0 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ j).

    intros. specialize (loc' u H2).
    destruct loc'. destruct H3.
    simpl in H4.
    replace dotS with dot in H4 by reflexivity.
    rewrite <- H4. unfold dot.
    rewrite MeetLat.min_comm.
    apply gdot_left.
    rewrite <- MeetLat.min_assoc.
    rewrite (MeetLat.min_comm a0 x).
    rewrite MeetLat.min_assoc.
    apply gdot_left. 
    apply H1. assumption.
- intros. unfold dot. rewrite <- MeetLat.min_assoc.
  rewrite (MeetLat.min_comm b0 b).
  rewrite MeetLat.min_assoc. apply gdot_left.
  apply IHGCov.
- intros. pose proof (loc b a i) as loc1.
  destruct loc1 as [j loc'].
  unfold dot. rewrite MeetLat.min_comm.
  apply (ginfinity _ j).

  intros. specialize (loc' u H2).
  destruct loc'. destruct H3. simpl in H4.

 replace dotS with dot in H4 by reflexivity.
    rewrite <- H4. unfold dot.
    rewrite MeetLat.min_comm.
    apply gdot_left.
    rewrite <- MeetLat.min_assoc.
    rewrite (MeetLat.min_comm a x).
    rewrite MeetLat.min_assoc.
    apply gdot_left.
    rewrite MeetLat.min_comm.
    apply H1. assumption.  
Qed.

Theorem GCov_formtop : t GCov.
Proof.
unfold localized in loc.
constructor.
- apply grefl.
- intros. induction H.
  + apply H0. assumption.
  + eapply gdot_left. apply IHGCov. apply H0.
  + apply (ginfinity _ i). intros. apply H1; assumption.
- apply gdot_left.
- intros.
  pose proof GCov_stable as stab.
  unfold stable in stab.
  pose proof GCov_stable.
  replace a with (dot a a).
  eapply H1. eassumption. eassumption.
  pose proof (MeetLat.min_idempotent a) as ida.
  simpl in ida. apply ida.
Qed.
End Defn.

End FormTopM.

(** A definition of commutative and idempotent semigroups.
    This is effectively a semi-lattice (it can be a join semi-lattice
    or a meet semi-lattice depending on your attitude) defined
    solely in terms of its min or max operation.
*)
Module CommIdemSG.

Generalizable All Variables.

Require Import SetoidClass Coq.Classes.Morphisms.

(** [dot] is a binary operation which is commutative, idempotent, and
    associative. It is effectively a max or min. *)
Class t {A} {eq : A -> A -> Prop} {dot : A -> A -> A} :=
  { eq_equiv :> Equivalence eq
  ; dot_proper :> Proper (eq ==> eq ==> eq) dot
  ; dot_idempotent : forall a, eq (dot a a) a
  ; dot_comm : forall a b, eq (dot a b) (dot b a)
  ; dot_assoc : forall a b c, eq (dot a (dot b c)) (dot (dot a b) c)
  }.

Arguments t : clear implicits.

Section Facts.
Context `{tA : t A eql dot}.

(** Here we define a "<=" relation which makes the [dot] a
    [min] operation for a meet semi-lattice *)
Definition ops : MeetLat.Ops A :=
  {| MeetLat.le := fun x y => eql (dot x y) x
   ; MeetLat.eq := eql
   ; MeetLat.min := dot
  |}.

Instance ops' : MeetLat.Ops A := ops.

(** Next, we prove successively, that these definitions using
    the [dot] operator indeed define a preorder, a partial order,
    and finally a meet semi-lattice. *)
Theorem asPreO : PreO.t A MeetLat.le.
Proof.
constructor; simpl; intros.
- apply dot_idempotent.
- rewrite <- H. rewrite <- H0 at 2.
  rewrite dot_assoc. reflexivity.
Qed.

Theorem asPO : PO.t A MeetLat.le eql.
Proof.
constructor.
- apply asPreO.
- repeat intro; simpl; split; intros. 
  rewrite <- H, <- H0. assumption.
  rewrite H, H0. assumption.
- simpl. intros. rewrite <- H. rewrite <- H0 at 2.
  rewrite dot_comm. reflexivity.
Qed.

Instance asMeetLat : MeetLat.t A ops.
Proof.
constructor. 
- apply asPO.
- solve_proper.
- intros. constructor; simpl; intros.
  + rewrite dot_comm. rewrite dot_assoc.
    rewrite dot_idempotent. reflexivity.
  + rewrite <- dot_assoc. rewrite dot_idempotent.
    reflexivity.
  + rewrite <- H at 2. rewrite <- H0 at 2.
    rewrite (dot_comm l r). rewrite dot_assoc.
    reflexivity.
Qed.

End Facts.
End CommIdemSG.

(** Information bases, which are the predicative versions of
    Scott domains. Perhaps, see Definition 1.9 of [2].
    Though my formulation is a little different; I build off
    of a pre-existing notion of a meet semi-lattice.

    Also, I directly show that this formal topology is
    inductively generated by generating it with an axiom set. *)
Module InfoBase. 
Section InfoBase.

Generalizable All Variables.

Context {S : Type}.

Hypothesis ops : MeetLat.Ops S.
Let dot := MeetLat.min. 
Hypothesis ML : MeetLat.t S ops.

(** The axiom set essentially says that if [s <= t], then
    [s] is covered by the singleton set [{t}]. *)
Definition Ix (s : S) : Type := { t : S & MeetLat.le s t }.
Definition C (s : S) (s' : Ix s) s'' : Prop := MeetLat.eq (projT1 s') s''.

(** This axiom set is localized. *)
Definition loc : @FormTop.localized S MeetLat.le Ix C.
Proof.
pose proof (@PO.t_equiv _ _ _ MeetLat.PO) as eqEquiv.
unfold FormTop.localized. intros. simpl.
unfold Ix, C in *.
destruct i. simpl.
assert (MeetLat.le a a).
apply PreO.le_refl.
exists (existT _ a H0).
intros.  simpl in *. 
exists x. split. reflexivity.
split. 
rewrite H1. apply PreO.le_refl.
rewrite <- H1.
eapply PreO.le_trans. eapply H. eassumption.
Qed.

(** The covering relation for information bases,
    which we derive from the axiom set above. *)
Definition Cov := @FormTop.GCov _ MeetLat.le Ix C.

(** The proof that [Cov] is a valid formal topology. *)
Instance isCov : @FormTop.t _ MeetLat.le Cov := 
  FormTop.GCov_formtop Ix C loc.

End InfoBase.
End InfoBase.

(** Here we intend to define the formal topology for the lower 
    non-negative real
    numbers, realizing that the lower real numbers can be made into 
    a formal topology by showing that they are an information base,
    taking the non-negative rational numbers, together with the
    minimum operation, as the meet semilattice for an information base.
*)
Module LowerR.
Require Import Qnn Coq.Classes.Morphisms SetoidClass.

(** In fact, the [Qnnmin] operation is a idempotent,
    commutative semigroup. I think I have a more generic proof of this
    somewhere in Frame.v?
*)
Theorem lowerCommSG : CommIdemSG.t Qnn eq Qnnmin.
Proof.
constructor; intros.
- apply eq_equivalence.
- solve_proper.
- apply Qnnle_antisym. 
  apply Qnnmin_r. apply Qnnmin_le_both; apply Qnnle_refl.
- apply Qnnle_antisym; apply Qnnmin_le_both;
    (apply Qnnmin_r || apply Qnnmin_l).
- apply Qnnle_antisym. apply Qnnmin_le_both.
  apply Qnnmin_le_both. apply Qnnmin_l. eapply Qnnle_trans.
  apply Qnnmin_r. apply Qnnmin_l. eapply Qnnle_trans. apply Qnnmin_r.
  apply Qnnmin_r.
  apply Qnnmin_le_both. eapply Qnnle_trans. apply Qnnmin_l.
  apply Qnnmin_l. apply Qnnmin_le_both. eapply Qnnle_trans.
  apply Qnnmin_l. apply Qnnmin_r. apply Qnnmin_r.
Qed.

Definition ops : MeetLat.Ops Qnn := 
  {| MeetLat.le := Qnnle ; MeetLat.eq := Logic.eq; MeetLat.min := Qnnmin |}.

Instance QnnML : MeetLat.t Qnn ops.
Proof.
constructor. constructor. constructor. 
- intros; apply Qnnle_refl.
- intros. eapply Qnnle_trans; eassumption.
- solve_proper.
- intros; apply Qnnle_antisym; assumption.
- solve_proper.
- intros. constructor.
  + apply Qnnmin_l.
  + apply Qnnmin_r.
  + intros. apply Qnnmin_le_both; assumption.
Qed.

Definition Ix := @InfoBase.Ix Qnn ops.
Definition C := @InfoBase.C Qnn ops.

Definition Cov := @InfoBase.Cov Qnn ops.

Definition isCov := @InfoBase.isCov Qnn ops QnnML.

End LowerR.

(** A definition of concrete topological spaces. These are formal topologies
    which are related to a type of points in the expected way, through a
    relation which I call [In]. See Definition 1.2 in [1]. Their relation
    which I call [In] looks like [||-], and they read as "lies in" or
    "forces".
*)
Module Concrete. 
Section Concrete.

Variable X S : Type.
Variable In : X -> S -> Prop.

Definition le := (map_op (fun (s : S) (x : X) => In x s)
            (pointwise_op (fun (_ : X) (P Q : Prop) => P -> Q))).

Instance SPO : PO.t S le _ := PO.map (fun s x => In x s) (PO.subset X).

Record t : Type :=
  { here : forall x, { s | In x s }
  ; local : forall (a b : S) x, In x a -> In x b 
          -> { c | In x c /\ @FormTop.down S (map_op (fun s x => In x s) L.le) a b c }
  }.

(** Every concrete topological space can be presented as an
    inductively generated formal topology. See Section 4.4
    of [1]. *)
Definition Ix (a : S) : Type := sig (fun (g : forall (x : X), In x a -> S) 
  => forall (x : X) (prf : In x a), In x (g x prf)).

Definition C (a : S) (i : Ix a) : S -> Prop := match i with
  | exist g _ => fun s => exists (x : X) (prf : In x a), s = g x prf
  end.

Theorem loc : t -> @FormTop.localized S (map_op (fun s x => In x s) L.le) Ix C.
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

Lemma LE_PO {A : Type} : PO.t (list A) LE eq.
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

Definition Cov := @FormTop.GCov S LE Ix C.

Theorem loc : @FormTop.localized S LE Ix C.
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
Variable CS : forall s, IS s -> (S -> Prop).
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
    @FormTop.localized S leS IS CS
  -> @FormTop.localized T leT IT CT
  -> @FormTop.localized (S * T) (prod_op leS leT) Ix C.
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
  simpl. split. assumption. assumption.
Qed.

Definition Cov := @FormTop.GCov (S * T) (prod_op leS leT) Ix C.

Hypothesis locS : @FormTop.localized S leS IS CS.
Hypothesis locT : @FormTop.localized T leT IT CT.

Theorem isCov : FormTop.t (prod_op leS leT) Cov.
Proof.
apply (@FormTop.GCov_formtop (S * T) (prod_op leS leT)
  PO Ix C (loc locS locT)).
Qed.

Let CovS := @FormTop.GCov S leS IS CS.
Let CovT := @FormTop.GCov T leT IT CT.

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

Context {CovS : S -> (S -> Prop) -> Prop}.
Context {CovT : T -> (T -> Prop) -> Prop}.

Record t {F : S -> T -> Prop} : Prop :=
  { here : forall a, CovS a (fun s => exists t, F s t)
  ; local : forall {a ab ac b c}, @FormTop.down _ leS ab ac a
    -> F ab b -> F ac c
    -> CovS a (fun s => exists bc, @FormTop.down _ leT b c bc /\ F s bc)
  ; cov : forall {a b} V, F a b -> CovT b V
    -> CovS a (fun s => exists t, V t /\ F s t)
 (* ; trans : forall a b U, CovS a U -> (forall x, U x -> F x b) -> F a b *)
  }.

Arguments t F : clear implicits.

End Cont.

Arguments t {S} leS {T} leT CovS CovT F : clear implicits.

Section Morph.

Context {S} `{POS : PreO.t S leS}.
Context `{FTS : FormTop.t S leS CovS}.

Definition id (s t : S) := s = t.

Theorem t_id : t leS leS CovS CovS id.
Proof.
constructor; intros; unfold id in *.
- eapply FormTop.refl. exists a. reflexivity.
- subst. apply FormTop.refl. exists a. tauto.
- subst. refine (FormTop.monotone FTS _ _ _ _ H0).
  firstorder.
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

Definition compose (F : S -> T -> Prop)
  (G : T -> U -> Prop) (s : S) (u : U) : Prop :=
    exists t, F s t /\ G t u.


Theorem t_compose : forall (F : S -> T -> Prop) (G : T -> U -> Prop),
    t leS leT CovS CovT F
  -> t leT leU CovT CovU G
  -> t leS leU CovS CovU (compose F G).
Proof.
intros. constructor.
- intros. pose proof (here H a).
  eapply FormTop.trans. eassumption.
  simpl. intros. destruct H2. 
  pose proof (here H0 x).
  pose proof (cov H _ H2 H3).
  refine (FormTop.monotone _ _ _ _ _ H4).
  intros. destruct H5 as [t1 [[u Gt1u] Fa0t1]].
  exists u. unfold compose. exists t1. split; assumption.
- intros. unfold compose in *.
  intros. 
  destruct H2 as [t1 [Fat1 Gt1b]]. 
  destruct H3 as [t2 [Fat2 Gt2b]].
  pose proof (local H H1 Fat1 Fat2).
  eapply FormTop.trans. apply H2.
  simpl. intros. destruct H3 as [bc [Fa'bc down]].
  pose proof (local H0 Fa'bc Gt1b Gt2b).
  apply (FormTop.monotone _)
  with (fun s => exists t' : T, (exists bc' : U, @FormTop.down _ leU b c bc' /\ G t' bc')
   /\ F s t'). firstorder.
  apply (cov H _ down H3).
- unfold compose. intros.
  destruct H1 as [t [Fat Gtb]].
  apply (FormTop.monotone _)
    with (fun s => exists t1 : T, (exists u : U, V u /\ G t1 u) /\ F s t1).
  firstorder.
  apply (cov H _ Fat).
  apply (cov H0 _ Gtb). assumption.
Qed.

End Morph.

Section Products. 
Context {S} `{POS : PreO.t S leS}.
Context {IS} {CS : forall (s : S), IS s -> (S -> Prop)}.
Variable locS : @FormTop.localized _ leS IS CS.
Let CovS := @FormTop.GCov _ leS IS CS.

Definition diagonal (p : S) (out : S * S) : Prop :=
  let (out1, out2) := out in leS p out1 /\ leS p out2.

Lemma t_diagonal : t leS (prod_op leS leS)
  CovS (@Product.Cov _ _ leS leS IS IS CS CS) diagonal.
Proof.
pose proof (FormTop.GCov_formtop IS CS locS) as FTS.
constructor; intros; unfold diagonal, CovS in *.
- apply FormTop.refl. exists (a, a). split; apply PreO.le_refl.
- destruct b, c. destruct H, H0, H1. subst. subst.
  apply FormTop.refl. exists (a, a). split.
  split; split; eauto using PreO.le_trans. 
  split; apply PreO.le_refl.
- generalize dependent a. induction H0; intros.
  + apply FormTop.refl. exists a. 
    split. assumption. assumption. 
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
Variable locT : @FormTop.localized _ leT IT CT.
Let CovT := @FormTop.GCov _ leT IT CT.

Definition proj_L (p : S * T) (out : S) : Prop :=
  let (s1, t1) := p in s1 = out.

Lemma t_proj_L : t (prod_op leS leT) leS 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovS proj_L.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_L in *.
- apply FormTop.refl. destruct a. exists s. reflexivity.
- apply FormTop.refl. destruct a, ab, ac.
  subst. exists s. destruct H. destruct H, H0.
  simpl in *. split. split; assumption. reflexivity.
- destruct a. subst.
  induction H0. 
  + apply FormTop.refl. exists a. firstorder.
  + apply FormTop.le_left with (b, t0).
    split. assumption. apply PreO.le_refl.
    assumption.
  + apply FormTop.ginfinity with (inl (i, t0)). 
    intros. simpl in *. destruct u. destruct H1. 
    specialize (H0 _ H1). subst.
    apply H0.
Qed.

Definition proj_R (p : S * T) (out : T) : Prop :=
  let (s1, t1) := p in t1 = out.

Lemma t_proj_R : t (prod_op leS leT) leT 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovT proj_R.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_R in *.
- apply FormTop.refl. destruct a. exists t0. reflexivity.
- apply FormTop.refl. destruct a, ab, ac.
  subst. exists t0. destruct H. destruct H, H0.
  simpl in *. split. subst. split; assumption. reflexivity.
- destruct a. subst.
  induction H0. 
  + apply FormTop.refl. exists a. firstorder.
  + apply FormTop.le_left with (s, b).
    split. apply PreO.le_refl. simpl in H. assumption.
    assumption.
  + apply FormTop.ginfinity with (inr (s, i)). 
    intros. simpl in *. destruct u. destruct H1. 
    specialize (H0 _ H2). subst.
    apply H0.
Qed.

Context {A} `{POA : PreO.t A leA}.
Context {IA} {CA : forall (t : A), IA t -> (A -> Prop)}.
Variable locA : @FormTop.localized _ leA IA CA.
Let CovA := @FormTop.GCov _ leA IA CA.

Context {B} `{POB : PreO.t B leB}.
Context {IB} {CB : forall (t : B), IB t -> (B -> Prop)}.
Variable locB : @FormTop.localized _ leB IB CB.
Let CovB := @FormTop.GCov _ leB IB CB.

Definition parallel (F : S -> A -> Prop) (G : T -> B -> Prop)
  (p : S * T) (out : A * B) : Prop :=
  let (s, t) := p in let (a, b) := out in
   F s a /\ G t b.

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
  intros. destruct a, u. 
  destruct H as ((? & ?) & (? & ?)). exists (x, x0).
  intuition. destruct a. apply Product.factors; try assumption.
  apply (here ContF). apply (here ContG).
- destruct ab, ac, b, c.
  destruct a. unfold FormTop.down, prod_op. simpl.
  apply FormTop.gmonotone with
  (fun s2 : S * T => let (s', t') := s2 in
  (fun s'' => exists a' : A, @FormTop.down _ leA a0 a1 a' /\ F s'' a') s'
  /\
  (fun t'' => exists b' : B, @FormTop.down _ leB b b0 b' /\ G t'' b') t'
  ).
  intros. destruct u.
  unfold FormTop.down in H2.
  destruct H2 as ((? & (? & ?) & ?) & (? & (? & ?) & ?)).
  exists (x, x0). intuition.
  apply Product.factors; try assumption.
  + destruct H. unfold prod_op in H, H2. simpl in H, H2.
    intuition.
    eapply (local ContF); try eassumption. split; assumption.
  + destruct H. unfold prod_op in H, H2. simpl in H, H2.
    intuition.
    eapply (local ContG); try eassumption. split; assumption.
- destruct a, b. destruct H.
  pose proof (fun U => cov ContF U H).
  pose proof (fun U => cov ContG U H1).
  pose proof (Product.unfactors1 _ _ _ _ _ _ _ _ H0).
  pose proof (Product.unfactors2 _ _ _ _ _ _ _ _ H0).
  specialize (H2 _ H4).
  specialize (H3 _ H5).

  (** This is likely a misstep in the proof, and in fact we will
      need to do something smarter. *)
  apply FormTop.gmonotone with
  (fun s0 : S * T => let (s', t') := s0 in
  (fun s'' => exists a' : A, exists b' : B, V (a', b') /\ F s'' a') s'
  /\
  (fun t'' => exists b' : B, exists a' : A, V (a', b') /\ G t'' b') t'
  ).
  intros.  destruct u. 
  destruct H6 as ((? & ? & ? & ?) & (? & ? & ? & ?)).
  exists (x, x1). 
  admit.

  apply Product.factors; try assumption. 
  eapply FormTop.gmonotone. 2:apply H2.
  simpl. intros. firstorder.
  eapply FormTop.gmonotone. 2:apply H3.
  simpl. intros. firstorder.
Admitted.

End Products.
End Cont.

Arguments Cont.t {S} leS {T} leT CovS CovT F : clear implicits.

Module InfoBaseCont.
Section InfoBaseCont.
Generalizable All Variables.
Context {S} `{MLS : MeetLat.t S}.
Context {T} `{MLT : MeetLat.t T}.


Let CovS : S -> (S -> Prop) -> Prop := InfoBase.Cov _.
Let CovT : T -> (T -> Prop) -> Prop := InfoBase.Cov _.


Lemma sc_monotone : forall (f : S -> T),
  PreO.scott_cont f ->
  forall x y : S, MeetLat.le x y -> MeetLat.le (f x) (f y).
Proof.
intros. 
unfold PreO.scott_cont in H.
pose (g := fun b : bool => if b then x else y).
specialize (H _ g).
assert (@PreO.directed _ MeetLat.le _ g).
unfold PreO.directed.
intros.
exists y. destruct i, j; simpl; split; 
  assumption || apply PreO.le_refl.
specialize (H H1 y).
assert (@PreO.sup _ MeetLat.le _ g y).
constructor.
intros. destruct i; simpl. assumption. apply PreO.le_refl.
intros. specialize (H2 false). simpl in H2.
assumption.
specialize (H H2).
destruct H.
specialize (sup_ge true). simpl in sup_ge.
apply sup_ge.
Qed.

(** I have no idea whether this is in fact
    a good definition *)
Record t {F : S -> T -> Prop} :=
  { le_left : forall a b c, MeetLat.le a b -> F b c -> F a c
  ; le_right :  forall a b c,  F a b -> MeetLat.le b c -> F a c
  ; convergence : forall a b c, F a b -> F a c ->
       exists d, @FormTop.down _ MeetLat.le b c d /\ F a d
  ; here : forall s, exists t, F s t
  }.

Arguments t : clear implicits.

Theorem cont : forall (F : S -> T -> Prop),
  t F
  -> Cont.t MeetLat.le MeetLat.le CovS CovT F.
Proof.
intros. constructor; intros.
- apply FormTop.grefl. apply (here H).
- apply FormTop.grefl.
  destruct H0. 
  apply convergence. assumption.
  eapply le_left. eassumption. apply H0. assumption. 
  eapply le_left. eassumption. apply H3. assumption.
- induction H1. 
  + apply FormTop.grefl. exists a0. split; assumption.
  + apply IHGCov. eapply le_right. assumption.
    eassumption. eassumption.
  + destruct i.
    apply (H2 x). unfold InfoBase.C. simpl. reflexivity. 
    eapply le_right. assumption. eassumption. 
    eassumption. 
Qed.
  


End InfoBaseCont.
End InfoBaseCont.

Module Discrete.
Section Discrete.

Generalizable All Variables.

Variable A : Type.

Inductive In (a : A) : option A -> Type :=
  | MkIn : In a (Some a).

Inductive LE : option A -> option A -> Prop :=
  | LENone : forall b, LE None b
  | LEEq : forall a, LE (Some a) (Some a).

Instance PreOLE : PreO.t _ LE.
Proof.
constructor; intros.
- destruct x; constructor.
- destruct H. apply LENone.
  assumption.
Qed.

Instance POLE : PO.t _ LE eq.
Proof.
constructor.
- apply PreOLE.
- repeat intro. subst. intuition.
- intros. destruct H. inversion H0. reflexivity.
  reflexivity.
Qed.

Definition Ix := Concrete.Ix A (option A) In.
Definition C := Concrete.C A (option A) In.
Definition Cov := @FormTop.GCov (option A) eq Ix C.

End Discrete.

Section FinFunc.

Variable (A B : Type).

Inductive discrF {f : A -> B} : option A -> option B -> Prop :=
  | PreImg : forall a, discrF (Some a) (Some (f a))
  | FNone : discrF None None. 

Arguments discrF : clear implicits.

Hint Constructors LE discrF.

Hypothesis deceqB : forall (b b' : B), {b = b'} + {b <> b'}.
Theorem fCont : forall (f : A -> B),
  Cont.t (LE A) (LE B) (Cov A) (Cov B) (discrF f).
Proof.
intros.
constructor; intros.
- destruct a. 
  + apply FormTop.grefl. exists (Some (f a)).
    constructor.
  + apply FormTop.grefl. exists None. constructor.
- destruct H. destruct H, H2; destruct H0, H1;
  try match goal with
  | [ |- _ ] => solve[apply FormTop.grefl; exists None;
      unfold FormTop.down; eauto]
  end.
  pose proof (@FormTop.ginfinity _ (LE A) (Ix A) (C A) (Some a)).
  unfold C, Ix in H. 
Abort.

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

Module LPRFuncs.
Require Import Qnn.

Definition plus (addends : Qnn * Qnn) (sum : Qnn) :  Prop :=
  let (l, r) := addends in (l + r = sum)%Qnn.

Definition prodCov := (@Product.Cov _ _ Qnnle Qnnle LowerR.Ix LowerR.Ix LowerR.C LowerR.C).

Theorem lowerR_loc : @FormTop.localized _ Qnnle LowerR.Ix LowerR.C.
Proof.
unfold LowerR.Ix, LowerR.C.
apply (@InfoBase.loc Qnn LowerR.ops LowerR.QnnML).
Qed.

Theorem isCov_prodCov : FormTop.t (prod_op Qnnle Qnnle) prodCov.
Proof.
unfold prodCov.
eapply Product.isCov.
apply (@MeetLat.PO _ _ LowerR.QnnML).
apply (@MeetLat.PO _ _ LowerR.QnnML).
apply lowerR_loc. apply lowerR_loc.
Qed.

Definition plus_cont_defn := 
  Cont.t (prod_op Qnnle Qnnle) Qnnle 
  prodCov LowerR.Cov plus.

Theorem plus_cont : plus_cont_defn.
Proof.
unfold plus_cont_defn.
constructor; intros.
- apply (@FormTop.refl _ _ _ isCov_prodCov). 
  destruct a. unfold plus. exists (q + q0)%Qnn. reflexivity.
- destruct a, ab, ac. unfold plus in *. 
  subst. apply (@FormTop.refl _ _ _ isCov_prodCov).
  exists (q + q0)%Qnn. split. 2:reflexivity.
  destruct H. destruct H, H0. simpl in *.
  split. admit. admit.
- destruct a. unfold plus in H. subst.
  (* if q + q0 < sup V, then we can do stuff... *)
Abort. 

End LPRFuncs.

Module Bundled.

Delimit Scope loc_scope with loc.
Open Scope loc.

(* Inductively-generated formal topology *)
Class IGT {S : Type} : Type :=
  { le : S -> S -> Prop
  ; PO : PreO.t S le
  ; Ix : S -> Type
  ; C : forall s, Ix s -> (S -> Prop)
  ; localized : @FormTop.localized _ le Ix C
  }.

Arguments IGT : clear implicits.

Generalizable All Variables.

Definition Cov `(X : IGT A) := @FormTop.GCov _ le Ix C.

Instance IGTFT `(X : IGT A) : FormTop.t le (Cov X) :=
  @FormTop.GCov_formtop _ _ PO _ _ localized.

Definition InfoBase {A : Type} {ops : MeetLat.Ops A}
  (ML : MeetLat.t A ops) : IGT A :=
  {| PO := PO.PreO
  ; localized := @InfoBase.loc _ _ ML
  |}.

Definition One : IGT _ := InfoBase MeetLat.one.

Definition times `(LA : IGT A) `(LB : IGT B) : IGT _ :=
 let POA : PreO.t A _ := PO in let POB : PreO.t B _ := PO in
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
  let POS : PreO.t A _ := PO in
  {| mp := Cont.id
  ; mp_ok := Cont.t_id |}.

Definition compose `{LA : IGT A} 
  `{LB : IGT B} `{LD : IGT D} (f : LA ~> LB) (g : LB ~> LD) : LA ~> LD :=
  let POA : PreO.t A _ := PO in 
  let POB : PreO.t B _ := PO in 
   let POD : PreO.t D _ := PO in
  {| mp := Cont.compose (mp f) (mp g)
  ; mp_ok := Cont.t_compose (mp f) (mp g) (mp_ok f) (mp_ok g)
  |}.

End Bundled.