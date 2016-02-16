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
Context {S} {le eq} {PO : PO.t S le eq}.

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

Variable Cov : S -> (S -> Prop) -> Prop.

Lemma monotone : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a -> V a)
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. eapply trans. eassumption.
intros. apply H0 in H2. eapply refl. eassumption.
Qed.

Lemma subset_equiv : t Cov
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

Instance ops : MeetLat.Ops S :=
  {| MeetLat.le := fun x y => dotS x y = x
   ; MeetLat.eq := eq
   ; MeetLat.min := dotS
  |}.

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
intros. eapply trans. eassumption.
intros. apply H0 in H2. eapply refl. eassumption.
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
Instance ops : MeetLat.Ops A :=
  {| MeetLat.le := fun x y => eql (dot x y) x
   ; MeetLat.eq := eql
   ; MeetLat.min := dot
  |}.

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

Context {S} `{commIdemSG : CommIdemSG.t S eq dot}.

Instance ops : MeetLat.Ops S := @CommIdemSG.ops _ eq dot.
Instance ML : MeetLat.t S ops
  := CommIdemSG.asMeetLat.

(** The axiom set essentially says that if [s <= t], then
    [s] is covered by the singleton set [{t}]. *)
Definition Ix (s : S) : Type := { t : S & MeetLat.le s t }.
Definition C (s : S) (s' : Ix s) s'' : Prop := projT1 s' = s''.

(** This axiom set is localized. *)
Definition loc : @FormTopM.localized S dot Ix C.
Proof.
unfold FormTopM.localized. intros. simpl.
unfold Ix, C in *.
destruct i.
unfold FormTopM.dot in *.
assert (MeetLat.le (MeetLat.min b c) (MeetLat.min b c)).
apply PreO.le_refl.
exists (existT _ (FormTopM.dot b c) H).
intros.  simpl in *. unfold FormTopM.dot in *. destruct H0. 
exists x. split. reflexivity.
replace dot with MeetLat.min by reflexivity.
apply (@PO.le_antisym _ MeetLat.le _ _).
apply MeetLat.min_l.
simpl.
replace dot with MeetLat.min by reflexivity.
rewrite MeetLat.min_assoc.
rewrite !MeetLat.min_idempotent.
rewrite MeetLat.min_assoc.
rewrite MeetLat.min_idempotent.
rewrite <- l at 2.
rewrite MeetLat.min_assoc. reflexivity.
Qed.

(** The covering relation for information bases,
    which we derive from the axiom set above. *)
Definition Cov := @FormTopM.GCov _ dot Ix C.

(** The proof that [Cov] is a valid formal topology. *)
Definition isCov : @FormTopM.t _ dot Cov := 
  FormTopM.GCov_formtop Ix C loc.

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

Theorem lowerTop : MeetLat.t Qnn (@InfoBase.ops _ Qnnmin).
Proof. 
apply (@CommIdemSG.asMeetLat _ _ _ lowerCommSG).
Qed.

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

Instance SPO : PO.t S _ _ := PO.map (fun s x => In x s) (PO.subset X).

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

Require Import List.

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
Context `{POS : PO.t S leS eqS}. 
Context `{POT : PO.t T leT eqT}.
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

Definition PO := PO.product POS POT.

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
  
End Product.
End Product.

(** I intend to define continuous relations below! I had some code here,
    but it broke when I updated to Coq 8.5, and I will probably rework the
    definitions because these were not good enough.
*)

Module Cont.
Generalizable All Variables.

Section Cont.

Context {S} `{POS : PO.t S leS eqS}.
Context {T} `{POT : PO.t T leT eqT}.

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

Context {S} `{POS : PO.t S leS eqS}.
Context {T} `{POT : PO.t T leT eqT}.
Context {U} `{POU : PO.t U leU eqU}.
Context `{FTS : FormTop.t S leS CovS}.
Context `{FTT : FormTop.t T leT CovT}.
Context `{FTU : FormTop.t U leU CovU}.

Definition id (s t : S) := s = t.

Theorem t_id : FormTop.t leS CovS -> t leS leS CovS CovS id.
Proof.
intros. constructor; intros; unfold id in *.
- eapply FormTop.refl. exists a. reflexivity.
- subst. apply FormTop.refl. exists a. tauto.
- subst. refine (FormTop.monotone _ _ _ _ _ _ H1).
  firstorder.
Qed.

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
  refine (FormTop.monotone _ _ _ _ _ _ H4).
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
  apply (FormTop.monotone _ FTS)
  with (fun s => exists t' : T, (exists bc' : U, @FormTop.down _ leU b c bc' /\ G t' bc')
   /\ F s t'). firstorder.
  apply (cov H _ down H3).
- unfold compose. intros.
  destruct H1 as [t [Fat Gtb]].
  apply (FormTop.monotone _ FTS)
    with (fun s => exists t1 : T, (exists u : U, V u /\ G t1 u) /\ F s t1).
  firstorder.
  apply (cov H _ Fat).
  apply (cov H0 _ Gtb). assumption.
Qed.
  

End Morph.
End Cont.