Require Import 
  Prob.StdLib 
  Coq.Classes.CMorphisms 
  Coq.Classes.CRelationClasses
  Algebra.OrderC.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Module L := Lattice.

(** A frame represents the essence of the algebraic structure of topologies,
    without the requirement that this algebraic structure be formed by
    subsets of an underlying space. The frame is just the algebra itself.
    A frame has a supremum operation, which corresponds to the fact that
    topologies are closed under arbitrary union.
    We call elements of a frame "opens" to indicate that they are reminiscent
    of open sets.

    Frames are also often referred to as locales. They're the same things, but
    are used to indicate opposite categories. The category of frames is the
    opposite of the category of locales. We do this because continuous functions
    are, in a sense, "backwards". A continuous function in topology 
    [f : A -> B] is defined by its inverse image which takes open sets in
    [B] to open sets in [A]. So a continuous function from [A] to [B] corresponds
    to a frame homomorphism from the frame representing the topology of [B] to the
    frame representing the topology of [A]. A frame homomorphism is a morphism
    in the category of frames. The morphisms of the category of locales are called
    continuous maps, and since it's the opposite category, a continuous 
    function from [A] to [B] corresponds to a continuous map from the locale
    for [A] to the locale for [B].
    *)
Module Frame.
  Class Ops {A} :=
   { LOps :> L.Ops A
   ; sup : forall {Ix : Type}, (Ix -> A) -> A
   }.

  Arguments Ops : clear implicits.

  Class t {A} {OA : Ops A}: Type :=
  { L :> L.t A LOps
  ; sup_proper : forall {Ix : Type},
     Proper (pointwise_relation _ L.eq ==> L.eq) (@sup _ _ Ix)
  ; sup_ok :  forall {Ix : Type} (f : Ix -> A), PreO.sup (le := L.le) f (sup f)
  ; sup_distr : forall x {Ix : Type} (f : Ix -> A)
    , L.eq (L.min x (sup f)) (sup (fun i => L.min x (f i)))
  }.

  Arguments t : clear implicits.
  Section Facts.
  Context {A OA} {tA : t A OA}.

  Definition sup_proper_u : forall {Ix : Type} (f g : Ix -> A),
    (forall (i : Ix), L.eq (f i) (g i)) -> L.eq (sup f) (sup g).
  Proof.
  intros. apply sup_proper. unfold pointwise_relation.
  assumption.
  Qed.


  (** Every frame must have a top and bottom element. *)

  Definition top : A := sup (fun a => a).

  Definition top_ok : PreO.top (le := L.le) top.
  Proof. 
    unfold PreO.top. simpl. pose proof (sup_ok (fun a => a)) as H.
    destruct H. apply sup_ge.
  Qed.

  Definition bottom : A := sup (fun contra : False => False_rect _ contra).

  Definition bottom_ok : PreO.bottom (le := L.le) bottom.
  Proof.
    unfold PreO.bottom. intros. 
    apply (PreO.sup_least (fun contra : False => False_rect _ contra)).
    apply sup_ok. intros; contradiction.
  Qed.

  End Facts.
  Section Morph. 
  Context {A OA} {tA : t A OA}.
  Context {B OB} {tB : t B OB}.

  Record morph {f : A -> B} : Type :=
  { f_L : L.morph LOps LOps f
  ; f_sup : forall {Ix : Type} (g : Ix -> A), L.eq (f (sup g)) (sup (fun i => f (g i)))
  ; f_top : L.eq (f top) top
  }.

  Arguments morph : clear implicits.

  Lemma f_eq {f : A -> B} :
    morph f -> Proper (L.eq ==> L.eq) f.
  Proof. 
    intros H. apply (L.f_eq (f_L H)).
  Qed.

  Lemma f_bottom {f : A -> B} : morph f -> L.eq (f bottom) bottom.
  Proof.
  intros MF. unfold bottom. rewrite (f_sup MF). apply sup_proper.
  unfold pointwise_relation. intros. contradiction.
  Qed.

  End Morph.

  Arguments morph {A} OA {B} OB f.

  Section MorphProps.
  Context {A OA} {tA : t A OA}.

  Lemma morph_id : morph OA OA (fun x => x).
  Proof. 
   intros. constructor. apply L.morph_id. apply L.
   reflexivity. reflexivity.
  Qed.

  Lemma morph_compose {B OB} {tB : t B OB}
    {C OC} {tC : t C OC}
     (f : A -> B) (g : B -> C)
     : morph OA OB f 
     -> morph OB OC g 
     -> morph OA OC (fun x => g (f x)).
  Proof. intros. constructor.
  - eapply L.morph_compose; (apply L || (eapply f_L; eassumption)).
  - intros. rewrite <- (f_sup X0). rewrite (f_eq X0).
    reflexivity. rewrite (f_sup X). reflexivity.
  - rewrite <- (f_top X0). rewrite (f_eq X0).
    reflexivity. rewrite (f_top X). reflexivity.
  Qed.

  End MorphProps.

  Definition one_ops : Ops True :=
    {| LOps := L.one_ops
     ; sup := fun _ _ => I
    |}.

  Definition one : t True one_ops.
  Proof. constructor; intros; auto.
  - apply L.one.
  - unfold Proper, respectful. intros. reflexivity.
  - constructor; trivial.
  Qed.

  (** Propositions form a frame, where supremum is given by the
      existential quantifier. *)
  Local Instance prop_ops : Ops Prop :=
    {| LOps := L.prop_ops
     ; sup := (fun _ f => exists i, f i)
    |}.

  Local Instance prop : t Prop prop_ops.
  Proof. constructor; simpl; intros.
  - apply L.prop.
  - constructor; unfold pointwise_relation in X; simpl in X;
     intros [??]; eexists; apply X; eassumption.
  - constructor; simpl; intros.
    + exists i. assumption.
    + destruct H0. apply (H x). assumption.
  - split; intros. 
    + destruct H as (xa & i & fia). exists i. intuition.
    + destruct H as (i & xa & fia). split. assumption.
      exists i. assumption.
  Qed.

  Definition pointwise_ops {A B} (OB : forall a : A, Ops (B a))
    : Ops (forall a, B a) :=
    {| LOps := L.pointwise_ops (fun _ => LOps)
     ; sup := fun _ f => fun x => sup (fun i => f i x)
    |}.

  Definition pointwise {A B OB} `(forall a : A, t (B a) (OB a))
    : t (forall a, B a) (pointwise_ops OB).
  Proof. constructor.
  - apply L.pointwise. intros. apply L.
  - simpl. unfold Proper, respectful, pointwise_relation, pointwise_op.
    intros. apply sup_proper. unfold pointwise_relation.
    intros a'. apply X.
  - constructor; simpl; unfold pointwise_op; intros.
    pose proof (@sup_ok _ _ (H a) Ix (fun i => f i a)).
    apply X.
    pose proof (@sup_ok _ _ (H a) Ix (fun i => f i a)).
    apply X0. intros. apply X.
  - simpl. unfold pointwise_op. intros.
    apply (sup_distr (t := H a)).
  Qed.

  Lemma sup_pointwise {A} {OA} {X : t A OA} {Ix Ix'} (f : Ix -> A) (g : Ix' -> A)
  : (forall (i : Ix), { j : Ix' & L.le (f i) (g j) })
  -> L.le (sup f) (sup g).
  Proof.
  intros H. eapply PreO.sup_least. apply sup_ok. intros.
  destruct (H i). eapply PreO.le_trans. eassumption.
  apply PreO.sup_ge. apply sup_ok.
  Qed.

  Definition morph_pointwise {A B C OC} {tC : t C OC} (f : B -> A)
    : morph (pointwise_ops (fun _ : A => OC)) (pointwise_ops (fun _ : B => OC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply L.morph_pointwise.
  - unfold pointwise_op. intros. apply PO.eq_refl. 
  - unfold pointwise_op. intros. apply PO.le_antisym.
    + apply sup_pointwise. intros. exists (fun b => i (f b)).
      apply PreO.le_refl. 
    + apply sup_pointwise. intros. exists (fun _ => i a). apply PreO.le_refl.
  Qed. 

  Definition subset_ops A : Ops (A -> Prop) := pointwise_ops (fun _ => prop_ops).
  
  Definition subset (A : Type) : t (A -> Prop) (subset_ops A):= 
     pointwise (fun _ : A => prop).

  (** [cmap] represents a continuous map on locales. It is just a
      package for a frame homomorphism running in the opposite direction. *)
  Record cmap {A OA} {B OB} := 
  { finv :> B -> A
  ; cont : morph OB OA finv
  }.

  Arguments cmap {A} OA {B} OB.

  (** A point in [A] is a continuous map from the frame representing
      a space with one point ([Prop]) to [A]. *)
  Definition point {A} (OA : Ops A) := cmap prop_ops OA.

  (** Every function [f : A -> B] is continuous on the topology
      which includes all subsets. *)
  Definition subset_map {A B} (f : A -> B) : cmap (subset_ops A) (subset_ops B).
  Proof.
  refine ( {| finv P x := P (f x) |}).
  apply morph_pointwise.
  Defined.

  Definition cmap_compose {A B C OA OB OC} 
    {tA : t A OA} {tB : t B OB} {tC : t C OC}
    (f : cmap OA OB) (g : cmap OB OC) : cmap OA OC.
  Proof. refine (
  {| finv x := finv f (finv g x) |}
  ). eapply morph_compose; eapply cont.
  Defined. 

End Frame.

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
Theorem asPreO : PreO.t MeetLat.le.
Proof.
constructor; simpl; intros.
- apply dot_idempotent.
- rewrite <- H. rewrite <- H0 at 2.
  rewrite dot_assoc. reflexivity.
Qed.

Theorem asPO : PO.t MeetLat.le eql.
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
- unfold CMorphisms.Proper, CMorphisms.respectful; intros. 
  simpl in *. rewrite X, X0. reflexivity.
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