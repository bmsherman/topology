Require Import SetoidClass Coq.Classes.Morphisms.
Generalizable All Variables.

Definition prod_op {A B} (fA : A -> A -> Prop) (fB : B -> B -> Prop)
   (x y : A * B) := fA (fst x) (fst y) /\ fB (snd x) (snd y).

Definition map_op {A B} (f : A -> B) (P : B -> B -> Prop) (x y : A) : Prop := 
  P (f x) (f y).

Definition pointwise_op {A} {B : A -> Type} (P : forall a, B a -> B a -> Prop)
  (f g : forall a, B a) := forall a, P a (f a) (g a).

(** A tour of algebraic structures. Most of them are things related to
    orders or latices.
    Each definition follows a relatively rigid pattern.
    Each algebraic structure is defined in its own module. 
    For instance, preorders are defined in the Module [PreO].
    The type which defines the algebraic structure for preorders
    is called [t], which outside the module looks like [PreO.t].

    Let's be concrete. The type [Qnn] of non-negative rational numbers
    has a relation [Qnnle : Qnn -> Qnn -> Prop] which represents a
    preorder. Therefore, we can make an instance
    [H : PO.t Qnn Qnnle] which gives evidence that [Qnnle] is in fact
    a preorder.

    Within the module [PreO] (and for most algebraic structures), we have a
    type [morph] which gives evidence that some function in fact is a morphism
    in that category of algebraic structure; that is, it preserves the structure
    for whatever algebraic structure we defined. We always prove that the identity
    function is a morphism [morph_id] and that morphisms are closed under 
    composition [morph_compose].
 
    At the end we give examples or building blocks for the algebraic structure.
    There's usually trivial examples of these structures over base types which
    have only one or two elements. There is usually a way to form products,
    and often, given an algebraic structure on [B] and a function [f : A -> B],
    we can define the algebraic structure on [A] by asking whether it holds
    pointwise in [B].

    Just given a preorder, we can define what it means for something to be
    a top element or bottom, max or min, infimum or supremum, and so these
    definitions are given in the [PO] module. Many algebraic structures are
    then closed under these operations, in which case there will be functions
    that are defined that implement the given operation. For instance, for
    meet-semilattices, we have an operation for minimums.
*)
    

(** Preorders: types which have a "<=" relation which is reflexitive and
    transitive *)
Module PreO.
  (** The relation [le] (read: Less than or Equal) is a preorder when
      it is reflexive [le_refl] and transitive [le_trans]. *)
  Class t {A : Type} {le : A -> A -> Prop} : Prop :=
  { le_refl : forall x, le x x
  ; le_trans : forall x y z, le x y -> le y z -> le x z
  }.

  Arguments t : clear implicits.
  
  (** A morphism of preorders is just a monotonic function. That is,
      it preserves ordering. *)
  Definition morph `(leA : A -> A -> Prop) `(leB : B -> B -> Prop) `(f : A -> B) : Prop :=
    forall a b, leA a b -> leB (f a) (f b).

  Section Facts.

  Context `{le : A -> A -> Prop}.
  Context `(tA : t A le).
  Infix "<=" := le.

  Lemma morph_id : morph le le (fun x => x).
  Proof. 
    unfold morph; auto.
  Qed.

  Lemma morph_compose `(tB : t B leB) `(tC : t C leC)
    : forall (f : A -> B) (g : B -> C), 
     morph le leB f -> morph leB leC g -> morph le leC (fun x => g (f x)).
  Proof.
    unfold morph; auto.
  Qed.

  (** [top t] holds if [t] is bigger than everything *)
  Definition top (t : A) : Prop := forall a, a <= t.

  (** [bottom b] holds if [b] is smaller than everything *)
  Definition bottom (b : A) : Prop := forall a, b <= a.

  (** [max l r m] holds if [m] is the maximum of [l] and [r]. *)
  Record max {l r m : A} : Prop :=
  { max_l     : l <= m
  ; max_r     : r <= m
  ; max_least : forall m', l <= m' -> r <= m' -> m <= m'
  }.

  Arguments max : clear implicits.

  (** [max] is commutative *)
  Lemma max_comm : forall l r m, max l r m -> max r l m.
  Proof.
  intros. constructor.
  - apply H.
  - apply H.
  - intros. apply H; assumption.
  Qed.

  (** [min l r m] holds if [m] is the minimum of [l] and [r] *)
  Record min {l r m : A} : Prop :=
  { min_l        : m <= l
  ; min_r        : m <= r
  ; min_greatest : forall m', m' <= l -> m' <= r -> m' <= m
  }.

  Global Arguments min : clear implicits.

  (** [min] is commutative *)
  Lemma min_comm : forall l r m, min l r m -> min r l m.
  Proof.
  intros. constructor.
  - apply H.
  - apply H.
  - intros. apply H; assumption.
  Qed.

  (** [min] is associative, phrased in a relational manner,
      i.e., minima are associative when they exist *)
  Lemma min_assoc : forall a b c, 
    forall bc, min b c bc ->
    forall ab, min a b ab ->
    forall abc, min a bc abc <-> min ab c abc.
  Proof.
  intros a b c bc BC ab AB abc. split; intros ABC.
  - constructor. 
    + apply (min_greatest AB).
      * apply (min_l ABC). 
      * eapply PreO.le_trans. 
        apply (min_r ABC). apply (min_l BC).
    + eapply PreO.le_trans. apply (min_r ABC).
      apply (min_r BC).
    + intros. apply (min_greatest ABC).
      * eapply PreO.le_trans. apply H. 
        apply (min_l AB).
      * apply (min_greatest BC). 
        eapply PreO.le_trans. apply H. apply (min_r AB).
        assumption.
  - constructor. 
    + eapply PreO.le_trans. apply (min_l ABC).
      apply (min_l AB).
    + apply (min_greatest BC).
      * eapply PreO.le_trans. 
        apply (min_l ABC). apply (min_r AB).
      * apply (min_r ABC). 
    + intros. apply (min_greatest ABC).
      * apply (min_greatest AB). 
        assumption.
        eapply PreO.le_trans. apply H0. apply (min_l BC).
      * eapply PreO.le_trans. apply H0. 
        apply (min_r BC).
  Qed.

  Lemma min_idempotent : forall a, min a a a.
  Proof.
  intros. constructor.
  - apply le_refl.
  - apply le_refl.
  - intros. assumption.
  Qed.

  (** [sup f m] holds when [m] is the supremum of all
      values indexed by [f]. *)
  Record sup {I : Type} (f : I -> A) (m : A) : Prop :=
  { sup_ge : forall i, f i <= m
  ; sup_least : forall m', (forall i, f i <= m') -> m <= m'
  }.

  (** [inf f m] holds when [m] is the infimum of all
      values indexed by [f]. *)
  Record inf {I : Type} (f : I -> A) (m : A) : Prop :=
  { inf_le : forall i, m <= f i
  ; inf_greatest : forall m', (forall i, m' <= f i) -> m' <= m
  }.

  (** A directed subset of [A] is one where every two
      elements have a common upper bound. *)
  Definition directed {I} (f : I -> A) :=
    forall i j : I, exists k, f i <= k /\ f j <= k.

  End Facts.

  Definition scott_cont `{tA : t A leA} 
  `{tB : t B leB} (f : A -> B) :=
  forall I (g : I -> A), @directed _ leA _ g
  -> forall m, @sup _ leA _ g m 
  -> @sup _ leB _ (fun i => f (g i)) (f m).

  (** [True], the one-element type, has a trivial preorder *)
  Definition one : t True (fun _ _ => True).
  Proof. constructor; auto.
  Qed.

  (** The preorder on booleans given by False < True *)
  Definition two : t bool Bool.leb.
  Proof. constructor. 
  - intros; auto. destruct x; simpl; trivial.
  - destruct x, y, z; auto. simpl in *. congruence.
  Qed.

  Definition Nat : t nat le.
  Proof. constructor; [ apply Le.le_refl | apply Le.le_trans ].
  Qed.

  Definition discrete (A : Type) : t A Logic.eq.
  Proof. constructor; auto. intros; subst; auto. Qed.

  (** Product preorders *)
  Definition product `(tA : t A leA) `(tB : t B leB) 
   : t (A * B) (prod_op leA leB).
  Proof. constructor.
   - destruct x. split; apply le_refl.
   - unfold prod_op; intros. 
     destruct x, y, z; simpl in *.
     destruct H, H0.
     split; eapply PreO.le_trans; eassumption.
  Qed.

  (** Given a preorder on [B] and a function [f : A -> B],
      we form a preorder on [A] by asking about their order
      when mapped into [B] by [f]. *)
  Definition map `(f : A -> B) `(tB : t B leB) 
    : t A (fun x y => leB (f x) (f y)).
  Proof. constructor; intros.
  - apply le_refl.
  - eapply le_trans; eauto.
  Qed.

  (** It's probably easiest to explain the simply-typed
      version of this: Given a preorder on [B], we can 
      form a preorder on functions of type [A -> B] by saying
      [f <= g] (where [f, g : A -> B]) whenever
      the relation holds pointwise, i.e., for all [a : A],
      we have [f a <= g a]. *)
  Definition pointwise {A} {B : A -> Type} 
    {leB : forall a, B a -> B a -> Prop}
    (tB : forall a, t (B a) (leB a)) 
    : t (forall a, B a) (pointwise_op leB).
  Proof. 
    unfold pointwise_op; constructor; intros. 
    - apply le_refl.
    - eapply le_trans; eauto.
  Qed.

  Definition morph_pointwise {A B C} `{tC : t C leC} (f : B -> A)
    : morph (pointwise_op (fun _ => leC)) (pointwise_op (fun _ => leC))
      (fun g b => g (f b)).
  Proof.
    unfold morph, pointwise_op. intros; simpl in *; apply H.
  Qed. 

  (** The type of propositions forms a preorder, where "<=" is
      implication. *)
  Instance prop : t Prop (fun P Q => P -> Q).
  Proof. 
    constructor; auto.
  Qed.

  (** Subsets, in type theory defined as propositional functions,
      i.e., subsets on [A] are functions of type [f : A -> Prop],
      form a preorder ordered by subset inclusion. This is actually just
      the preorder on propositions applied pointwise to functions. *)
  Instance subset (A : Type) : t (A -> Prop) _ := pointwise (fun _ => prop).

End PreO.

Arguments PreO.max {A} {le} _ _ _ : clear implicits.

(** Partial orders: We take a preorder, but also have an equality relation [eq]
    such that [eq x y] exactly when both [le x y] and [le y x]. *)
Module PO.
  Class t {A : Type} {le : A -> A -> Prop} {eq : A -> A -> Prop} : Prop :=
  { PreO :> PreO.t A le
  ; le_proper : Proper (eq ==> eq ==> iff) le
  ; le_antisym : forall x y, le x y -> le y x -> eq x y
  }.

  Arguments t : clear implicits.

  Section Morph.
  Context `{tA : t A leA eqA} `{tB : t B leB eqB}.

  Record morph {f : A -> B} : Prop :=
   { f_PreO : PreO.morph leA leB f
   ; f_eq : Proper (eqA ==> eqB) f
   }.

  Arguments morph : clear implicits.
  
  End Morph.

  Arguments morph {_} leA eqA {_} leB eqB f.

  Section Facts.
  Context `{tA : t A leA eqA}.

  (** The equality relation of a partial order must form an
      equivalence relation. *)
  Definition eq_refl : Reflexive eqA. 
  Proof. unfold Reflexive. 
    intros. apply le_antisym; apply PreO.le_refl.
  Qed.

  Definition eq_sym : Symmetric eqA.
  Proof. 
  unfold Symmetric. intros. apply le_antisym. eapply le_proper.
  apply eq_refl. apply H. apply PreO.le_refl. eapply le_proper.
  apply H. apply eq_refl. apply PreO.le_refl.
  Qed.

  Definition eq_trans : Transitive eqA.
  Proof.
    unfold Transitive.
    intros. apply le_antisym. eapply le_proper. apply H. 
    apply eq_refl. eapply le_proper. apply H0. apply eq_refl.
    apply PreO.le_refl. eapply le_proper. apply eq_refl. apply H.
    eapply le_proper. apply eq_refl. apply H0. apply PreO.le_refl.
  Qed.

  Lemma max_unique : forall l r m m'
   , PreO.max (le := leA) l r m 
   -> PreO.max (le := leA) l r m' 
   -> eqA m m'.
  Proof.
  intros. apply PO.le_antisym.
  - apply H; apply H0.
  - apply H0; apply H.
  Qed.

  Lemma min_unique : forall l r m m'
   , PreO.min (le := leA) l r m 
   -> PreO.min (le := leA) l r m' 
   -> eqA m m'.
  Proof.
  intros. apply PO.le_antisym.
  - apply H0; apply H. 
  - apply H; apply H0.
  Qed.

  End Facts.

  Instance t_equiv `{tA : t A leA eqA} : Equivalence eqA.
  Proof. 
    split; [apply eq_refl | apply eq_sym | apply eq_trans ].
  Qed.

  Lemma morph_id `{tA : t A leA eqA} : morph leA eqA leA eqA (fun x : A => x).
  Proof. constructor.
    - apply PreO.morph_id. 
    - solve_proper.
  Qed.

  Lemma morph_compose `{tA : t A leA eqA} `{tB : t B leB eqB} `{tC : t C leC eqC}
    : forall (f : A -> B) (g : B -> C), morph leA eqA leB eqB f 
    -> morph leB eqB leC eqC g -> morph leA eqA leC eqC (fun x => g (f x)).
  Proof.
    intros. destruct H, H0. constructor; intros.
    - apply (PreO.morph_compose (leB := leB)); eauto using PreO. apply PreO.
    - solve_proper.
  Qed.

  Instance le_properI `(tA : t A leA eqA) 
    : Proper (eqA ==> eqA ==> iff) leA.
  Proof. intros. apply le_proper. Qed.

  (** Morphisms must respect the equality relations on both their
      source (domain) and target (codomain). *)
  Instance morph_properI `(tA : t A leA eqA) `(tB : t B leB eqB) (f : A -> B)
    : morph leA eqA leB eqB f -> Proper (eqA ==> eqB) f.
  Proof. 
    intros. destruct H. unfold Proper, respectful. apply f_eq0. 
  Qed.

  (** Now we will extend the preorders we had to partial orders
      in the obvious ways. There's really nothing interesting
      here. *)

  Definition one : t True (fun _ _ => True) (fun _ _ => True).
  Proof. 
    constructor; intros; auto.
    - apply PreO.one.
    - unfold Proper, respectful. intuition.
  Qed.

  Definition two : t bool Bool.leb Logic.eq.
  Proof. 
    constructor; intros. 
    - apply PreO.two. 
    - solve_proper. 
    - destruct x, y; auto.
  Qed.

  Definition Nat : t nat le Logic.eq.
  Proof.
  constructor; intros.
  - apply PreO.Nat.
  - solve_proper.
  - apply Le.le_antisym; assumption.
  Qed.

  Definition discrete (A : Type) : t A Logic.eq Logic.eq.
  Proof.
  constructor; intros.
  - apply PreO.discrete.
  - solve_proper.
  - assumption.
  Qed.

  Definition product `(tA : t A leA eqA) `(tB : t B leB eqB) 
    : t (A * B) (prod_op leA leB) (prod_op eqA eqB).
  Proof. constructor; intros.
   - apply PreO.product; apply PreO.
   - unfold prod_op, Proper, respectful. intros. intuition;
     (eapply le_proper; 
      [ ((eapply eq_sym; eassumption) || eassumption) 
      | ((eapply eq_sym; eassumption) || eassumption) 
      | eassumption ]).
   - unfold prod_op. destruct H, H0. split; apply le_antisym; intuition.
  Qed.

  Definition map `(f : A -> B) `(tB : t B leB eqB) : t A
    (map_op f leB) (map_op f eqB).
  Proof. constructor; intros.
  - apply (PreO.map f PreO).
  - unfold map_op; split; simpl in *; intros. 
    + rewrite <- H. rewrite <- H0.
      assumption.
    + rewrite H.  rewrite H0. apply H1.
  - unfold map_op; eapply le_antisym; eauto.
  Qed.

  Definition pointwise {A} {B : A -> Type}
    {leB eqB : forall a, B a -> B a -> Prop}
    (tB : forall a, t (B a) (leB a) (eqB a)) : t (forall a, B a) (pointwise_op leB)
     (pointwise_op eqB).
  Proof. 
  constructor; intros.
  - apply (PreO.pointwise (fun _ => PreO)).  
  - unfold pointwise_op. split; simpl in *; intros. 
    rewrite <- H0. rewrite <- H. apply H1.
    rewrite H0. rewrite H. apply H1.
  - unfold pointwise_op. eauto using le_antisym.
  Qed.

  Definition morph_pointwise {A B C} `{tC : t C leC eqC} (f : B -> A)
    : morph (pointwise_op (fun _ => leC)) (pointwise_op (fun _ => eqC))
            (pointwise_op (fun _ => leC)) (pointwise_op (fun _ => eqC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply PreO.morph_pointwise. 
  - unfold pointwise_op in *. solve_proper.
  Qed. 

  Instance prop : t Prop (fun P Q => P -> Q) (fun P Q => P <-> Q).
  Proof. 
  constructor; intuition.
  split; simpl in *; intros; intuition.
  Qed.

  Instance subset (A : Type) : t (A -> Prop) _ _ := pointwise (fun _ => prop).
 
End PO.

(** Join semi-lattices, or directed sets. Here we take a partial order
    and add on a maximum operation. Natural numbers are
    one of many examples. We will often generalize sequences, which
    are functions of type (nat -> A), to nets, which are functions of
    type (I -> A), where I is a directed set. *)
Module JoinLat.

  Class Ops {A} : Type :=
  { le : A -> A -> Prop
  ; eq : A -> A -> Prop
  ; max : A -> A -> A
  }. 

  Arguments Ops : clear implicits.

  (** When do the operations [le], [eq], and [max] actually represent
      a join semi-lattice? We need [le] and [eq] to be a partial order,
      and we need our [max] operation to actually implement a maximum. *)
  Class t {A : Type} {O : Ops A} : Prop :=
  { PO :> PO.t A le eq
  ; max_proper : Proper (eq ==> eq ==> eq) max
  ; max_ok : forall l r, PreO.max (le := le) l r (max l r)
  }.

  Arguments t : clear implicits.

  Instance max_properI `(tA : t A)
    : Proper (eq ==> eq ==> eq) max.
  Proof. intros. apply max_proper. Qed.

  Record morph `{OA : Ops A} `{OB : Ops B}
    {f : A -> B} : Prop :=
   { f_PO : PO.morph le eq le eq f
   ; f_max : forall a b, eq (f (max a b)) (max (f a) (f b))
   }.

  Arguments morph {A} OA {B} OB f.

  (** A morphism on join semi-lattices respects the equality relation
      on its source and target. *)
  Lemma f_eq {A B OA OB} {tA : t A OA} {tB : t B OB} {f : A -> B} : 
  morph OA OB f -> Proper (eq ==> eq) f.
  Proof. 
    unfold Proper, respectful. intros. apply (PO.f_eq (f_PO H)).
    assumption.
  Qed.

  Lemma morph_id {A OA} (tA : t A OA) 
    : morph OA OA (fun x => x).
  Proof.
  constructor; intros.
  - apply PO.morph_id.
  - apply PO.eq_refl.
  Qed.

  Lemma morph_compose {A B C OA OB OC} 
    (tA : t A OA) (tB : t B OB) (tC : t C OC)
    : forall f g, morph OA OB f 
           -> morph OB OC g 
           -> morph OA OC (fun x => g (f x)).
  Proof.
  intros. constructor; intros.
  - eapply PO.morph_compose; eapply f_PO; eassumption.
  - rewrite <- (f_max H0). rewrite (f_eq H0). reflexivity.
    apply (f_max H).
  Qed.

  (** Max is very boring for the one-point set *)
  Definition one_ops : Ops True :=
    {| le := fun _ _ => True
     ; eq := fun _ _ => True
     ; max := fun _ _ => I
    |}.

  Definition one : t True one_ops.
  Proof. 
  constructor; intros; auto; unfold Proper, respectful; simpl; auto.
  - apply PO.one. 
  - destruct l, r. constructor; tauto.
  Qed.

  (** Max for booleans is the boolean OR. *)
  Definition two_ops : Ops bool :=
    {| le := Bool.leb
     ; eq := Logic.eq
     ; max := orb
    |}.

  Definition two : t bool two_ops.
  Proof. constructor; intros; (
    apply PO.two || solve_proper
    ||
   (try constructor;
  repeat match goal with
  | [ b : bool |- _ ] => destruct b
  end; simpl; auto)).
  Qed. 

  Instance Nat_ops : Ops nat :=
    {| le := Peano.le
     ; eq := Logic.eq
     ; max := Peano.max
    |}.

  Require Max.
  Instance Nat : t nat Nat_ops.
  Proof. constructor; intros.
  - apply PO.Nat.
  - solve_proper.
  - constructor. simpl. apply Max.le_max_l. apply Max.le_max_r.
    apply Max.max_lub.
  Qed.

  (** Max for propositions is the propositional OR, i.e., disjunction *)
  Instance prop_ops : Ops Prop :=
    {| le := fun P Q : Prop => P -> Q
     ; eq := fun P Q : Prop => P <-> Q
     ; max := fun P Q : Prop => P \/ Q
    |}.

  Instance prop : t Prop prop_ops.
  Proof. 
    constructor; simpl; intros; constructor; simpl; firstorder.
  Qed.

  Definition pointwise_ops {A B} (O : forall a : A, Ops (B a)) : Ops (forall a, B a) :=
    {| le := pointwise_op (fun a => @le _ (O a))
     ; eq := pointwise_op (fun a => @eq _ (O a))
     ; max :=  (fun f g a => @max _ (O a) (f a) (g a))
    |}.

  Definition pointwise 
    `(tB : forall (a : A), t (B a) (OB a)) : 
     t (forall a, B a) (pointwise_ops OB).
  Proof. constructor; simpl; intros.
    - apply PO.pointwise; intros. eapply @PO; apply tB.
    - unfold respectful, Proper, pointwise_op. intros.
      apply max_proper. apply H. apply H0.
    - constructor; unfold pointwise_op; simpl; intros; apply max_ok.
      apply H. apply H0.
  Qed.

  Definition morph_pointwise {C OC} {tC : t C OC} `(f : B -> A)
    : morph (pointwise_ops (fun _ => OC)) (pointwise_ops (fun _ => OC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply PO.morph_pointwise.
  - unfold pointwise_op. intros. apply PO.eq_refl. 
  Qed. 

  Instance subset (A : Type) : t (A -> Prop) (pointwise_ops (fun _ => prop_ops)) 
    := pointwise (fun _ => prop).

  Definition product_ops `(OA : Ops A) `(OB : Ops B) : Ops (A * B) :=
    {| le := prod_op le le
     ; eq := prod_op eq eq
     ; max := fun (x y : A * B) => (max (fst x) (fst y), max (snd x) (snd y))
    |}.

  Definition product {A OA B OB} (tA : t A OA) (tB : t B OB) 
   : t (A * B) (product_ops OA OB).
  Proof. constructor;
    (apply PO.product; apply PO) ||
    (simpl; intros; 
     constructor; unfold prod_op in *; simpl; intros;
    repeat match goal with
    | [ p : (A * B)%type |- _ ] => destruct p; simpl
    | [ p : _ /\ _ |- _ ] => destruct p; simpl
    | [  |- _ /\ _ ] => split
    | [ |- _ ] => eapply PreO.max_l; apply max_ok
    | [ |- _ ] => eapply PreO.max_r; apply max_ok
    | [ |- _ ] => apply max_proper; assumption
    end).
   eapply PreO.max_least. apply max_ok. assumption. assumption.
   eapply PreO.max_least. apply max_ok. assumption. assumption.
   Qed. 
   
End JoinLat.

(** A meet semi-lattice is literally a join semi-lattice turned
    upside-down. Instead of having a [max] operation, it has a [min].
    The code is essentially copied from [JoinLat]. *)
Module MeetLat.

  Class Ops {A} : Type :=
  { le : A -> A -> Prop
  ; eq : A -> A -> Prop
  ; min : A -> A -> A
  }. 

  Arguments Ops : clear implicits.

  Class t {A : Type} {O : Ops A} : Prop :=
  { PO :> PO.t A le eq
  ; min_proper : Proper (eq ==> eq ==> eq) min
  ; min_ok : forall l r, PreO.min (le := le) l r (min l r)
  }.

  Arguments t : clear implicits.

  Instance min_properI `(tA : t A)
    : Proper (eq ==> eq ==> eq) min.
  Proof. intros. apply min_proper. Qed.

  Record morph `{OA : Ops A} `{OB : Ops B}
    {f : A -> B} : Prop :=
   { f_PO : PO.morph le eq le eq f
   ; f_min : forall a b, eq (f (min a b)) (min (f a) (f b))
   }.

  Arguments morph {A} OA {B} OB f.

  Lemma f_eq {A B OA OB} {tA : t A OA} {tB : t B OB} {f : A -> B} : 
  morph OA OB f -> Proper (eq ==> eq) f.
  Proof. 
    unfold Proper, respectful. intros. apply (PO.f_eq (f_PO H)).
    assumption.
  Qed.

  Lemma morph_id {A OA} (tA : t A OA) 
    : morph OA OA (fun x => x).
  Proof.
  constructor; intros.
  - apply PO.morph_id.
  - apply PO.eq_refl.
  Qed.

  Lemma morph_compose {A B C OA OB OC} 
    (tA : t A OA) (tB : t B OB) (tC : t C OC)
    : forall f g, morph OA OB f 
           -> morph OB OC g 
           -> morph OA OC (fun x => g (f x)).
  Proof.
  intros. constructor; intros.
  - eapply PO.morph_compose; eapply f_PO; eassumption.
  - rewrite <- (f_min H0). rewrite (f_eq H0). reflexivity.
    apply (f_min H).
  Qed.

  Section Props.
  Context `{tA : t A}.

  Lemma min_l : forall l r, le (min l r) l.
  Proof. 
  intros. eapply PreO.min_l. apply min_ok.
  Qed.

  Lemma min_r : forall l r, le (min l r) r.
  Proof. 
  intros. eapply PreO.min_r. apply min_ok.
  Qed.

  Lemma min_comm : forall l r, eq (min l r) (min r l).
  Proof.
  intros.
  apply PO.min_unique with l r.
  - apply min_ok.
  - apply PreO.min_comm. apply min_ok.
  Qed.

  Lemma min_assoc : forall a b c, 
    eq (min a (min b c)) (min (min a b) c).
  Proof. 
  intros.
  apply PO.min_unique with a (min b c).
  - apply min_ok.
  - apply <- (PreO.min_assoc _ a b c); apply min_ok.
  Qed.

  Lemma min_idempotent : forall a, eq (min a a) a.
  Proof.
  intros. apply PO.min_unique with a a.
  apply min_ok. apply PreO.min_idempotent. apply PO.PreO.
  Qed.

  End Props.

  Definition one_ops : Ops True :=
    {| le := fun _ _ => True
     ; eq := fun _ _ => True
     ; min := fun _ _ => I
    |}.

  Definition one : t True one_ops.
  Proof. 
  constructor; intros; auto; unfold Proper, respectful; simpl; auto.
  - apply PO.one. 
  - destruct l, r. constructor; tauto.
  Qed.

  Definition two_ops : Ops bool :=
    {| le := Bool.leb
     ; eq := Logic.eq
     ; min := andb
    |}.

  Definition two : t bool two_ops.
  Proof. constructor; intros; (
    apply PO.two || solve_proper
    ||
   (try constructor;
  repeat match goal with
  | [ b : bool |- _ ] => destruct b
  end; simpl; auto)).
  Qed. 

  Instance prop_ops : Ops Prop :=
    {| le := fun P Q : Prop => P -> Q
     ; eq := fun P Q : Prop => P <-> Q
     ; min := fun P Q : Prop => P /\ Q
    |}.

  Instance prop : t Prop prop_ops.
  Proof. 
    constructor; simpl; intros; constructor; simpl; firstorder.
  Qed.

  Definition pointwise_ops {A B} (O : forall a : A, Ops (B a)) : Ops (forall a, B a) :=
    {| le := pointwise_op (fun a => @le _ (O a))
     ; eq := pointwise_op (fun a => @eq _ (O a))
     ; min :=  (fun f g a => @min _ (O a) (f a) (g a))
    |}.

  Definition pointwise 
    `(tB : forall (a : A), t (B a) (OB a)) : 
     t (forall a, B a) (pointwise_ops OB).
  Proof. constructor; simpl; intros.
    - apply PO.pointwise; intros. eapply @PO; apply tB.
    - unfold respectful, Proper, pointwise_op. intros.
      apply min_proper. apply H. apply H0.
    - constructor; unfold pointwise_op; simpl; intros; apply min_ok.
      apply H. apply H0.
  Qed.

  Definition morph_pointwise {C OC} {tC : t C OC} `(f : B -> A)
    : morph (pointwise_ops (fun _ => OC)) (pointwise_ops (fun _ => OC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply PO.morph_pointwise.
  - unfold pointwise_op. intros. apply PO.eq_refl. 
  Qed. 

  Instance subset (A : Type) : t (A -> Prop) (pointwise_ops (fun _ => prop_ops)) 
    := pointwise (fun _ => prop).

  Definition product_ops `(OA : Ops A) `(OB : Ops B) : Ops (A * B) :=
    {| le := prod_op le le
     ; eq := prod_op eq eq
     ; min := fun (x y : A * B) => (min (fst x) (fst y), min (snd x) (snd y))
    |}.

  Definition product {A OA B OB} (tA : t A OA) (tB : t B OB) 
   : t (A * B) (product_ops OA OB).
  Proof. constructor;
    (apply PO.product; apply PO) ||
    (simpl; intros; 
     constructor; unfold prod_op in *; simpl; intros;
    repeat match goal with
    | [ p : (A * B)%type |- _ ] => destruct p; simpl
    | [ p : _ /\ _ |- _ ] => destruct p; simpl
    | [  |- _ /\ _ ] => split
    | [ |- _ ] => eapply PreO.min_l; apply min_ok
    | [ |- _ ] => eapply PreO.min_r; apply min_ok
    | [ |- _ ] => apply min_proper; assumption
    end).
   eapply PreO.min_greatest. apply min_ok. assumption. assumption.
   eapply PreO.min_greatest. apply min_ok. assumption. assumption.
   Qed. 
   
End MeetLat.

(** A lattice is both a join semi-lattice and a meet semi-lattice;
    it has both a [max] operation and a [min] operation. Again,
    this is basically just copied from the two modules above. *)
Module Lattice.

  Class Ops {A} : Type :=
    { le : A -> A -> Prop
    ; eq : A -> A -> Prop
    ; max : A -> A -> A
    ; min : A -> A -> A
    }.

  Arguments Ops : clear implicits.

  Class t {A : Type} {O : Ops A} : Prop :=
  { PO :> PO.t A le eq
  ; max_proper : Proper (eq ==> eq ==> eq) max
  ; max_ok : forall l r, PreO.max (le := le) l r (max l r)
  ; min_proper : Proper (eq ==> eq ==> eq) min
  ; min_ok : forall l r, PreO.min (le := le) l r (min l r)
  }.

  Arguments t : clear implicits.

  Instance max_properI `(tA : t A)
    : Proper (eq ==> eq ==> eq) max.
  Proof. intros. apply max_proper. Qed.

  Instance min_properI `(tA : t A)
    : Proper (eq ==> eq ==> eq) min.
  Proof. intros. apply min_proper. Qed.

  Record morph `{OA : Ops A} `{OB : Ops B}
    {f : A -> B} : Prop :=
   { f_PO : PO.morph le eq le eq f
   ; f_max : forall a b, eq (f (max a b)) (max (f a) (f b))
   ; f_min : forall a b, eq (f (min a b)) (min (f a) (f b))
   }.

  Arguments morph {A} OA {B} OB f.

  Lemma f_eq {A B OA OB} {tA : t A OA} {tB : t B OB} {f : A -> B} : 
  morph OA OB f -> Proper (eq ==> eq) f.
  Proof. 
    unfold Proper, respectful. intros. apply (PO.f_eq (f_PO H)).
    assumption.
  Qed.

  Lemma morph_id {A OA} (tA : t A OA) 
    : morph OA OA (fun x => x).
  Proof.
  constructor; intros.
  - apply PO.morph_id.
  - apply PO.eq_refl.
  - apply PO.eq_refl.
  Qed.

  Lemma morph_compose {A B C OA OB OC} 
    (tA : t A OA) (tB : t B OB) (tC : t C OC)
    : forall f g, morph OA OB f 
           -> morph OB OC g 
           -> morph OA OC (fun x => g (f x)).
  Proof.
  intros. constructor; intros.
  - eapply PO.morph_compose; eapply f_PO; eassumption.
  - rewrite <- (f_max H0). rewrite (f_eq H0). reflexivity.
    apply (f_max H).
  - rewrite <- (f_min H0). rewrite (f_eq H0). reflexivity.
    apply (f_min H).
  Qed.

  Definition one_ops : Ops True :=
    {| le := fun _ _ => True
     ; eq := fun _ _ => True
     ; max := fun _ _ => I
     ; min := fun _ _ => I
    |}.

  Definition one : t True one_ops.
  Proof. 
  constructor; intros; auto; unfold Proper, respectful; simpl; auto.
  - apply PO.one. 
  - destruct l, r. constructor; tauto.
  - destruct l, r. constructor; tauto.
  Qed.

  Definition two_ops : Ops bool :=
    {| le := Bool.leb
     ; eq := Logic.eq
     ; max := orb
     ; min := andb
    |}.

  Definition two : t bool two_ops.
  Proof. constructor; intros; (
    apply PO.two || solve_proper
    ||
   (try constructor;
  repeat match goal with
  | [ b : bool |- _ ] => destruct b
  end; simpl; auto)).
  Qed. 

  Instance prop_ops : Ops Prop :=
    {| le := fun P Q : Prop => P -> Q
     ; eq := fun P Q : Prop => P <-> Q
     ; max := fun P Q : Prop => P \/ Q
     ; min := fun P Q : Prop => P /\ Q
    |}.

  Instance prop : t Prop prop_ops.
  Proof. 
    constructor; simpl; intros; constructor; simpl; firstorder.
  Qed.

  Definition pointwise_ops {A B} (O : forall a : A, Ops (B a)) : Ops (forall a, B a) :=
    {| le := pointwise_op (fun a => @le _ (O a))
     ; eq := pointwise_op (fun a => @eq _ (O a))
     ; max :=  (fun f g a => @max _ (O a) (f a) (g a))
     ; min :=  (fun f g a => @min _ (O a) (f a) (g a))
    |}.

  Definition pointwise 
    `(tB : forall (a : A), t (B a) (OB a)) : 
     t (forall a, B a) (pointwise_ops OB).
  Proof. constructor; simpl; intros.
    - apply PO.pointwise; intros. eapply @PO; apply tB.
    - unfold respectful, Proper, pointwise_op. intros.
      apply max_proper. apply H. apply H0.
    - constructor; unfold pointwise_op; simpl; intros; apply max_ok.
      apply H. apply H0.
    - unfold respectful, Proper, pointwise_op. intros.
      apply min_proper. apply H. apply H0.
    - constructor; unfold pointwise_op; simpl; intros; apply min_ok.
      apply H. apply H0.
  Qed.

  Definition morph_pointwise {C OC} {tC : t C OC} `(f : B -> A)
    : morph (pointwise_ops (fun _ => OC)) (pointwise_ops (fun _ => OC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply PO.morph_pointwise.
  - unfold pointwise_op. intros. apply PO.eq_refl. 
  - unfold pointwise_op. intros. apply PO.eq_refl.
  Qed. 

  Instance subset (A : Type) : t (A -> Prop) (pointwise_ops (fun _ => prop_ops)) 
    := pointwise (fun _ => prop).

  Definition product_ops `(OA : Ops A) `(OB : Ops B) : Ops (A * B) :=
    {| le := prod_op le le
     ; eq := prod_op eq eq
     ; max := fun (x y : A * B) => (max (fst x) (fst y), max (snd x) (snd y))
     ; min := fun (x y : A * B) => (min (fst x) (fst y), min (snd x) (snd y))
    |}.

  Definition product {A OA B OB} (tA : t A OA) (tB : t B OB) 
   : t (A * B) (product_ops OA OB).
  Proof. constructor;
    (apply PO.product; apply PO) ||
    (simpl; intros; 
     constructor; unfold prod_op in *; simpl; intros;
    repeat match goal with
    | [ p : (A * B)%type |- _ ] => destruct p; simpl
    | [ p : _ /\ _ |- _ ] => destruct p; simpl
    | [  |- _ /\ _ ] => split
    | [ |- _ ] => eapply PreO.max_l; apply max_ok
    | [ |- _ ] => eapply PreO.max_r; apply max_ok
    | [ |- _ ] => eapply PreO.min_l; apply min_ok
    | [ |- _ ] => eapply PreO.min_r; apply min_ok
    | [ |- _ ] => apply max_proper; assumption
    | [ |- _ ] => apply min_proper; assumption
    end).
   eapply PreO.max_least. apply max_ok. assumption. assumption.
   eapply PreO.max_least. apply max_ok. assumption. assumption.
   eapply PreO.min_greatest. apply min_ok. assumption. assumption.
   eapply PreO.min_greatest. apply min_ok. assumption. assumption.
   Qed. 
   
End Lattice.

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
    unfold PreO.top. simpl. pose proof (sup_ok (fun a => a)).
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

  Record morph {f : A -> B} : Prop :=
  { f_L : L.morph LOps LOps f
  ; f_sup : forall {Ix : Type} (g : Ix -> A), L.eq (f (sup g)) (sup (fun i => f (g i)))
  ; f_top : L.eq (f top) top
  }.

  Arguments morph : clear implicits.

  Lemma f_eq {f : A -> B} :
    morph f -> Proper (L.eq ==> L.eq) f.
  Proof. 
    intros. apply (L.f_eq (f_L H)).
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
  - intros. rewrite <- (f_sup H0). rewrite (f_eq H0).
    reflexivity. rewrite (f_sup H). reflexivity.
  - rewrite <- (f_top H0). rewrite (f_eq H0).
    reflexivity. rewrite (f_top H). reflexivity.
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
  Instance prop_ops : Ops Prop :=
    {| LOps := L.prop_ops
     ; sup := (fun _ f => exists i, f i)
    |}.

  Instance prop : t Prop prop_ops.
  Proof. constructor; simpl; intros.
  - apply L.prop.
  - constructor; unfold pointwise_relation in H; simpl in H;
     intros [??]; eexists; apply H; eassumption.
  - constructor; simpl; intros.
    + exists i. assumption.
    + destruct H0. apply (H x). assumption.
  - split; intros. 
    + destruct H as (xa & i & fia). exists i. intuition.
    + destruct H as (i & xa & fia). split. assumption.
      exists i. assumption.
  Qed.

  Definition pointwise_ops `(OB : forall a : A, Ops (B a))
    : Ops (forall a, B a) :=
    {| LOps := L.pointwise_ops (fun _ => LOps)
     ; sup := fun _ f => fun x => sup (fun i => f i x)
    |}.

  Definition pointwise `(forall a : A, t (B a) (OB a))
    : t (forall a, B a) (pointwise_ops OB).
  Proof. constructor.
  - apply L.pointwise. intros. apply L.
  - simpl. unfold Proper, respectful, pointwise_relation, pointwise_op.
    intros. apply sup_proper. unfold pointwise_relation.
    intros a'. apply H0.
  - constructor; simpl; unfold pointwise_op; intros.
    pose proof (@sup_ok _ _ (H a) Ix (fun i => f i a)).
    apply H0.
    pose proof (@sup_ok _ _ (H a) Ix (fun i => f i a)).
    apply H1. intros. apply H0.
  - simpl. unfold pointwise_op. intros.
    apply (sup_distr (t := H a)).
  Qed.

  Lemma sup_pointwise {A} {OA} {X : t A OA} {Ix Ix'} (f : Ix -> A) (g : Ix' -> A)
  : (forall (i : Ix), exists (j : Ix'), L.le (f i) (g j))
  -> L.le (sup f) (sup g).
  Proof.
  intros. eapply PreO.sup_least. apply sup_ok. intros.
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

Module F := Frame.

Require Import LPReal.
Local Open Scope LPR.

(** Supremum over directed sets (i.e., join-semilattices)
    commutes with addition *)
Lemma LPRsup_sum_jlat : forall A `(I : JoinLat.t A),
  forall (f g : A -> LPReal) ,
    (forall n m : A, JoinLat.le n m -> f n <= f m) ->
    (forall n m : A, JoinLat.le n m -> g n <= g m) ->
    LPRsup (fun x : A => f x + g x) = LPRsup f + LPRsup g.
Proof.
intros. eapply LPRsup_sum_lattice.
intros. eapply PreO.max_l. apply JoinLat.max_ok.
intros. eapply PreO.max_r. apply JoinLat.max_ok.
assumption. assumption.
Qed. 


Delimit Scope Val_scope with Val.
(** This module defines valuations. Valuations like measures, rather than
    being defined on sigma-algebras of subsets, they are defined on
    locales (= frames).
*)
Module Val.

Require Import Equalities Coq.Structures.Orders GenericMinMax.

(** This describes the property of when a valuation is
    _continuous_. This condition is analagous to countable additivity
    in measure theory. Essentially, if I have a sequence of subsets
    which is getting bigger and bigger, then the measure of the union
    of the subsets is the supremum of the measures of each of the
    subsets in the sequence. *)
Definition ContinuousV {A OA} (X : F.t A OA) (mu : (A -> LPReal))
  := forall I `{JL : JoinLat.t I} (f : I -> A)
       (fmono : forall (m n : I), JoinLat.le m n -> L.le (f m) (f n))
       , mu (F.sup f) = LPRsup (fun n => mu (f n)).

  Record t {A OA} {X : F.t A OA} :=
  { val :> A -> LPReal
  ; strict : val F.bottom = 0
  ; monotonic : forall (U V : A), L.le U V -> val U <= val V
  ; modular : forall (U V : A),
      val U + val V = val (L.max U V) + val (L.min U V)
  ; continuous : ContinuousV X val
  }.

  Arguments t {A} {OA} X.

  (** If two elements of the frame are equal, they are assigned the
      same measure. *)
  Lemma val_iff : forall `{X : F.t A} (mu : t X) (U V : A),
    L.eq U V -> mu U = mu V.
  Proof. 
   intros. apply LPRle_antisym; apply monotonic; 
   rewrite H; apply PreO.le_refl.
  Qed.

  (** We say one valuation [mu] is less than or equal to another valuation
      [nu] if, for every open [P], the measure [mu] assigns to [P] is
      less than or equal to the measure [nu] assigns to [P] *)
  Definition le `{X : F.t A} (mu nu : t X) := forall P, mu P <= nu P.

  Infix "<=" := le : Val_scope.

  Lemma le_refl `{X : F.t A} (mu : t X) : (mu <= mu)%Val.
  Proof. unfold le. intros. apply monotonic. apply PreO.le_refl. Qed.

  Definition eq `{X : F.t A} (mu nu : t X) := forall P, mu P = nu P.
  Infix "==" := eq : Val_scope.

  (** Lower reals have a partial order. *)
  Definition POLPR : PO.t LPReal LPRle Logic.eq.
  Proof. constructor; intros.
  - constructor; intros. apply LPRle_refl.  eapply LPRle_trans; eassumption.
  - unfold Proper, respectful. intros. subst. reflexivity.
  - eapply LPRle_antisym; eassumption.
  Qed.

  (** Our definition of "<=" on valuations induces a partial order structure. *)
  Instance PO `{X : F.t A} : PO.t (t X) le eq 
    := PO.map val (PO.pointwise (fun _ : A => POLPR)).

  Lemma le_trans `{X : F.t A} (x y z : t X) : (x <= y -> y <= z -> x <= z)%Val.
  Proof.
    intros. eapply PreO.le_trans; eassumption.
  Qed.

Require Import FunctionalExtensionality ProofIrrelevance.
Lemma eq_compat : forall `{X : F.t A} (mu nu : t X), (mu == nu)%Val -> mu = nu. 
Proof.
intros.
unfold eq in *.
destruct mu, nu. simpl in *.
assert (val0 = val1).
apply functional_extensionality. assumption.
induction H0.
pose proof (proof_irrelevance _ strict0 strict1).
induction H0.
pose proof (proof_irrelevance _ monotonic0 monotonic1).
induction H0.
pose proof (proof_irrelevance _ modular0 modular1).
induction H0.
pose proof (proof_irrelevance _ continuous0 continuous1).
induction H0.
reflexivity.
Qed.

(** The valuation which assigns zero measure to every open. This is the
    bottom element of the partial order we defined on valuations. *)
Definition zero `{X : F.t A} : t X.
Proof. refine (
  {| val := fun _ => 0 |}
); intros.
- reflexivity.
- apply LPRle_refl.
- reflexivity.
- unfold ContinuousV. intros. simpl. symmetry.
  apply LPRle_antisym.
  + unfold LPRle. simpl. intros. destruct H. assumption.
  + apply LPRzero_min.
Defined.

  Instance val_proper `{X : F.t A} : Proper (Logic.eq ==> L.eq ==> Logic.eq) (@val _ _ X).
  Proof.
   unfold Proper, respectful. intros. rewrite H. apply val_iff.
   assumption.
  Qed.

Notation "'0'" := zero : Val_scope.

Require Import Ring.

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 = (andLq + orLq) + (andRq + orRq).
Proof. intros. ring. Qed.

(** We can add two valuations by adding the measure they assign to each open. *)
Definition add `{X : F.t A} (mu nu : t X) : t X.
Proof. refine (
  {| val := fun P => mu P + nu P |}
); intros.
- rewrite strict. rewrite strict. ring.
- apply LPRplus_le_compat; apply monotonic; assumption.
- rewrite qredistribute. 
  rewrite (qredistribute (mu (L.max _ _))).
  apply LPRplus_eq_compat; apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite (LPRsup_sum_jlat I).
  apply LPRplus_eq_compat;
   eapply continuous; assumption.
   assumption.
  intros. apply monotonic. apply fmono. assumption.
  intros. apply monotonic. apply fmono. assumption.
Defined.

(** Scale a valuation by a constant *)
Definition scale `{X : F.t A} (c : LPReal) (mu : t X) : t X.
Proof. refine (
  {| val := fun P => c * mu P |}
); intros.
- rewrite strict. ring.
- apply LPRmult_le_compat. apply LPRle_refl.
  apply monotonic; assumption.
- replace (c * mu U + c * mu V) with (c * (mu U + mu V)) by ring.
  replace (c * mu _ + c * mu _) 
  with (c * (mu (L.max U V) + mu (L.min U V))) by ring.
  apply LPRmult_eq_compat. reflexivity.
  apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite continuous by eassumption.
  apply LPRsup_scales.
Defined.

Infix "+" := add : Val_scope.
Infix "*" := scale : Val_scope.

Lemma zero_min `{X : F.t A} : forall (mu : t X), (0 <= mu)%Val.
Proof. intros. unfold le. intros. simpl. apply LPRzero_min. Qed.

(** We can map a continuous map over a valuation. *)
Definition map {A OA B OB} {X : F.t A OA} {Y : F.t B OB} (f : F.cmap OA OB)
  (mu : t X) : t Y.
Proof.
refine (
  {| val := fun x => mu (F.finv f x) |}
).
Proof. 
- pose proof (F.f_bottom (F.cont f)).
  rewrite H. apply strict.
- intros. apply monotonic.
   apply (L.f_PO (F.f_L (F.cont f))).
   apply H.
- intros. unfold L.min, L.max. 
  rewrite (L.f_min (F.f_L (F.cont f))).
  rewrite (L.f_max (F.f_L (F.cont f))).
  apply modular.
- unfold ContinuousV. intros.
  rewrite (F.f_sup (F.cont f)).
  eapply continuous. eassumption. intros. 
  apply (L.f_PO (F.f_L (F.cont f))). apply fmono. assumption.
Defined.

(** If we view [F.prop] as locale corresponding to the 1-point set, then
    [unit_prop] is the unique probability distribution we can define for the 1-point 
    set; it puts all its mass (i.e., a measure of 1) on that single point. *)
Definition unit_prop : t F.prop.
Proof.
refine (
  {| val := fun P => LPRindicator P |}
); simpl; intros.
- apply LPRind_false. unfold not. intros. destruct H.
  contradiction.
- unfold L.le in H. simpl in H. apply LPRind_imp. assumption.
- unfold L.max, L.min. simpl. rewrite (SRadd_comm LPRsrt (LPRindicator (U \/ V))). 
  apply LPRind_modular.
- unfold ContinuousV. intros.
  apply LPRind_exists. 
Defined.

(** We can now define a Dirac delta distribution, which is a probability distribution
    which puts all its mass on a single point. Since a point is just a continuous map from
    the one-point set, a Dirac delta just maps this continuous function over the
    probability distribution [unit_prop] for the one-point set. *)
Definition unit {A OA} {X : F.t A OA} (x : F.point OA)
  : t X := map x unit_prop.

Lemma unit_prob {A OA} {X : F.t A OA} (x : F.point OA) : unit x (F.top) = 1.
Proof.
simpl. apply LPRind_true.
rewrite (F.f_top (F.cont x)). simpl. exists True. constructor.
Qed.

Definition pointwise {A B : Type} (cmp : B -> B -> Prop)
  (f g : A -> B) : Prop := forall (a : A), cmp (f a) (g a).

Definition supValuation {A OA} {X : F.t A OA}
  I `{JL : JoinLat.t I} (f : I -> t X)
    (fmono : forall (m n : I), JoinLat.le m n -> (f m <= f n)%Val)
 : t X.
Proof.
refine (
  {| val := fun P => LPRsup (fun i => f i P) |}).
- apply LPRle_antisym. apply LPRsup_le.
  intros. rewrite strict. apply LPRle_refl. apply LPRzero_min.
- intros. apply LPRsup_le. intros.
  apply LPRsup_ge2. exists a. apply monotonic. assumption.
- intros. unfold le in fmono.
  repeat  erewrite <- LPRsup_sum_jlat by auto.
  apply LPRsup_eq_pointwise. intros. apply modular.
- unfold ContinuousV. intros. apply LPRle_antisym. 
  apply LPRsup_le. intros. rewrite continuous.
  apply LPRsup_le. intros. apply LPRsup_ge2. exists a0.
  apply LPRsup_ge2. exists a. apply LPRle_refl. assumption. assumption.
  apply LPRsup_le. intros. apply LPRsup_le. intros.
  apply LPRsup_ge2. exists a0. apply monotonic.
  apply F.sup_ok.
Defined.

(** The nth iteration of the fixpoint of a functional on
    measures *)
Fixpoint fixn {A OA} {X : F.t A OA} 
  (f : t X -> t X) (n : nat)
  : t X
  := match n with
  | 0 => 0%Val
  | S n' => f (fixn f n')
  end.

(** If our valuation functional is monotonic, then the
    fixpoint is nondecreasing. *)
Lemma fixnmono {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : forall (n : nat), (fixn f n <= fixn f (S n))%Val.
Proof. intros. induction n.
simpl. unfold le; intros. simpl. apply LPRzero_min.
simpl. apply fmono. assumption.
Qed.

Lemma fixnmono2 {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : forall (m n : nat), (JoinLat.le m n)%nat -> (fixn f m <= fixn f n)%Val.
Proof. intros. induction H. apply le_refl. 
eapply le_trans. eassumption. apply fixnmono. assumption.
Qed.

(** If we have a valuation functional which is monotonic, we can take
    its fixpoint! *)
Definition fixValuation {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : t X
  := supValuation nat (fun n => (fixn f n)) 
     (fixnmono2 f fmono).

Lemma fixValuation_subProb {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  (fbounded : forall v, val v F.top <= 1 -> val (f v) F.top <= 1)
  : (fixValuation f fmono) F.top <= 1.
Proof. unfold fixValuation.  simpl. apply LPRsup_le.
intros n. induction n. simpl. apply LPRzero_min.
simpl. apply fbounded. assumption.
Qed.

Theorem fixValuation_fixed_u {A OA} {X : F.t A OA} 
  (f : t X -> t X)
  (fmono : forall u v : t X, (u <= v)%Val -> (f u <= f v)%Val)
  : (fixValuation f fmono <= f (fixValuation f fmono))%Val.
Proof.
unfold le. intros P. apply LPRsup_le. intros n. destruct n; simpl.
- apply LPRzero_min.
- apply fmono. unfold le; intros. simpl.
  apply LPRsup_ge2. exists n. apply LPRle_refl.
Qed.

(** Definition of when a functional is continuous. *)
Definition Continuous {A OA} {X : F.t A OA} (f : t X -> t X) 
  := forall I `(JL : JoinLat.t I) (nonempty : I) (g : I -> t X)
       (gmono : forall m n : I, JoinLat.le m n -> (g m <= g n)%Val)
       (P : A),
      (f (supValuation I g gmono)) P
    = LPRsup (fun x : I => f (g x) P).

(** If a functional is continuous, then we indeed reach a fixpoint
    when we apply [fixValuation]. *)
Theorem fixValuation_fixed {A OA} {X : F.t A OA} (f : t X -> t X)
  (fmono : forall u v : t X, (u <= v)%Val -> (f u <= f v)%Val)
  : Continuous f
  -> f (fixValuation f fmono) = fixValuation f fmono.
Proof.
intros.
apply eq_compat. unfold eq. intros. apply LPRle_antisym.
-  unfold Continuous in H.
  unfold fixValuation at 1. rewrite H.
  apply LPRsup_le. intros n.
  simpl. apply LPRsup_ge2. exists (S n). apply LPRle_refl. exact 0%nat.
- apply fixValuation_fixed_u.
Qed.

(** * Reasoning about measures *)

(** A set of techniques for reasoning about measures. *)

(** Binary version of the union bound. *)
Lemma union_bound2 {A OA} {X : F.t A OA} {mu : t X}
  (P Q : A)
  : mu (L.min P Q) <= mu P + mu Q.
Proof.
rewrite modular. eapply LPRle_trans.
Focus 2. eapply LPRplus_le_compat.
apply LPRzero_min. apply LPRle_refl.
rewrite (SRadd_0_l LPRsrt). 
apply LPRle_refl.
Qed.

(** Finite version of the union bound. *)
Lemma union_bound {A OA} {X : F.t A OA} {mu : t X}
  (xs : list A)
  : mu (List.fold_right L.min F.bottom xs) <=
    List.fold_right LPRplus 0 (List.map (val mu) xs).
Proof.
induction xs; simpl.
- rewrite strict. apply LPRle_refl.
- eapply LPRle_trans. Focus 2. 
  eapply LPRplus_le_compat.
  Focus 2. apply IHxs. apply LPRle_refl.
  apply union_bound2.
Qed.

(** Finite distributions *)
Require Import Qnn.
Section FinDist.
Context {A} {OA} {X : F.t A OA}.

Fixpoint uniform_helper (p : LPReal) (xs : list (F.point OA)) := match xs with
  | nil => 0%Val
  | (x :: xs')%list => (p * unit x + uniform_helper p xs')%Val
end.

Lemma uniform_helper_weight {p : LPReal} {xs : list (F.point OA)}
  : uniform_helper p xs F.top = LPRQnn (Qnnnat (length xs)) * p.
Proof.
induction xs. 
- simpl. ring. 
- simpl. pose proof (unit_prob a) as UP. simpl in UP.
  rewrite UP. rewrite IHxs. rewrite <- LPRQnn_plus.
  ring.
Qed.

(** A uniform distribution over a finite, non-empty list
    of elements. *)
Definition uniform {n : nat} (xs : Vector.t (F.point OA) (S n)) :=
  uniform_helper (LPRQnn (Qnnfrac (S n))) (Vector.to_list xs).

Lemma Vector_length {T} {n : nat} {xs : Vector.t T n}
  : length (Vector.to_list xs) = n.
Proof. induction xs.
- reflexivity.
- unfold Vector.to_list in *. simpl. rewrite IHxs. reflexivity.
Qed.

Lemma uniform_prob : forall {n : nat} {xs : Vector.t (F.point OA) (S n)}
  , (uniform xs) F.top = 1.
Proof.
intros. unfold uniform.
rewrite uniform_helper_weight. rewrite Vector_length.
rewrite LPRQnn_mult. rewrite Qnnnatfrac. reflexivity.
Qed.

End FinDist.

End Val.

Module ValNotation.
Coercion Val.val : Val.t >-> Funclass.  Delimit Scope Val_scope with Val.

Infix "<=" := Val.le : Val_scope.
Infix "==" := Val.eq : Val_scope.
Infix "+" := Val.add : Val_scope.
Infix "*" := Val.scale : Val_scope.
Notation "'0'" := Val.zero : Val_scope.

End ValNotation.