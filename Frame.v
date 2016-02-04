Require Import SetoidClass Coq.Classes.Morphisms.
Generalizable All Variables.

Definition prod_op {A B} (fA : A -> A -> Prop) (fB : B -> B -> Prop)
   (x y : A * B) := fA (fst x) (fst y) /\ fB (snd x) (snd y).

Definition map_op {A B} (f : A -> B) (P : B -> B -> Prop) (x y : A) : Prop := 
  P (f x) (f y).

Definition pointwise_op {A} {B : A -> Type} (P : forall a, B a -> B a -> Prop)
  (f g : forall a, B a) := forall a, P a (f a) (g a).

Module PreO.
  Class t {A : Type} {le : A -> A -> Prop} : Prop :=
  { le_refl : forall x, le x x
  ; le_trans : forall x y z, le x y -> le y z -> le x z
  }.

  Arguments t : clear implicits.

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

  Definition top (t : A) : Prop := forall a, a <= t.
  Definition bottom (b : A) : Prop := forall a, b <= a.

  Record max {l r m : A} : Prop :=
  { max_l     : l <= m
  ; max_r     : r <= m
  ; max_least : forall m', l <= m' -> r <= m' -> m <= m'
  }.

  Arguments max : clear implicits.

  Lemma max_comm : forall l r m, max l r m -> max r l m.
  Proof.
  intros. constructor.
  - apply H.
  - apply H.
  - intros. apply H; assumption.
  Qed.

  Record min {l r m : A} : Prop :=
  { min_l        : m <= l
  ; min_r        : m <= r
  ; min_greatest : forall m', m' <= l -> m' <= r -> m' <= m
  }.

  Arguments min : clear implicits.

  Lemma min_comm : forall l r m, min l r m -> min r l m.
  Proof.
  intros. constructor.
  - apply H.
  - apply H.
  - intros. apply H; assumption.
  Qed.

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

  Record sup {I : Type} (f : I -> A) (m : A) : Prop :=
  { sup_ge : forall i, f i <= m
  ; sup_least : forall m', (forall i, f i <= m') -> m <= m'
  }.

  Record inf {I : Type} (f : I -> A) (m : A) : Prop :=
  { inf_le : forall i, m <= f i
  ; inf_greatest : forall m', (forall i, m' <= f i) -> m' <= m
  }.


  End Facts.

  Definition one : t True (fun _ _ => True).
  Proof. constructor; auto.
  Qed.

  Definition two : t bool Bool.leb.
  Proof. constructor. 
  - intros; auto. destruct x; simpl; trivial.
  - destruct x, y, z; auto. simpl in *. congruence.
  Qed.

  Definition product `(tA : t A leA) `(tB : t B leB) 
   : t (A * B) (prod_op leA leB).
  Proof. constructor.
   - destruct x. split; apply le_refl.
   - unfold prod_op; intros. 
     destruct x, y, z; simpl in *;
     intuition; (eapply PreO.le_trans; eassumption).
  Qed.

  Definition map `(f : A -> B) `(tB : t B leB) 
    : t A (fun x y => leB (f x) (f y)).
  Proof. constructor; intros.
  - apply le_refl.
  - eapply le_trans; eauto.
  Qed.

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

  Instance prop : t Prop (fun P Q => P -> Q).
  Proof. 
    constructor; auto.
  Qed.

  Instance subset (A : Type) : t (A -> Prop) _ := pointwise (fun _ => prop).

End PreO.

Arguments PreO.max {A} {le} _ _ _ : clear implicits.
Arguments PreO.min {A} {le} _ _ _ : clear implicits.

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


  Instance morph_properI `(tA : t A leA eqA) `(tB : t B leB eqB) (f : A -> B)
    : morph leA eqA leB eqB f -> Proper (eqA ==> eqB) f.
  Proof. 
    intros. destruct H. unfold Proper, respectful. apply f_eq0. 
  Qed.

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

(** Join semi-lattices, or directed sets. Natural numbers are
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
  }.

  Arguments morph : clear implicits.

  Lemma f_eq {f : A -> B} :
    morph f -> Proper (L.eq ==> L.eq) f.
  Proof. 
    intros. apply (L.f_eq (f_L H)).
  Qed.

  Lemma f_bottom {f : A -> B} : morph f -> L.eq (f bottom) bottom.
  Proof.
  intros. unfold bottom. rewrite (f_sup H). apply sup_proper.
  unfold pointwise_relation. intros. contradiction.
  Qed.

  End Morph.

  Arguments morph {A} OA {B} OB f.

  Section MorphProps.
  Context {A OA} {tA : t A OA}.

  Lemma morph_id : morph OA OA (fun x => x).
  Proof. 
   intros. constructor. apply L.morph_id. apply L.
   reflexivity.
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

  Definition morph_pointwise {A B C OC} {tC : t C OC} (f : B -> A)
    : morph (pointwise_ops (fun _ : A => OC)) (pointwise_ops (fun _ : B => OC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply L.morph_pointwise.
  - unfold pointwise_op. intros. apply PO.eq_refl. 
  Qed. 

  Instance subset_ops A : Ops (A -> Prop) := pointwise_ops (fun _ => prop_ops).
  
  Instance subset (A : Type) : t (A -> Prop) (subset_ops A):= 
     pointwise (fun _ : A => prop).

  (** continuous map on locales *)
  Record cmap {A OA} {B OB} := 
  { finv :> B -> A
  ; cont : morph OB OA finv
  }.

  Arguments cmap {A} OA {B} OB.

  Definition point {A} (OA : Ops A) := cmap prop_ops OA.

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

Module Val.

Require Import Equalities Orders GenericMinMax.

(** This describes the property of when a valuation is
    _continuous_. This condition is analagous to countable additivity
    in measure theory. Essentially, if I have a sequence of subsets
    which is getting bigger and bigger, then the measure of the union
    of the subsets is the supremum of the measures of each of the
    subsets in the sequence. *)
Definition ContinuousV {A OA} (X : F.t A OA) (mu : (A -> LPReal))
  := forall {I} `{JL : JoinLat.t I} (f : I -> A)
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

  Lemma val_iff : forall `{X : F.t A} (mu : t X) (U V : A),
    L.eq U V -> mu U = mu V.
  Proof. 
   intros. apply LPRle_antisym; apply monotonic; 
   rewrite H; apply PreO.le_refl.
  Qed.

  Definition le `{X : F.t A} (mu nu : t X) := forall P, mu P <= nu P.

  Infix "<=" := le : Val_scope.
  Delimit Scope Val_scope with Val.

  Lemma le_refl `{X : F.t A} (mu : t X) : (mu <= mu)%Val.
  Proof. unfold le. intros. apply monotonic. apply PreO.le_refl. Qed.

  Definition eq `{X : F.t A} (mu nu : t X) := forall P, mu P = nu P.
  Infix "==" := eq : Val_scope.

  Definition POLPR : PO.t LPReal LPRle Logic.eq.
  Proof. constructor; intros.
  - constructor; intros. apply LPRle_refl.  eapply LPRle_trans; eassumption.
  - unfold Proper, respectful. intros. subst. reflexivity.
  - eapply LPRle_antisym; eassumption.
  Qed.

  Instance PO `{X : F.t A} : PO.t (t X) le eq 
    := PO.map val (PO.pointwise (fun _ : A => POLPR)).

  Lemma le_trans `{X : F.t A} (x y z : t X) : (x <= y -> y <= z -> x <= z)%Val.
  Proof.
    intros. eapply PreO.le_trans; eassumption.
  Qed.

Require Import FunctionalExtensionality.
Lemma eq_compat_OK 
  (proof_irrel : forall (P : Prop) (x y : P), x = y)
  : forall `{X : F.t A} (mu nu : t X), eq mu nu -> mu = nu. 
Proof.
intros.
unfold eq in *.
destruct mu, nu. simpl in *.
assert (val0 = val1).
apply functional_extensionality. assumption.
induction H0.
pose proof (proof_irrel _ strict0 strict1).
induction H0.
pose proof (proof_irrel _ monotonic0 monotonic1).
induction H0.
pose proof (proof_irrel _ modular0 modular1).
induction H0.
pose proof (proof_irrel _ continuous0 continuous1).
induction H0.
reflexivity.
Qed.

Axiom eq_compat : forall `{X : F.t A} (mu nu : t X)
  , eq mu nu -> mu = nu.

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

Definition unit {A OA} {X : F.t A OA} (x : F.point OA)
  : t X := map x unit_prop.

Definition pointwise {A B : Type} (cmp : B -> B -> Prop)
  (f g : A -> B) : Prop := forall (a : A), cmp (f a) (g a).

(** * Integration *)

(** An inductive definition of simple functions. I hesitate to
    call them functions because they aren't necessarily computable.
    *)

Module Simple.
Inductive t `{X : F.t A} :=
  | Ind : A -> t
  | Scale : LPReal -> t -> t
  | Add : t -> t -> t.

Arguments t {A} {OA} X.

(** Definition of how to integrate simple functions *)
Fixpoint Integral `{X : F.t A} (s : t X) 
  (mu : Val.t X) : LPReal := match s with
  | Ind P => mu P
  | Scale c f => c * Integral f mu
  | Add f g => Integral f mu + Integral g mu
  end.

Delimit Scope Simple_scope with Simple.
Infix "+" := Add : Simple_scope.
Infix "*" := Scale : Simple_scope.

Definition le `{X : F.t A} (x y : t X) := 
  forall (mu : Val.t X), Integral x mu <= Integral y mu.

Definition eq `{X : F.t A} (x y : t X) := 
  forall (mu : Val.t X), Integral x mu = Integral y mu.

Instance PO `{X : F.t A} : PO.t (t X) le eq
  := PO.map Integral 
     (PO.pointwise (fun _ : Val.t X => Val.POLPR)).

Lemma int_proper1 `{X : F.t A} : Proper (Logic.eq ==> Val.eq ==> Logic.eq) (@Integral _ _ X).
Proof.
 unfold Proper, respectful. unfold eq. intros.  subst. induction y. 
 - simpl. apply H0. 
 - simpl. rewrite IHy. ring.
 - simpl. rewrite IHy1, IHy2. ring.
Qed.

Instance int_proper `{X : F.t A} : Proper (eq ==> Val.eq ==> Logic.eq) (@Integral _ _ X).
Proof.
 unfold Proper, respectful. unfold eq. intros. rewrite H.
 apply int_proper1. reflexivity. assumption.
Qed.

Lemma le_refl `{X : F.t A} : forall (x : t X), le x x.
Proof.
  apply PreO.le_refl.
Qed.

Infix "<=" := le : Simple_scope.
Infix "==" := eq : Simple_scope.

Lemma le_plus `{X : F.t A} : forall (f f' g g' : t X),
  (f <= f' -> g <= g' -> f + g <= f' + g')%Simple.
Proof.
intros. unfold le in *. intros. simpl. apply LPRplus_le_compat; auto.
Qed.

Lemma le_scale `{X : F.t A} : forall (c c' : LPReal) (f f' : t X),
  c <= c' -> (f <= f' -> c * f <= c' * f')%Simple.
Proof.
intros.  unfold le in *. intros. simpl.
apply LPRmult_le_compat. assumption. apply H0.
Qed.

Lemma int_monotonic_val `{X : F.t A} {f : t X}
  {mu mu' : Val.t X}
  : (mu <= mu')%Val -> Integral f mu <= Integral f mu'.
Proof. intros. induction f; simpl.
- apply H.
- apply LPRmult_le_compat. apply LPRle_refl. apply IHf.
- simpl. apply LPRplus_le_compat; assumption.
Qed.

Lemma int_adds_val `{X : F.t A} {f : t X}
  {mu mu' : Val.t X}
  : Integral f (mu + mu')%Val
  = Integral f mu + Integral f mu'.
Proof.
induction f; simpl.
- reflexivity.
- rewrite IHf. ring. 
- simpl in *. rewrite IHf1. rewrite IHf2. ring.
Qed.

Lemma int_scales_val `{X : F.t A} {c : LPReal} {f : t X}
  {mu : Val.t X}
  : Integral f (c * mu)%Val 
  = c * Integral f mu.
Proof.
induction f; simpl.
- reflexivity.
- rewrite IHf. ring. 
- simpl in *. rewrite IHf1. rewrite IHf2. ring.
Qed.

Lemma int_bottom `{X : F.t A} : forall {mu : Val.t X}
  , Integral (Ind F.bottom) mu = 0.
Proof.
intros. simpl. apply strict.
Qed.

Fixpoint map_concrete {B} `{X : F.t A} `{Y : F.t B}
  (f : A -> B) (s : t X) : t Y := match s with
  | Ind P => Ind (f P)
  | Scale c s' => Scale c (map_concrete f s')
  | Add l r => Add (map_concrete f l) (map_concrete f r)
  end.

Definition map {A B OA OB} {X : F.t A OA} {Y : F.t B OB}
  (f : F.cmap OA OB) : t Y -> t X
  := map_concrete (F.finv f).

End Simple.

Module RealFunc.

  Record t {A} `{X : F.t A} :=
    { func :> nat -> Simple.t X
    ; mono : forall m n, (m <= n)%nat -> Simple.le (func m) (func n) }.

  Arguments t {A} {OA} X.

  Definition simple `{X : F.t A} (f : Simple.t X) : t X.
  Proof. refine (
   {| func := fun _ => f |}).
  intros. apply Simple.le_refl.
  Defined.

  Definition add `{X : F.t A} (f g : t X) : t X.
  Proof. refine (
    {| func n := Simple.Add (f n) (g n) |}
  ).
  intros. unfold Simple.le. intros. 
  apply Simple.le_plus; apply mono; assumption.
  Defined.

  Infix "+" := add : RFunc_scope.
  Delimit Scope RFunc_scope with RFunc.

  Definition scale `{X : F.t A} (c : LPReal) (f : t X) : t X.
  Proof. refine (
    {| func n := Simple.Scale c (f n) |}
  ).
  intros. apply Simple.le_scale. apply LPRle_refl. apply mono. assumption.
  Defined.

  Infix "*" := scale : RFunc_scope.

  Definition map {A OA} {X : F.t A OA} {B OB} {Y : F.t B OB} (f : F.cmap OA OB) 
    (g : t Y) : t X.
  Proof. refine (
    {| func := fun i => Simple.map f (g i) |}
  ). destruct g. simpl.
  Abort.

  Definition integral `{X : F.t A} (f : t X) (mu : Val.t X) :=
   LPRsup (fun i => Simple.Integral (f i) mu).

  Definition le `{X : F.t A} (f g : t X) := forall (mu : Val.t X),
    integral f mu <= integral g mu.

  Definition eq `{X : F.t A} (f g : t X) := forall (mu : Val.t X),
    integral f mu = integral g mu.

  Instance PO `{X : F.t A} : PO.t (t X) le eq
    := PO.map (fun f => (fun mu => integral f mu)) 
       (PO.pointwise (fun _ : Val.t X => Val.POLPR)).

  Infix "<=" := le : RFunc_scope.
  Infix "==" := eq : RFunc_scope.

  Instance int_proper `{X : F.t A} : Proper (eq ==> Val.eq ==> Logic.eq) (@integral _ _ X).
  Proof.
   unfold Proper, respectful. unfold eq. intros. unfold integral in *.
   rewrite H. apply LPRsup_eq_pointwise. intros n. apply Simple.int_proper.
   unfold Simple.eq. reflexivity. assumption.
  Qed.

  Lemma int_simple `{X : F.t A} : forall (f : Simple.t X) (mu : Val.t X),
      integral (simple f) mu = Simple.Integral f mu.
  Proof.
    intros. unfold integral, simple. simpl. apply LPRsup_constant. exact 0%nat.
  Qed.

  Lemma int_zero `{X : F.t A} : forall {mu : Val.t X}
    , integral (simple (Simple.Ind F.bottom)) mu = 0.
  Proof.
    intros.
    rewrite int_simple. simpl.
    rewrite strict. ring.
  Qed.

  Lemma int_adds `{X : F.t A} : forall (f g : t X) (mu : Val.t X),
     integral (f + g)%RFunc mu = integral f mu + integral g mu.
  Proof.
    intros. unfold integral. 
    apply LPRsup_nat_ord; intros; apply mono; assumption.
  Qed.

  Lemma le_plus `{X : F.t A} : forall (f f' g g' : t X),
    (f <= f' -> g <= g' -> f + g <= f' + g')%RFunc.
  Proof. 
    unfold le in *. intros. repeat rewrite int_adds.
    apply LPRplus_le_compat; auto.
  Qed.

  Lemma int_scales `{X : F.t A} : forall (c : LPReal) (f : t X) (mu : Val.t X)
    , integral (c * f)%RFunc mu = c * integral f mu.
  Proof.
    intros. unfold integral. rewrite LPRsup_scales. apply LPRsup_eq_pointwise.
    intros n. simpl. reflexivity.
  Qed.

Lemma int_monotonic_val `{X : F.t A} {f : t X}
  {mu mu' : Val.t X}
  : (mu <= mu')%Val -> integral f mu <= integral f mu'.
Proof. 
  intros. unfold integral. apply LPRsup_monotonic. intros.
  apply Simple.int_monotonic_val. assumption.
Qed.

Lemma int_adds_val `{X : F.t A} {f : t X}
  {mu mu' : Val.t X}
  : integral f (mu + mu')%Val 
  = integral f mu + integral f mu'.
Proof.
unfold integral. 
rewrite <- LPRsup_nat_ord by (intros; apply mono; assumption).
apply LPRsup_eq_pointwise. intros. apply Simple.int_adds_val.
Qed.

Lemma int_scales_val `{X : F.t A} {c : LPReal} {f : t X}
  {mu : Val.t X}
  : integral f (c * mu)%Val
  = c * integral f mu.
Proof.
unfold integral. rewrite LPRsup_scales. apply LPRsup_eq_pointwise.
intros. apply Simple.int_scales_val.
Qed.

Definition eval {A OA} {X : F.t A OA} (f : t X) (x : F.point OA) : LPReal :=
  integral f (unit x).

End RealFunc.

End Val.

Module SubsetVal.

Module RF := Val.RealFunc.

Definition O := F.subset.

Definition Val (A : Type) := Val.t (O A).

Definition point {A} (a : A) : F.point (F.subset_ops A).
 refine (
  {| F.finv := fun P => P a |}
). simpl. constructor; simpl. constructor; simpl; intros. 
- constructor; simpl; intros; firstorder.
- reflexivity.
- reflexivity.
- reflexivity.
Defined.

Axiom all_cont : forall {A}, (A -> LPReal) -> RF.t (O A).
Axiom all_cont_point : forall A (f : A -> LPReal) (a : A), 
  RF.eval (all_cont f) (point a) = f a.
Axiom RF_pointwise : forall A (f g : RF.t (O A)),
  (forall a, RF.eval f (point a) <= RF.eval g (point a)) -> RF.le f g.

Require Finite.

Definition inject {A B}
  (f : A -> B) : Val.Simple.t (O A) -> Val.Simple.t (O B)
  := Val.Simple.map_concrete (fun P b => exists a, b = f a /\ P a).

Definition fin_all_cont {A : Type} (fin : Finite.T A) (f : A -> LPReal)
  : Val.Simple.t (O A).
Proof.
induction fin.
- exact (Val.Simple.Ind (fun _ => False)).
- unfold O. 
  pose (Val.Simple.Scale (f (inl I)) (@Val.Simple.Ind _ _ (O _) 
    (fun x => x = @inl _ A I))) as v1.
  pose (inject (@inr True _) (IHfin (fun x => f (inr x)))) as v2.
  exact (Val.Simple.Add v1 v2).
- pose (IHfin (fun a => f (Iso.to t a))) as v.
  exact (Val.Simple.map (F.subset_map (Iso.from t)) v).
Defined.

Require Import Ring. 
Lemma inject_L : forall A B (a : A) v, Val.Simple.Integral
     (inject inr v)
     (Val.unit (point (@inl A B a))) = 0.
Proof. intros. unfold inject. induction v; simpl.
- rewrite LPRind_false. reflexivity. unfold not. intros contra.
  destruct contra. destruct H. congruence.
- rewrite IHv. ring.
- rewrite IHv1. rewrite IHv2. ring.
Qed.

Lemma inject_R : forall A B (b : B) v, Val.Simple.Integral
     (inject inr v)
     (Val.unit (point (@inr A B b))) = Val.Simple.Integral v
     (Val.unit (point b)).
Proof. intros. unfold inject. induction v; simpl.
- apply LPRind_iff. split; intros.
  destruct H. destruct H. inversion H. assumption.
  exists b. split. reflexivity. assumption.
- rewrite IHv. ring.
- rewrite IHv1. rewrite IHv2. ring.
Qed.

Lemma map_point {A B OA OB} (X : F.t A OA) (Y : F.t B OB) :
  forall (f : F.cmap OA OB) (x : F.point OA),
  Val.eq (Val.map f (Val.unit x))
         (Val.unit (F.cmap_compose x f)).
Proof. 
intros. unfold Val.eq. intros. reflexivity.
Qed.

Lemma simple_int_map_point : forall {A B OA OB} (X : F.t A OA) (Y : F.t B OB)
  (f : F.cmap OA OB) s (x : F.point OA),
   Val.Simple.Integral (Val.Simple.map f s) (Val.unit x)
  = Val.Simple.Integral s (Val.unit (F.cmap_compose x f)).
Proof.
intros. induction s; simpl in *. 
- reflexivity.
- rewrite <- IHs. reflexivity.
- rewrite <- IHs1. rewrite <- IHs2. reflexivity.
Qed.

Theorem fin_all_cont_point : forall {A : Type} 
  (fin : Finite.T A) (f : A -> LPReal) (a : A),
   RF.eval (RF.simple (fin_all_cont fin f)) (point a) = f a.
Proof.
intros. induction fin.
- contradiction. 
- destruct a.
  + destruct t. unfold RF.eval in *. rewrite RF.int_simple. simpl.
    rewrite LPRind_true by trivial.
    rewrite inject_L. ring.
  + unfold RF.eval in *. rewrite RF.int_simple.
    simpl. rewrite LPRind_false.
    specialize (IHfin (fun x => f (inr x)) a).
    rewrite RF.int_simple in IHfin. rewrite inject_R. 
    simpl in *. rewrite IHfin.
    ring. congruence.
-  unfold RF.eval. rewrite RF.int_simple. simpl.
   specialize (IHfin (fun a0 => f (Iso.to t a0)) (Iso.from t a)).
   simpl in IHfin. rewrite Iso.to_from in IHfin.
   unfold RF.eval in IHfin. rewrite RF.int_simple in IHfin.
   rewrite <- IHfin. simpl. rewrite simple_int_map_point.
   apply Val.Simple.int_proper. unfold Val.Simple.eq. reflexivity.
   apply (map_point (F.subset _) (F.subset _)).
Qed.   
 
Lemma RF_pointwise_eq : forall {A} (f g : RF.t (O A)),
  (forall a, RF.eval f (point a) = RF.eval g (point a)) -> RF.eq f g.
Proof. intros. apply PO.le_antisym; apply RF_pointwise; 
  intros; rewrite H; apply LPRle_refl.
Qed.

Lemma RF_add : forall {A} (f g : A -> LPReal),
  RF.eq (RF.add (all_cont f) (all_cont g)) (all_cont (fun x => f x + g x)).
Proof.
intros. apply RF_pointwise_eq. intros.
rewrite all_cont_point. unfold RF.eval. rewrite RF.int_adds.
apply LPRplus_eq_compat; apply all_cont_point.
Qed.

Lemma RF_add_eval : forall {A} (f g : A -> LPReal) (a : A),
    RF.eval (RF.add (all_cont f) (all_cont g)) (point a)
  = f a + g a.
Proof.
intros. unfold RF.eval. rewrite RF_add. apply all_cont_point.
Qed.

Definition integral {A} (f : A -> LPReal) (mu : Val A) : LPReal :=
  RF.integral (all_cont f) mu.

(* Theorem 3.13 of Jones 1990 *)
Theorem directed_monotone_convergence {A : Type} :
  forall (mu : Val.t (O A)) I `(JL : JoinLat.t I),
  forall (g : I -> (A -> LPReal)),
    integral (fun x => LPRsup (fun i => g i x)) mu
  = LPRsup (fun i => integral (fun x => g i x) mu).
Proof.
intros. 
Admitted.

(** The "bind" of our monad. Given a measure over the space A, and a
    function which, given a point in A, returns a measure on B,
    we can produce a measure on B by integrating over A. *)
Definition bind {A B : Type}
  (v : Val A) (f : A -> Val B)
  : Val B.
Proof. refine (
  {| Val.val := fun P => integral (fun x => Val.val (f x) P) v |}
).
- apply LPReq_compat. unfold LPReq. split.
  unfold integral. 
  rewrite <- (@RF.int_zero _ _ _ v).
  apply RF_pointwise. intros. rewrite all_cont_point. 
  rewrite Val.strict. apply LPRzero_min.
  apply LPRzero_min.
- intros. unfold integral. apply RF_pointwise. intros. 
  repeat rewrite all_cont_point. apply Val.monotonic. 
  assumption.
- intros. unfold integral. repeat rewrite <- RF.int_adds. apply RF_pointwise_eq.
  intros. unfold RF.eval. repeat rewrite RF_add. pose proof all_cont_point.
  unfold RF.eval in H. repeat rewrite H.
  apply Val.modular.
- unfold Val.ContinuousV. intros. simpl.
  unfold integral. erewrite RF.int_proper. Focus 3. unfold Val.eq. reflexivity.
  Focus 2. apply RF_pointwise_eq. intros. do 2 rewrite all_cont_point.
  eapply (Val.continuous (f a)). eassumption. apply fmono.
  pose proof @directed_monotone_convergence.
  unfold integral in H. eapply H. eassumption.
Defined.

End SubsetVal.
