Module PO.
  Record t {A : Type} : Type :=
  { le : A -> A -> Prop
  ; eq : A -> A -> Prop
  ; le_refl : forall x, le x x
  ; le_antisym : forall x y, le x y -> le y x -> eq x y
  ; le_trans : forall x y z, le x y -> le y z -> le x z
  }.

  Arguments t : clear implicits.

  Definition eq_refl {A} (tA : t A) : forall a, eq tA a a.
  Proof. 
    intros. apply le_antisym; apply le_refl.
  Qed.

  Record morph {A B : Type} (tA : t A) (tB : t B) (f : A -> B) : Prop :=
   { f_le : forall a b, le tA a b -> le tB (f a) (f b)
   ; f_eq : forall a b, eq tA a b -> eq tB (f a) (f b)
   }.

  Section Facts.

  Context {A : Type}.
  Variable PO : t A.
  Let le := le PO.

  Infix "<=" := le.

  Record max (l r m : A) : Prop :=
  { max_l     : l <= m
  ; max_r     : r <= m
  ; max_least : forall m', l <= m' -> r <= m' -> m <= m'
  }.

  Record min (l r m : A) : Prop :=
  { min_l        : m <= l
  ; min_r        : m <= r
  ; min_greatest : forall m', m' <= l -> m' <= r -> m' <= m
  }.

  Record sup {I : Type} (f : I -> A) (m : A) : Prop :=
  { sup_ge : forall i, f i <= m
  ; sup_least : forall m', (forall i, f i <= m') -> m <= m'
  }.

  Record inf {I : Type} (f : I -> A) (m : A) : Prop :=
  { inf_le : forall i, m <= f i
  ; sup_greatest : forall m', (forall i, m' <= f i) -> m' <= m
  }.

  Lemma morph_id (tA : t A) : morph tA tA (fun x => x).
  Proof. 
    constructor; auto.
  Qed.

  Lemma morph_compose {B C : Type} {tA : t A} {tB : t B} {tC : t C}
    : forall f g, morph tA tB f -> morph tB tC g -> morph tA tC (fun x => g (f x)).
  Proof.
    intros. destruct H, H0. constructor; intros; auto.
  Qed.

  End Facts.

  Definition subset (A : Type) : t (A -> Prop).
  Proof. refine (
    {| le := fun (P Q : A -> Prop) => forall (a : A), P a -> Q a
    ; eq := fun (P Q : A -> Prop) => forall (a : A), P a <-> Q a
    |}
  ); intros; intuition.
  Defined.

  Definition product {A B : Type} (tA : t A) (tB : t B) : t (A * B).
  Proof. refine (
   {| le := fun (x y : A * B) => le tA (fst x) (fst y) /\ le tB (snd x) (snd y)
   ; eq := fun (x y : A * B) => eq tA (fst x) (fst y) /\ eq tB (snd x) (snd y)
   |}); intros.
   - destruct x. split; apply le_refl.
   - destruct x, y. split; apply le_antisym; intuition.
   - destruct x, y, z. split; eapply le_trans; intuition; eassumption.
  Defined.
 
End PO.

Require Import SetoidClass.

Module Lattice.
  Record t {A : Type} : Type :=
  { PO :> PO.t A
  ; max : A -> A -> A
  ; max_proper : Proper (PO.eq PO ==> PO.eq PO ==> PO.eq PO) max
  ; max_ok : forall l r, PO.max PO l r (max l r)
  ; min : A -> A -> A
  ; min_proper : Proper (PO.eq PO ==> PO.eq PO ==> PO.eq PO) min
  ; min_ok : forall l r, PO.min PO l r (min l r)
  }.

  Arguments t : clear implicits.

  Definition le {A} (l : t A) : A -> A -> Prop := PO.le (PO l).
  Definition eq {A} (l : t A) : A -> A -> Prop := PO.eq (PO l).
  Definition sup {A} (l : t A) {I : Type} : (I -> A) -> A -> Prop
    := PO.sup (PO l).

  Record morph {A B : Type} (tA : t A) (tB : t B) (f : A -> B) : Prop :=
   { f_PO : PO.morph (PO tA) (PO tB) f
   ; f_max : forall a b, eq tB (f (max tA a b)) (max tB (f a) (f b))
   ; f_min : forall a b, eq tB (f (min tA a b)) (min tB (f a) (f b))
   }.

  Lemma morph_id {A} (tA : t A) : morph tA tA (fun x => x).
  Proof.
  constructor; intros.
  - apply PO.morph_id.
  - apply PO.eq_refl.
  - apply PO.eq_refl.
  Qed.

  Lemma morph_compose {A B C} (tA : t A) (tB : t B) (tC : t C)
    : forall f g, morph tA tB f -> morph tB tC g -> morph tA tC (fun x => g (f x)).
  Proof.
  intros. destruct H, H0. constructor; intros.
  - eapply PO.morph_compose; eassumption.
  - 
  Admitted.

  Definition subset (A : Type) : t (A -> Prop).
  Proof. refine (
    {| PO := PO.subset A
    ; max P Q a := P a \/ Q a
    ; min P Q a := P a /\ Q a
    |}); simpl; intros; constructor; simpl; firstorder.
  Defined.

  Definition product {A B : Type} (tA : t A) (tB : t B) : t (A * B).
  Proof. refine (
   {| PO := PO.product tA tB
   ; max := fun (x y : A * B) => (max tA (fst x) (fst y), max tB (snd x) (snd y))
   ; min := fun (x y : A * B) => (min tA (fst x) (fst y), min tB (snd x) (snd y))
   |}); simpl; intros; constructor; simpl; intros;
    repeat match goal with
    | [ p : (A * B)%type |- _ ] => destruct p
    | [ p : _ /\ _ |- _ ] => destruct p
    | [  |- _ /\ _ ] => split
    | [ |- _ ] => eapply PO.max_l; apply max_ok
    | [ |- _ ] => eapply PO.max_r; apply max_ok
    | [ |- _ ] => eapply PO.min_l; apply min_ok
    | [ |- _ ] => eapply PO.min_r; apply min_ok
    | [ |- _ ] => apply max_proper; assumption
    | [ |- _ ] => apply min_proper; assumption
    end.
   eapply PO.max_least. apply max_ok. assumption. assumption.
   eapply PO.max_least. apply max_ok. assumption. assumption.
   eapply PO.min_greatest. apply min_ok. assumption. assumption.
   eapply PO.min_greatest. apply min_ok. assumption. assumption.
   Defined. 
   
End Lattice.

Module L := Lattice.

Module Frame.
  Record t {A : Type} : Type :=
  { L :> L.t A
  ; sup : forall {I : Type}, (I -> A) -> A
  ; sup_proper : forall {I : Type},
     Proper (pointwise_relation _ (L.eq L) ==> L.eq L) (@sup I)
  ; sup_ok :  forall {I : Type} (f : I -> A), L.sup L f (sup f)
  ; sup_distr : forall x {I : Type} (f : I -> A)
    , L.eq L (L.min L x (sup f)) (sup (fun i => L.min L x (f i)))
  }.

  Arguments t : clear implicits.

  Definition subset (A : Type) : t (A -> Prop).
  Proof. refine (
    {| L := L.subset A
    ; sup I f a := exists (i : I), f i a
    |}); simpl; intros.
  - constructor; unfold pointwise_relation, L.eq in H; simpl in H;
     intros [??]; eexists; apply H; eassumption.
  - constructor; simpl; intros.
    + exists i. assumption.
    + destruct H0. apply (H x a). assumption.
  - split; intros. 
    + destruct H as (xa & i & fia). exists i. intuition.
    + destruct H as (i & xa & fia). split. assumption.
      exists i. assumption.
  Defined.
  
End Frame.