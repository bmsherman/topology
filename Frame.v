Require Import SetoidClass.

Module PO.
  Record t {A : Type} : Type :=
  { eq : A -> A -> Prop
  ; le : A -> A -> Prop
  ; le_proper : Proper (eq ==> eq ==> iff) le
  ; le_refl : forall x, le x x
  ; le_antisym : forall x y, le x y -> le y x -> eq x y
  ; le_trans : forall x y z, le x y -> le y z -> le x z
  }.

  Arguments t : clear implicits.

  Record morph {A B : Type} (tA : t A) (tB : t B) (f : A -> B) : Prop :=
   { f_le : forall a b, le tA a b -> le tB (f a) (f b)
   ; f_eq : forall a b, eq tA a b -> eq tB (f a) (f b)
   }.

  Section Facts.

  Context {A : Type}.
  Variable PO : t A.
  Let le := le PO.
  Let eq := PO.eq PO.

  Infix "<=" := le.

  Definition eq_refl : Reflexive eq. 
  Proof. unfold Reflexive. 
    intros. apply le_antisym; apply le_refl.
  Qed.

  Definition eq_sym : Symmetric eq.
  Proof. 
  unfold Symmetric. intros. apply le_antisym. eapply le_proper.
  apply eq_refl. apply H. apply le_refl. eapply le_proper.
  apply H. apply eq_refl. apply le_refl.
  Qed.

  Definition eq_trans : Transitive eq.
  Proof.
    unfold Transitive.
    intros. apply le_antisym. eapply le_proper. apply H. 
    apply eq_refl. eapply le_proper. apply H0. apply eq_refl.
    apply le_refl. eapply le_proper. apply eq_refl. apply H.
    eapply le_proper. apply eq_refl. apply H0. apply le_refl.
  Qed.

  Definition top (t : A) : Prop := forall a, a <= t.
  Definition bottom (b : A) : Prop := forall a, b <= a.

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
  ; inf_greatest : forall m', (forall i, m' <= f i) -> m' <= m
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

  Instance t_equiv : forall {A} (tA : t A), Equivalence (eq tA).
  Proof. 
    split; [apply eq_refl | apply eq_sym | apply eq_trans ].
  Qed.

  Instance le_properI : forall {A} (tA : t A), Proper (eq tA ==> eq tA ==> iff) (le tA).
  Proof. intros. apply le_proper. Qed.

  Instance morph_properI : forall {A B} (tA : t A) (tB : t B) (f : A -> B)
    , morph tA tB f -> Proper (eq tA ==> eq tB) f.
  Proof. intros. destruct H. unfold Proper, respectful. apply f_eq0. Qed.

  Definition product {A B : Type} (tA : t A) (tB : t B) : t (A * B).
  Proof. refine (
   {| le := fun (x y : A * B) => le tA (fst x) (fst y) /\ le tB (snd x) (snd y)
   ; eq := fun (x y : A * B) => eq tA (fst x) (fst y) /\ eq tB (snd x) (snd y)
   |}); intros.
   - split; simpl in *; intros; intuition;
     (eapply le_proper; 
      [ ((apply eq_sym; eassumption) || eassumption) 
      | ((apply eq_sym; eassumption) || eassumption) 
      | eassumption ]).
   - destruct x. split; apply le_refl.
   - destruct x, y. split; apply le_antisym; intuition.
   - destruct x, y, z. split; eapply le_trans; intuition; eassumption.
  Defined.

  Definition pointwise {A B : Type} (tB : t B) : t (A -> B).
  Proof. refine (
    {| le := fun (f g : A -> B) => forall a, le tB (f a) (g a)
     ; eq := fun (f g : A -> B) => forall a, eq tB (f a) (g a)
    |}); intros; eauto using le_refl, le_antisym, le_trans.
  split; simpl in *; intros. rewrite <- H0. rewrite <- H. apply H1.
  rewrite H0. rewrite H. apply H1.
  Defined.

  Definition prop : t Prop.
  Proof. refine (
    {| le := fun (P Q : Prop) => P -> Q
     ; eq := fun (P Q : Prop) => P <-> Q
    |}); intuition.
  split; simpl in *; intros; intuition.
  Defined.

  Definition subset (A : Type) : t (A -> Prop) := pointwise prop.
 
End PO.

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

  Instance max_properI : forall {A} (tA : t A), Proper (eq tA ==> eq tA ==> eq tA) (max tA).
  Proof. intros. apply max_proper. Qed.

  Instance min_properI : forall {A} (tA : t A), Proper (eq tA ==> eq tA ==> eq tA) (min tA).
  Proof. intros. apply min_proper. Qed.


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
  - eapply PO.eq_trans. Focus 2. apply f_max1.
    apply (PO.f_eq _ _ _ f_PO1).
    rewrite f_max0. reflexivity.
  - eapply PO.eq_trans. 2: apply f_min1.
    apply (PO.f_eq _ _ _ f_PO1).
    rewrite f_min0. reflexivity.
  Qed.

  Definition prop : t Prop.
  Proof. refine (
    {| PO := PO.prop
     ; max P Q := P \/ Q
     ; min P Q := P /\ Q
    |}); simpl; intros; constructor; simpl; firstorder.
  Defined.

  Definition pointwise {A B} (tB : t B) : t (A -> B).
  Proof. refine (
    {| PO := PO.pointwise tB
    ; max f g a := max tB (f a) (g a)
    ; min f g a := min tB (f a) (g a)
    |}); simpl; intros.
    - unfold respectful. unfold Proper. intros.
      apply max_proper. apply H. apply H0.
    - constructor; simpl; intros; apply max_ok.
      apply H. apply H0.
    - unfold respectful, Proper. intros.
      apply min_proper. apply H. apply H0.
    - constructor; simpl; intros; apply min_ok.
      apply H. apply H0.
  Defined.

  Definition subset (A : Type) : t (A -> Prop) := pointwise prop.

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

  Definition le {A} (l : t A) : A -> A -> Prop := L.le (L l).
  Definition eq {A} (l : t A) : A -> A -> Prop := L.eq (L l).
  Definition min {A} (l : t A) : A -> A -> A := L.min (L l).
  Definition max {A} (l : t A) : A -> A -> A := L.max (L l).

  Definition top {A} (tA : t A) : A :=
    sup tA (fun a => a).

  Definition top_ok {A} (tA : t A) : PO.top (L.PO (L tA)) (top tA).
  Proof. 
    unfold PO.top. simpl. pose proof (sup_ok tA (fun a => a)).
    destruct H. apply sup_ge.
  Qed.

  Definition bottom {A} (tA : t A) : A :=
    sup tA (fun contra : False => False_rect _ contra).

  Definition bottom_ok {A} (tA : t A) : PO.bottom (L.PO (L tA)) (bottom tA).
  Proof.
    unfold PO.bottom. intros. 
    apply (PO.sup_least _ (fun contra : False => False_rect _ contra)).
    apply sup_ok. intros; contradiction.
  Qed.
  
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

Module F := Frame.

Module Valuation.

  Require Import LPReal.
  Local Open Scope LPR.

  Record t {A} {X : Frame.t A} :=
  { val :> A -> LPReal
  ; strict : val (F.bottom X) = 0
  ; monotonic : forall (U V : A), F.le X U V -> val U <= val V
  ; modular : forall (U V : A),
      val U + val V = val (F.max X U V) + val (F.min X U V)
  }.

  Arguments t {A} X.

  Lemma val_iff {A} {X : Frame.t A} : forall (mu : t X) (U V : A),
    F.eq X U V -> mu U = mu V.
  Proof. 
   intros. apply LPRle_antisym; apply monotonic; 
   rewrite H; apply PO.le_refl.
  Qed.

End Valuation.