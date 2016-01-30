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

  Record morph {A B : Type} {tA : t A} {tB : t B} {f : A -> B} : Prop :=
   { f_le : forall a b, le tA a b -> le tB (f a) (f b)
   ; f_eq : forall a b, eq tA a b -> eq tB (f a) (f b)
   }.

  Arguments morph {A} {B} tA tB f.

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

  Definition one : t True.
  Proof. refine (
    {| le := fun _ _ => True
     ; eq := fun _ _ => True
    |}); intros; auto.
  unfold Proper, respectful. intuition.
  Defined.

  Definition two : t bool.
  Proof. refine (
    {| le := Bool.leb
    ;  eq := Logic.eq
    |}); intros; auto. destruct x; simpl; trivial.
    destruct x, y; auto. destruct x, y, z; auto. simpl in *. congruence.
  Defined.

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

  Definition map {A B : Type} (f : A -> B) (tB : t B) : t A.
  Proof. refine (
    {| le x y := le tB (f x) (f y)
    ;  eq x y := eq tB (f x) (f y)
    |}); intros.
  - split; simpl in *; intros. 
    + rewrite <- H. rewrite <- H0. apply H1.
    + rewrite H.  rewrite H0. apply H1.
  - apply le_refl.
  - apply le_antisym; eauto.
  - eapply le_trans; eauto.
  Defined.

  Definition pointwise {A} {B : A -> Type} (tB : forall a, t (B a)) : t (forall a, B a).
  Proof. refine (
    {| le := fun (f g : forall a : A, B a) => forall a, le (tB a) (f a) (g a)
     ; eq := fun (f g : forall a : A, B a) => forall a, eq (tB a) (f a) (g a)
    |}); intros; eauto using le_refl, le_antisym, le_trans.
  split; simpl in *; intros. rewrite <- H0. rewrite <- H. apply H1.
  rewrite H0. rewrite H. apply H1.
  Defined.

  Definition morph_pointwise {A B C} {tC : t C} (f : B -> A)
    : morph (pointwise (fun _ : A => tC)) (pointwise (fun _ : B => tC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply H.
  - apply H.
  Qed. 

  Definition prop : t Prop.
  Proof. refine (
    {| le := fun (P Q : Prop) => P -> Q
     ; eq := fun (P Q : Prop) => P <-> Q
    |}); intuition.
  split; simpl in *; intros; intuition.
  Defined.

  Definition subset (A : Type) : t (A -> Prop) := pointwise (fun _ => prop).
 
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


  Record morph {A B : Type} {tA : t A} {tB : t B} {f : A -> B} : Prop :=
   { f_PO : PO.morph (PO tA) (PO tB) f
   ; f_max : forall a b, eq tB (f (max tA a b)) (max tB (f a) (f b))
   ; f_min : forall a b, eq tB (f (min tA a b)) (min tB (f a) (f b))
   }.

  Arguments morph {A} {B} tA tB f.

  Lemma f_eq {A B} {tA : t A} {tB : t B} {f : A -> B} : 
  morph tA tB f -> Proper (eq tA ==> eq tB) f.
  Proof. 
    unfold Proper, respectful. intros. apply (PO.f_eq (f_PO H)).
    assumption.
  Qed.

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
  intros. constructor; intros.
  - eapply PO.morph_compose; eapply f_PO; eassumption.
  - rewrite <- (f_max H0). rewrite (f_eq H0). reflexivity.
    apply (f_max H).
  - rewrite <- (f_min H0). rewrite (f_eq H0). reflexivity.
    apply (f_min H).
  Qed.

  Definition one : t True.
  Proof. refine (
    {| PO := PO.one
     ; max := fun _ _ => I
     ; min := fun _ _ => I
    |}); intros; auto; unfold Proper, respectful; auto.
  - destruct l, r. constructor. apply PO.le_refl. apply PO.le_refl.
    intros. destruct m'. apply PO.le_refl.
  - destruct l, r. constructor. apply PO.le_refl. apply PO.le_refl.
    intros. destruct m'. apply PO.le_refl.
  Defined.

  Definition two : t bool.
  Proof. refine (
    {| PO := PO.two
    ; max := orb
    ; min := andb
    |}); intros; constructor;
  repeat match goal with
  | [ b : bool |- _ ] => destruct b
  end; simpl; auto.
  Defined. 

  Definition prop : t Prop.
  Proof. refine (
    {| PO := PO.prop
     ; max P Q := P \/ Q
     ; min P Q := P /\ Q
    |}); simpl; intros; constructor; simpl; firstorder.
  Defined.

  Definition pointwise {A} {B : A -> Type} (tB : forall a, t (B a)) : t (forall a, B a).
  Proof. refine (
    {| PO := PO.pointwise tB
    ; max f g a := max (tB a) (f a) (g a)
    ; min f g a := min (tB a) (f a) (g a)
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

  Definition morph_pointwise {A B C} {tC : t C} (f : B -> A)
    : morph (pointwise (fun _ : A => tC)) (pointwise (fun _ : B => tC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply PO.morph_pointwise.
  - apply PO.eq_refl. 
  - apply PO.eq_refl.
  Qed. 

  Definition subset (A : Type) : t (A -> Prop) := pointwise (fun _ => prop).

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
  ; sup : forall {Ix : Type}, (Ix -> A) -> A
  ; sup_proper : forall {Ix : Type},
     Proper (pointwise_relation _ (L.eq L) ==> L.eq L) (@sup Ix)
  ; sup_ok :  forall {Ix : Type} (f : Ix -> A), L.sup L f (sup f)
  ; sup_distr : forall x {Ix : Type} (f : Ix -> A)
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

  Record morph {A B : Type} {tA : t A} {tB : t B} {f : A -> B} : Prop :=
  { f_L : L.morph (L tA) (L tB) f
  ; f_sup : forall {Ix : Type} (g : Ix -> A), eq tB (f (sup tA g)) (sup tB (fun i => f (g i)))
  }.

  Arguments morph {A} {B} tA tB f.

  Lemma f_eq {A B} {tA : t A} {tB : t B} {f : A -> B} :
    morph tA tB f -> Proper (eq tA ==> eq tB) f.
  Proof. 
    intros. apply (L.f_eq (f_L H)).
  Qed.

  Lemma f_bottom {A B} {tA : t A} {tB : t B} {f : A -> B} :
    morph tA tB f -> eq tB (f (bottom tA)) (bottom tB).
  Proof.
  intros. unfold bottom. rewrite (f_sup H). apply sup_proper.
  unfold pointwise_relation. intros. contradiction.
  Qed.

  Lemma morph_id {A} : forall (tA : t A), morph tA tA (fun x => x).
  Proof. 
   intros. constructor. apply L.morph_id. reflexivity.
  Qed.

  Lemma morph_compose {A B C} : forall (tA : t A) (tB : t B) (tC : t C)
     (f : A -> B) (g : B -> C), morph tA tB f -> morph tB tC g 
     -> morph tA tC (fun x => g (f x)).
  Proof. intros. constructor.
  - eapply L.morph_compose; eapply f_L; eassumption.
  - intros. rewrite <- (f_sup H0). rewrite (f_eq H0).
    reflexivity. rewrite (f_sup H). reflexivity.
  Qed.

  Definition one : t True.
  Proof. refine (
    {| L := L.one
     ; sup := fun _ _ => I
    |}); intros; auto.
  - unfold Proper, respectful. intros. reflexivity.
  - constructor. intros. destruct (f i). apply PO.le_refl.
    intros.  destruct m'. apply PO.le_refl.
  Defined.

  Definition prop : t Prop.
  Proof. refine (
    {| L := L.prop
     ; sup := fun _ f => exists i, f i
    |}); simpl; intros.
  - constructor; unfold pointwise_relation, L.eq in H; simpl in H;
     intros [??]; eexists; apply H; eassumption.
  - constructor; simpl; intros.
    + exists i. assumption.
    + destruct H0. apply (H x). assumption.
  - split; intros. 
    + destruct H as (xa & i & fia). exists i. intuition.
    + destruct H as (i & xa & fia). split. assumption.
      exists i. assumption.
  Defined.

  Definition pointwise {A} {B : A -> Type} : (forall a, t (B a))
    -> t (forall a, B a).
  Proof. intros. refine (
   {| L := L.pointwise X
   ; sup := fun _ f => fun x => sup (X x) (fun i => f i x)
   |}); intros.
  - unfold Proper, respectful, pointwise_relation.
    intros. unfold L.eq. simpl. intros. 
    apply (sup_proper (X a)). unfold pointwise_relation.
    intros a'. apply H.
  - constructor; intros; simpl. intros.
    pose proof (@sup_ok _ (X a) Ix (fun i => f i a)).
    unfold L.sup in H.
    pose proof (PO.sup_ge (L.PO (X a)) _ _ H).
    apply H0.
    intros. pose proof (@sup_ok _ (X a) Ix (fun i => f i a)).
    unfold L.sup in H0. pose proof (PO.sup_least (L.PO (X a)) _ _ H0).
    apply H1. intros. apply H.
  - simpl. unfold L.eq. simpl. intros. 
    apply (sup_distr (X a)).
  Defined.

  Definition morph_pointwise {A B C} {tC : t C} (f : B -> A)
    : morph (pointwise (fun _ : A => tC)) (pointwise (fun _ : B => tC))
      (fun g b => g (f b)).
  Proof.
  constructor; intros; simpl in *; intros.
  - apply L.morph_pointwise.
  - apply PO.eq_refl. 
  Qed. 
  
  Definition subset (A : Type) : t (A -> Prop) := pointwise (fun _ => prop).

  (** continuous map on locales *)
  Record cmap {A B} {tA : t A} {tB : t B} := 
  { finv :> B -> A
  ; cont : morph tB tA finv
  }.

  Arguments cmap {A} {B} tA tB.

  Definition point {A} (tA : t A) := cmap prop tA.

  Definition subset_map {A B} (f : A -> B) : cmap (subset A) (subset B).
  Proof.
  refine ( {| finv P x := P (f x) |}).
  apply morph_pointwise.
  Defined.

  Definition cmap_compose {A B C} {tA : t A} {tB : t B} {tC : t C}
    (f : cmap tA tB) (g : cmap tB tC) : cmap tA tC.
  Proof. refine (
  {| finv x := finv f (finv g x) |}
  ). eapply morph_compose; eapply cont.
  Defined. 

End Frame.

Module F := Frame.

(** Join semi-lattices, or directed sets. Natural numbers are
    one of many examples. We will often generalize sequences, which
    are functions of type (nat -> A), to nets, which are functions of
    type (I -> A), where I is a directed set. *)
Module JoinLat.
  Record t : Type :=
  { ty : Type 
  ; le : ty -> ty -> Prop
  ; max : ty -> ty -> ty
  ; max_l : forall x y, le x (max x y)
  ; max_r : forall x y, le y (max x y)
  }.
End JoinLat.

Require Import LPReal.
Local Open Scope LPR.

Lemma LPRsup_sum_jlat : forall (I : JoinLat.t), let A := JoinLat.ty I in 
  forall (f g : A -> LPReal) ,
    (forall n m : A, JoinLat.le I n m -> f n <= f m) ->
    (forall n m : A, JoinLat.le I n m -> g n <= g m) ->
    LPRsup (fun x : A => f x + g x) = LPRsup f + LPRsup g.
Proof.
intros. eapply LPRsup_sum_lattice.
apply JoinLat.max_l.
apply JoinLat.max_r.
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
Definition ContinuousV {A} (X : F.t A) (mu : (A -> LPReal))
  := forall (I : JoinLat.t) (f : JoinLat.ty I -> A)
       (fmono : forall (m n : JoinLat.ty I), JoinLat.le I m n -> F.le X (f m) (f n))
       , mu (F.sup X f) = LPRsup (fun n => mu (f n)).

  Record t {A} {X : Frame.t A} :=
  { val :> A -> LPReal
  ; strict : val (F.bottom X) = 0
  ; monotonic : forall (U V : A), F.le X U V -> val U <= val V
  ; modular : forall (U V : A),
      val U + val V = val (F.max X U V) + val (F.min X U V)
  ; continuous : ContinuousV X val
  }.

  Arguments t {A} X.

  Generalizable Variables A.

  Lemma val_iff : forall `{X : F.t A} (mu : t X) (U V : A),
    F.eq X U V -> mu U = mu V.
  Proof. 
   intros. apply LPRle_antisym; apply monotonic; 
   rewrite H; apply PO.le_refl.
  Qed.

  Definition le `{X : F.t A} (mu nu : t X) := forall P, mu P <= nu P.

  Infix "<=" := le : Val_scope.
  Delimit Scope Val_scope with Val.

  Lemma le_refl `{X : F.t A} (mu : t X) : (mu <= mu)%Val.
  Proof. unfold le. intros. apply monotonic. apply PO.le_refl. Qed.

  Definition eq `{X : F.t A} (mu nu : t X) := forall P, mu P = nu P.
  Infix "==" := eq : Val_scope.

  Definition POLPR : PO.t LPReal.
  Proof. refine (
    {| PO.eq := Logic.eq
     ; PO.le := LPRle |}).
  - apply LPRle_refl.
  - intros. apply LPRle_antisym; assumption.
  - intros. eapply LPRle_trans; eassumption.
  Defined.

  Definition PO `{X : F.t A} : PO.t (t X) := PO.map val (PO.pointwise (fun _ : A => POLPR)).

  Lemma le_trans `{X : F.t A} (x y z : t X) : (x <= y -> y <= z -> x <= z)%Val.
  Proof. 
    pose proof (PO.le_trans (@PO _ X)). simpl in H. unfold le. apply H.
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

  Instance val_proper `{X : F.t A} : Proper (Logic.eq ==> F.eq X ==> Logic.eq) (@val _ X).
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
  rewrite (qredistribute (mu (F.max _ _ _))).
  apply LPRplus_eq_compat; apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite (LPRsup_sum_jlat I).
  apply LPRplus_eq_compat;
   apply continuous; assumption.
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
  with (c * (mu (F.max X U V) + mu (F.min X U V))) by ring.
  apply LPRmult_eq_compat. reflexivity.
  apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite continuous by assumption.
  apply LPRsup_scales.
Defined.

Infix "+" := add : Val_scope.
Infix "*" := scale : Val_scope.

Lemma zero_min `{X : F.t A} : forall (mu : t X), (0 <= mu)%Val.
Proof. intros. unfold le. intros. simpl. apply LPRzero_min. Qed.

Definition map {A B} {X : F.t A} {Y : F.t B} (f : F.cmap X Y)
  (mu : t X) : t Y.
Proof.
refine (
  {| val := fun x => mu (F.finv f x) |}
).
Proof. 
- pose proof (F.f_bottom (F.cont f)).
  rewrite H. apply strict.
- intros. apply monotonic. 
   apply (PO.f_le (L.f_PO (F.f_L (F.cont f)))).
   apply H.
- intros. unfold F.min, F.max. 
  rewrite (L.f_min (F.f_L (F.cont f))).
  rewrite (L.f_max (F.f_L (F.cont f))).
  apply modular.
- unfold ContinuousV. intros.
  rewrite (F.f_sup (F.cont f)).
  apply continuous. intros. 
  apply (L.f_PO (F.f_L (F.cont f))). apply fmono. assumption.
Defined.

Definition unit_prop : t F.prop.
Proof.
refine (
  {| val := fun P => LPRindicator P |}
); simpl; intros.
- apply LPRind_false. unfold not. intros. destruct H.
  contradiction.
- unfold F.le, L.le in H. simpl in H. apply LPRind_imp. assumption.
- unfold F.max, F.min. simpl. rewrite (SRadd_comm LPRsrt (LPRindicator (U \/ V))). 
  apply LPRind_modular.
- unfold ContinuousV. intros.
  apply LPRind_exists. 
Defined.

Definition unit {A} {X : F.t A} (x : F.point X)
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

Arguments t {A} X.

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


Definition PO `{X : F.t A} : PO.t (t X) 
  := PO.map Integral 
     (PO.pointwise (fun _ : Val.t X => Val.POLPR)).

Definition le `{X : F.t A} (x y : t X) := 
  forall (mu : Val.t X), Integral x mu <= Integral y mu.

Definition eq `{X : F.t A} (x y : t X) := 
  forall (mu : Val.t X), Integral x mu = Integral y mu.

Lemma int_proper1 `{X : F.t A} : Proper (Logic.eq ==> Val.eq ==> Logic.eq) (@Integral _ X).
Proof.
 unfold Proper, respectful. unfold eq. intros.  subst. induction y. 
 - simpl. apply H0. 
 - simpl. rewrite IHy. ring.
 - simpl. rewrite IHy1, IHy2. ring.
Qed.

Instance int_proper `{X : F.t A} : Proper (eq ==> Val.eq ==> Logic.eq) (@Integral _ X).
Proof.
 unfold Proper, respectful. unfold eq. intros. rewrite H.
 apply int_proper1. reflexivity. assumption.
Qed.

Lemma le_refl `{X : F.t A} : forall (x : t X), le x x.
Proof.
pose proof (PO.le_refl (@PO _ X)). unfold le.
simpl in *. apply H.
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
  , Integral (Ind (F.bottom X)) mu = 0.
Proof.
intros. simpl. apply strict.
Qed.

Fixpoint map_concrete {B} `{X : F.t A} {Y : F.t B}
  (f : A -> B) (s : t X) : t Y := match s with
  | Ind P => Ind (f P)
  | Scale c s' => Scale c (map_concrete f s')
  | Add l r => Add (map_concrete f l) (map_concrete f r)
  end.

Definition map {B} `{X : F.t A} {Y : F.t B}
  (f : F.cmap X Y) : t Y -> t X
  := map_concrete (F.finv f).

End Simple.

Module RealFunc.

  Record t {A} {X : F.t A} :=
    { func :> nat -> Simple.t X
    ; mono : forall m n, (m <= n)%nat -> Simple.le (func m) (func n) }.

  Arguments t {A} X.

  Definition simple `{X : F.t A} (f : Simple.t X) : t X.
  Proof. refine (
   {| func := fun _ => f |}).
  intros. apply Simple.le_refl.
  Defined.

  Definition add {A} {X : F.t A} (f g : t X) : t X.
  Proof. refine (
    {| func n := Simple.Add (f n) (g n) |}
  ).
  intros. unfold Simple.le. intros. 
  apply Simple.le_plus; apply mono; assumption.
  Defined.

  Infix "+" := add : RFunc_scope.
  Delimit Scope RFunc_scope with RFunc.

  Definition scale {A} {X : F.t A} (c : LPReal) (f : t X) : t X.
  Proof. refine (
    {| func n := Simple.Scale c (f n) |}
  ).
  intros. apply Simple.le_scale. apply LPRle_refl. apply mono. assumption.
  Defined.

  Infix "*" := scale : RFunc_scope.

  Definition map `{X : F.t A} {B} {Y : F.t B} (f : F.cmap X Y) 
    (g : t Y) : t X.
  Proof. refine (
    {| func := fun i => Simple.map f (g i) |}
  ). destruct g. simpl.
  Abort.

  Definition integral `{X : F.t A} (f : t X) (mu : Val.t X) :=
   LPRsup (fun i => Simple.Integral (f i) mu).

  Definition PO `{X : F.t A} : PO.t (t X) 
    := PO.map (fun f => (fun mu => integral f mu)) 
       (PO.pointwise (fun _ : Val.t X => Val.POLPR)).

  Definition le `{X : F.t A} (f g : t X) := forall (mu : Val.t X),
    integral f mu <= integral g mu.

  Definition eq `{X : F.t A} (f g : t X) := forall (mu : Val.t X),
    integral f mu = integral g mu.

  Infix "<=" := le : RFunc_scope.
  Infix "==" := eq : RFunc_scope.

  Instance int_proper `{X : F.t A} : Proper (eq ==> Val.eq ==> Logic.eq) (@integral _ X).
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
    , integral (simple (Simple.Ind (F.bottom X))) mu = 0.
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

Definition eval `{X : F.t A} (f : t X) (x : F.point X) : LPReal :=
  integral f (unit x).

End RealFunc.

End Val.

Module SubsetVal.

Module RF := Val.RealFunc.

Definition O := F.subset.

Definition Val (A : Type) := Val.t (O A).

Definition point {A} (a : A) : F.point (O A).
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
  pose (Val.Simple.Scale (f (inl I)) (@Val.Simple.Ind _ (O _) (fun x => x = @inl _ A I))) as v1.
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

Lemma map_point : forall A B (X : F.t A) (Y : F.t B) 
  (f : F.cmap X Y) (x : F.point X),
  Val.eq (Val.map f (Val.unit x))
         (Val.unit (F.cmap_compose x f)).
Proof. 
intros. unfold Val.eq. intros. reflexivity.
Qed.

Lemma simple_int_map_point : forall {A B} (X : F.t A) (Y : F.t B)
  (f : F.cmap X Y) s (x : F.point X),
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
    rewrite RF.int_simple in IHfin. rewrite inject_R. rewrite IHfin.
    ring. congruence.
-  unfold RF.eval. rewrite RF.int_simple. simpl.
   specialize (IHfin (fun a0 => f (Iso.to t a0)) (Iso.from t a)).
   simpl in IHfin. rewrite Iso.to_from in IHfin.
   unfold RF.eval in IHfin. rewrite RF.int_simple in IHfin.
   rewrite <- IHfin. simpl. rewrite simple_int_map_point.
   apply Val.Simple.int_proper. unfold Val.Simple.eq. reflexivity.
   apply map_point.
Qed.   
 
Lemma RF_pointwise_eq : forall {A} (f g : RF.t (O A)),
  (forall a, RF.eval f (point a) = RF.eval g (point a)) -> RF.eq f g.
Proof. intros. apply (PO.le_antisym RF.PO); apply RF_pointwise; 
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
  forall (mu : Val.t (O A)) (I : JoinLat.t),
  forall (g : JoinLat.ty I -> (A -> LPReal)),
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
  rewrite <- (@RF.int_zero _ _ v).
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
  apply (Val.continuous (f a)). apply fmono.
  pose proof @directed_monotone_convergence.
  unfold integral in H. apply H.
Defined.

End SubsetVal.