Require Import 
  Prob.StdLib 
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC 
  FormTopC.Cont
  FormTopC.Bundled.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Existing Instances FormTop.GCov_formtop 
  Bundled.IGT_PreO Bundled.IGTFT Bundled.IGT_Pos.
Local Open Scope FT.


(** Product spaces for inductively generated formal topologies.
    See Section 4.3 of [1]. *)
Module Product.

Generalizable All Variables.
Section Product.

Set Printing Universes.
Set Printing All.
Universes AX PX IX AY PY IY A P I.
Variable X : IGT@{AX PX IX}.
Variable Y : IGT@{AY PY IY}.

Definition S' : Type@{A} := S X * S Y.

Definition le' := prod_op (le X) (le Y).

Definition Ix := PreISpace.Ix.
Definition C := PreISpace.C.

Inductive Ix' : S' -> Type@{I} := 
  | PLeft : forall {s}, Ix X s -> forall t, Ix' (s, t)
  | PRight : forall {t}, Ix Y t -> forall s, Ix' (s, t).

Definition C'@{} (p : S') (i : Ix' p) : Subset@{A P} S'
  := fun open => let (z, w) := open in (match i with
  | PLeft _ ixs t => prod@{PX Set} (C X _ ixs z) (w = t)
  | PRight _ ixt s => prod@{PY Set} (C Y _ ixt w) (z = s)
  end)%type.

Definition ProdPreO@{} : FormTop.PreOrder@{A P} :=
  {| PO_car := S'
   ; FormTop.le := le'
  |}.

Definition Prod : PreISpace.t :=
  {| PreISpace.S := ProdPreO
   ; PreISpace.Ix := Ix'
   ; PreISpace.C := C'
  |}.

Local Instance PO : PreO.t (le Prod) := PreO.product (PO X) (PO Y).

Local Instance loc : FormTop.localized Prod.
Proof.
unfold FormTop.localized.
intros a c H1 i. destruct H1 as (H1 & H2).
destruct a as [sa ta].
destruct i.
- pose (localized X sa s H1 i) as H.
  destruct H as (x & H).
  exists (PLeft x ta).
  intros s0 H3. destruct s0 as [su tu].
  simpl in H3. destruct H3 as (H3 & H4).
  specialize (H _ H3).
  destruct H as [u [CSu downu]].
  simpl. exists (u, t). split. split. assumption. reflexivity.
  subst. destruct downu.
  simpl in *.
  split; split; simpl; (assumption || reflexivity). 
- pose (localized Y ta t H2 i) as H0.
  destruct H0 as (x & H0).
  exists (PRight x sa).
  intros s0 H3. destruct s0 as [su tu].
  simpl in H3. destruct H3 as (H3 & H4).
  specialize (H0 _ H3).
  destruct H0 as [u [CTu downu]].
  simpl. exists (s, u). split. split. assumption. reflexivity.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. reflexivity. assumption.
  simpl.
  unfold le', prod_op; eauto.
Qed.

Lemma factors a b U V : a <|[X] U -> b <|[Y] V -> 
  (a, b) <|[Prod] (fun p => let (a', b') := p in U a' * V b')%type.
Proof.
intros H H0. induction H.
- induction H0.
  + apply FormTop.grefl. split; assumption.
  + eapply FormTop.gle_left. 2:apply IHGCov.
    split; simpl. apply PreO.le_refl. assumption.
  + apply (FormTop.ginfinity) with (PRight i a).
    intros. simpl in X0. destruct u0. destruct X1. 
    subst. apply X0. assumption.
- apply FormTop.gle_left with (b0, b). split; simpl.
  assumption. reflexivity.
  apply IHGCov.
- apply (FormTop.ginfinity) with (PLeft i b).
  intros. simpl in X1. destruct u. destruct X1. 
  subst. apply X0. assumption.
Qed.

(** Prove the space has a positivity predicate. *)
Definition PosProd : Subset Prod :=
  fun p => let (x, y) := p in (FormTop.gPos x * FormTop.gPos y)%type.

Local Open Scope Subset.

Lemma PosProd_factors (a : Prod) :
  eq a ∩ PosProd === fun p => let (x, y) := p in
    ((eq (fst a) ∩ FormTop.gPos) x * (eq (snd a) ∩ FormTop.gPos) y)%type.
Proof.
destruct a as [x y].
apply Same_set_iff.
intros. split; intros H.
- destruct H. subst. simpl. destruct p.
  split; split; (reflexivity || assumption).
- destruct x0. destruct H. destruct i, i0. subst.
  simpl in *. split. reflexivity. split; assumption.
Qed.

Lemma Pos : FormTop.gtPos Prod.
Proof.
unshelve econstructor.
- exact PosProd.
- intros. destruct a, b, X0. simpl in *.
  destruct X1. split; eapply pos; eassumption.
- intros. destruct i, X0. 
  + destruct (FormTop.gmono_ax (gtPos := pos X) s i g).
    exists (a, t). destruct i0. split. simpl. 
    split. assumption. reflexivity.
    split; assumption.
  + destruct (FormTop.gmono_ax (gtPos := pos Y) t i g0).
    exists (s, a). destruct i0. split. simpl. 
    split. assumption. reflexivity. split; assumption.
- intros.
  apply (FormTop.trans (A := Prod) (U := eq a ∩ PosProd)).
  + eapply FormTop.gsubset_equiv.
    apply PosProd_factors. destruct a.
    eapply factors; apply FormTop.gpositive; 
    intros; apply FormTop.grefl; split; trivial.
  + intros. destruct X1. subst. apply X0. assumption.
Qed.

Axiom undefined : forall A, A.

Definition times : IGT :=
  {| S := Prod
   ; Bundled.PO := PO
   ; localized := loc
   ; pos := undefined _ (*Pos*)
  |}.

(** The other space has to be nonempty *)
Lemma unfactors1 a b U : (a, b) <|[times] U
  -> (forall (t : S Y) (i : Ix Y t), Inhabited (C Y t i))
  -> a <|[X] (fun s => { b' : S Y & U (s, b') }).
Proof.
intros H H0. remember (a, b) as ab.
replace (a) with (fst ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. eexists; eassumption.
- destruct a, b, l. simpl in *.
  eapply FormTop.gle_left with p1. assumption.
  assumption.
- destruct a. destruct i.
  + apply FormTop.ginfinity with i.
    intros. apply (X0 (u, t)). simpl. simpl in X1.
    intuition.
  + simpl in *.
    specialize (H0 t i). destruct H0.
    apply (X0 (s, a)). split; trivial. 
Qed.

Lemma unfactors2 a b U : (a, b) <|[times] U
  -> (forall (s : S X) (i : Ix X s), Inhabited (C X s i))
  -> b <|[Y] (fun t' => { a' : S X & U (a', t') }).
Proof.
intros H H0. remember (a, b) as ab.
replace b with (snd ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. exists p; assumption.
- destruct a, b, l. simpl in *. 
  apply FormTop.gle_left with p2. assumption.
  assumption.
- destruct a. destruct i.
  + simpl in *.
    specialize (H0 s i). destruct H0.
    apply (X0 (a, t)). split; trivial.
  + apply FormTop.ginfinity with i.
    intros. apply (X0 (s, u)). simpl. simpl in X0.
    intuition.
Qed.

End Product.
End Product.

Infix "*" := Product.times : loc_scope.

Module ProductMaps.
  Generalizable All Variables.
Section Products.

Require Import FormTopC.Bundled.

Variable A : IGT.
Local Open Scope loc.

Definition diagonal : Cont.map A (A * A)
  := fun (out : S (A * A)) (p : S A) =>
  let (out1, out2) := out in ((p <=[A] out1) * (p <=[A] out2))%type.

Lemma t_diagonal : Cont.t A (A * A) diagonal.
Proof.
constructor; intros; unfold diagonal in *.
- apply FormTop.refl. exists (a, a). split.
  split; reflexivity. 
- destruct b. destruct X0. 
  split; etransitivity; eassumption.
- destruct b, c. destruct X, X0.
  apply FormTop.refl. exists (a, a).
  split. split; unfold prod_op; simpl; eauto.
  split; eauto. split; reflexivity.
- generalize dependent a. induction X0; intros.
  + apply FormTop.refl. exists a. assumption. assumption. 
  + apply IHX0. destruct a, b, l. simpl in *. 
    destruct X. 
    split. transitivity p; eassumption.
    transitivity p0; eassumption.
  + destruct i; simpl in *; destruct X0.
    * destruct (localized A a0 s l i).
      apply FormTop.ginfinity with x.
      intros.
      specialize (s0 _ X0).
      destruct s0. destruct p. 
      apply X with (x0, t). simpl. 
      auto. destruct d. 
      split. assumption. transitivity a0; eassumption.
    * destruct (localized A a0 t l0 i).
      apply FormTop.ginfinity with x.
      intros.
      specialize (s0 _ X0).
      destruct s0. destruct p. 
      apply X with (s, x0). simpl. auto.
      destruct d.
      split. transitivity a0; assumption. assumption.
Qed.
  
Variable B : IGT.

Definition proj_L : Cont.map (A * B) A :=
  fun (out : S A) (p : S (A * B)) => let (s1, t1) := p in s1 <=[A] out.

Lemma t_proj_L : Cont.t (A * B) A proj_L.
Proof.
constructor; intros; unfold proj_L in *.
- apply FormTop.refl. destruct a. exists p. unfold In.
  constructor. reflexivity.
- destruct c, a, X. simpl in l, l0. 
  etransitivity; eassumption.
- destruct a. apply FormTop.refl. 
  exists p. split; assumption. reflexivity. 
- destruct a. generalize dependent p. induction X0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (b, p0).
    split; simpl. etransitivity; eassumption. 
    reflexivity. apply IHX0. reflexivity.
  + destruct (localized A _ _ X0 i).
    apply FormTop.ginfinity with (Product.PLeft _ _ x p0). 
    intros. simpl in *. destruct u. destruct X1.
    subst.
    specialize (s _ c). destruct s as (u & Caiu & downu).
    eapply X. eassumption.
    destruct downu. assumption.
Qed.

Definition proj_R : Cont.map (A * B) B :=
  fun (out : S B) (p : S (A * B)) => let (s1, t1) := p in t1 <=[B] out.

Lemma t_proj_R : Cont.t (A * B) B proj_R.
Proof.
constructor; intros; unfold proj_R in *.
- apply FormTop.refl. destruct a. exists p0. unfold In.
  constructor. reflexivity.
- destruct c, a, X. simpl in l, l0. 
  etransitivity; eassumption.
- destruct a. apply FormTop.refl. 
  exists p0. split; eauto. reflexivity. 
- destruct a. generalize dependent p0. induction X0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply (FormTop.le_left) with (p, b).
    (** We would like
        eauto using (PreO.le_refl, PreO.le_trans)
        to work here, but it is dumb! *)
    split; simpl. reflexivity.
    etransitivity; eassumption.
    apply IHX0. reflexivity.
  + destruct (localized B _ _ X0 i).
    apply FormTop.ginfinity with (Product.PRight _ _ x p). 
    intros. simpl in *. destruct u. destruct X1.
    subst.
    specialize (s _ c). destruct s as (u & Caiu & downu).
    eapply X. eassumption.
    destruct downu. assumption.
Qed.

Variable X Y : IGT.

Definition parallelIG (F : Cont.map A X) (G : Cont.map B Y)
  : Cont.map (A * B) (X * Y) :=
  fun (out : S (X * Y)) (p : S (A * B)) =>
  let (s, t) := p in let (a, b) := out in
   (F a s * G b t)%type.

Local Open Scope Subset.
Lemma parallelIG_Proper_LE {F F' : Cont.map A X} {G G' : Cont.map B Y}
  : LE_map F F' -> LE_map G G'
  -> LE_map (parallelIG F G) (parallelIG F' G').
Proof.
unfold LE_map, Cont.func_LE. intros HF HG.
unfold RelIncl. intros.
destruct a as (x, y).
specialize (HF x). specialize (HG y).
unfold Cont.Sat, Included, pointwise_rel, CRelationClasses.arrow. 
intros.
unfold parallelIG in *. FormTop.trans X0.
unfold In in X0. destruct a. destruct X0.
apply Product.factors.
- apply HF. unfold Cont.Sat. apply FormTop.refl. assumption.
- apply HG. unfold Cont.Sat. apply FormTop.refl. assumption.
Qed.

Lemma parallelIG_Proper_EQ {F F' : Cont.map A X} {G G' : Cont.map B Y}
  : EQ_map F F' -> EQ_map G G'
  -> EQ_map (parallelIG F G) (parallelIG F' G').
Proof.
unfold EQ_map. intros HF HG. 
apply Cont.func_LE_antisym; apply parallelIG_Proper_LE;
apply Cont.func_EQ_LE; (assumption || (symmetry ; assumption)).
Qed.

(*
Existing Instances Product.PO Product.loc.

Local Instance product_cov :
  FormTop.t (prod_op leS leT) (@Product.Cov S T leS leT IS IT CS CT).
Proof.
apply FormTop.GCov_formtop.
Qed.
*)

Require Import CRelationClasses. 

Theorem t_parallelIG (F : Cont.map A X) (G : Cont.map B Y)
  : IGCont.t A X F
  -> IGCont.t B Y G
  -> IGCont.t (A * B) (X * Y) (parallelIG F G).
Proof.
intros ContF ContG. constructor; intros.
- eapply FormTop.gmonotone with
  (fun s : S (A * B)%loc => let (s', t') := s in
  union (fun _ => True) F s' * union (fun _ => True) G t')%type.
  unfold Included, pointwise_rel, arrow; intros x H.
  destruct a, x. 
  destruct H. destruct u, u0.
  constructor 1 with (a, a0). 
  constructor. econstructor; eassumption.
  destruct a.
  eapply (@FormTop.monotone (A * B) _).
  Focus 2.
  apply Product.factors; try eassumption.
  apply (IGCont.here ContF). apply (IGCont.here ContG).
  unfold Included, pointwise_rel, arrow; intros. 
  destruct a. assumption.
- destruct a, b, c.
  destruct X0, X1.
  pose proof (IGCont.local ContF _ _ _ f f0).
  pose proof (IGCont.local ContG _ _ _ g g0).
  eapply FormTop.monotone. Focus 2.
  eapply Product.factors; eassumption.
  unfold Included, pointwise_rel, arrow; intros x H.
  destruct x. destruct H. destruct u, u0.
  destruct i, i0.
  exists (a, a0). simpl.
   unfold FormTop.down, In. simpl; unfold Product.le', prod_op. auto.
  split; assumption.
- destruct c, b, a. destruct X0, X1; simpl in *.
  split. 
  eapply (IGCont.le_left ContF); eassumption.
  eapply (IGCont.le_left ContG); eassumption.
- destruct a, b, c. destruct X0, X1. simpl in *.
  split. eapply (IGCont.le_right ContF); eassumption.
  eapply (IGCont.le_right ContG); eassumption.
- destruct j as [a0 i b | b i a0]; simpl in *.
  + destruct a. destruct X0.
  pose proof (IGCont.ax_right ContF _ _ i f).
  assert ( (p, p0) <|[(A * B)%loc]
    (fun open => let (s', t') := open in (union (PreISpace.C X a0 i) F s') * (p0 = t')))%type.
  eapply Product.factors; try eassumption. apply FormTop.grefl. reflexivity.
  eapply FormTop.gmonotone. 2: apply X1.
  unfold Included, pointwise_rel, arrow; intros.
  destruct a. destruct X2. subst.
  destruct u.  exists (a, b). unfold In. split. assumption.
  reflexivity. split; assumption.
  + (** Same thing on this side. Yay! *)
  destruct a. destruct X0.
  pose proof (IGCont.ax_right ContG _ _ i g).
  assert ((p, p0) <|[(A * B)%loc]
    (fun open => let (s', t') := open in (p = s') * (union (PreISpace.C Y b i) G t')))%type.
  eapply Product.factors; try eassumption. apply FormTop.grefl. reflexivity.
  eapply FormTop.gmonotone. 2: apply X1.
  unfold Included, pointwise_rel, arrow; intros.
  destruct a. destruct X2. subst.
  destruct u. exists (a0, a). unfold In. split. assumption. reflexivity.
  split; assumption.
Qed.

Definition parallel (F : Cont.map A X) (G : Cont.map B Y)
  : Cont.map (A * B) (X * Y) :=
  parallelIG (Cont.Sat (S := A) F) (Cont.Sat (S := B) G).

Theorem t_parallel (F : Cont.map A X) (G : Cont.map B Y)
  : Cont.t A X F
  -> Cont.t B Y G
  -> Cont.t (A * B) (X * Y) (parallel F G).
Proof.
intros ContF ContG.
unfold parallel. apply IGCont.cont.
apply t_parallelIG; apply IGCont.converse;
  try (typeclasses eauto); eassumption.
Qed.

End Products.
End ProductMaps.

Require Import
  Spec.Category
  FormTopC.Bundled
  FormTopC.Cont.
Import Category.

Local Open Scope obj.
Local Open Scope loc.

Existing Instances Bundled.PO Bundled.local.

Definition proj1 {A B : IGT} : A * B ~~> A :=
  {| mp := ProductMaps.proj_L A B
  ; mp_ok := ProductMaps.t_proj_L A B
  |}.

Definition proj2 {A B : IGT} : A * B ~~> B :=
  {| mp := ProductMaps.proj_R A B
  ; mp_ok := ProductMaps.t_proj_R A B
  |}.

Definition diagonal {A : IGT} : A ~~> A * A :=
  {| mp := ProductMaps.diagonal A
  ; mp_ok := ProductMaps.t_diagonal A
  |}.

Definition parallel {A B X Y : IGT} (f : A ~~> X) (g : B ~~> Y)
  : A * B ~~> X * Y :=
  {| mp := ProductMaps.parallel A B X Y (mp f) (mp g)
   ; mp_ok := ProductMaps.t_parallel A B X Y (mp f) (mp g) (mp_ok f) (mp_ok g)
  |}.

Definition pair {Γ A B : IGT} (f : Γ ~~> A) (g : Γ ~~> B)
  : Γ ~~> A * B
  := parallel f g ∘ diagonal.

Definition times := Product.times.