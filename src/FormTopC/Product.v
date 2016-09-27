Require Import 
  Prob.StdLib 
  FormTopC.FormTop
  Algebra.FrameC
  Algebra.SetsC 
  FormTopC.Cont.

Set Universe Polymorphism.
Set Asymmetric Patterns.

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
Variable CS : forall s, IS s -> Subset S.
Variable CT : forall t, IT t -> Subset T.

Inductive Ix : S * T -> Type := 
  | PLeft : forall {s}, IS s -> forall t, Ix (s, t)
  | PRight : forall {t}, IT t -> forall s, Ix (s, t).

Definition C (p : S * T) (i : Ix p) : Subset (S * T)
  := fun open => let (z, w) := open in (match i with
  | PLeft _ ixs t => CS _ ixs z * (w = t)
  | PRight _ ixt s => CT _ ixt w * (z = s)
  end)%type.

Definition PO := PreO.product POS POT.

Local Instance loc : 
    FormTop.localized leS CS
  -> FormTop.localized leT CT
  -> FormTop.localized (prod_op leS leT) C.
Proof.
intros H H0. unfold FormTop.localized in *.
intros a c H1 i. destruct H1 as (H1 & H2).
destruct a as [sa ta].
destruct i.
- specialize (H sa s H1 i).
  destruct H as (x & H).
  exists (PLeft x ta).
  intros s0 H3. destruct s0 as [su tu].
  simpl in H3. destruct H3 as (H3 & H4).
  specialize (H _ H3).
  destruct H as [u [CSu downu]].
  simpl. exists (u, t). split. split. assumption. reflexivity.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. assumption. reflexivity.
  simpl. split; assumption.
- specialize (H0 ta t H2 i).
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
  unfold prod_op; eauto.
Qed.

Definition Cov := FormTop.GCov (prod_op leS leT) C.

Hypothesis locS : FormTop.localized leS CS.
Hypothesis locT : FormTop.localized leT CT.

Local Instance isCov : FormTop.t (prod_op leS leT) Cov.
Proof.
apply (@FormTop.GCov_formtop (S * T) (prod_op leS leT)
  PO Ix C (loc locS locT)).
Qed.

Let CovS := FormTop.GCov leS CS.
Let CovT := FormTop.GCov leT CT.

Lemma factors a b U V : CovS a U -> CovT b V -> 
  Cov (a, b) (fun p => let (a', b') := p in U a' * V b')%type.
Proof.
intros H H0. induction H.
- induction H0.
  + apply FormTop.grefl. split; assumption.
  + eapply FormTop.gle_left. 2:apply IHGCov.
    split; simpl. apply PreO.le_refl. assumption.
  + apply (FormTop.ginfinity (C := C)) with (PRight i a).
    intros. simpl in X0. destruct u0. destruct X0. 
    subst. apply X. assumption.
- apply FormTop.gle_left with (b0, b). split; simpl.
  assumption. reflexivity.
  apply IHGCov.
- apply (FormTop.ginfinity (C := C)) with (PLeft i b).
  intros. simpl in X0. destruct u. destruct X0. 
  subst. apply X. assumption.
Qed.

(** The other space has to be nonempty *)
Lemma unfactors1 a b U : Cov (a, b) U
  -> (forall (t : T) (i : IT t), Inhabited (CT t i))
  -> CovS a (fun s => { b' : T & U (s, b') }).
Proof.
intros H H0. remember (a, b) as ab.
replace (a) with (fst ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. exists t. assumption.
- destruct a, b, l. simpl in *. 
  apply FormTop.gle_left with s0. assumption.
  assumption.
- destruct a. destruct i.
  + apply FormTop.ginfinity with i.
    intros. apply (X (u, t0)). simpl. simpl in X0.
    intuition.
  + simpl in *.
    specialize (H0 t0 i). destruct H0.
    apply (X (s0, a)). split. assumption. reflexivity.
Qed.

Lemma unfactors2 a b U : Cov (a, b) U
  -> (forall (s : S) (i : IS s), Inhabited (CS s i))
  -> CovT b (fun t' => { a' : S &  U (a', t') }).
Proof.
intros H H0. remember (a, b) as ab.
replace b with (snd ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. exists s. assumption.
- destruct a, b, l. simpl in *. 
  apply FormTop.gle_left with t0. assumption.
  assumption.
- destruct a. destruct i.
  + simpl in *.
    specialize (H0 s0 i). destruct H0.
    apply (X (a, t0)). split. assumption. reflexivity.
  + apply FormTop.ginfinity with i.
    intros. apply (X (s0, u)). simpl. simpl in X0.
    intuition.
Qed.

Section Overt.

Context {PosS : Subset S} {OvertS : FormTop.gtPos leS CS}.
Context {PosT : Subset T} {OvertT : FormTop.gtPos leT CT}.

Definition PosProd : Subset (S * T) :=
  fun p => let (x, y) := p in (FormTop.gPos x * FormTop.gPos y)%type.

Local Open Scope Subset.

Lemma PosProd_factors (a : S * T) :
  eq a ∩ PosProd === fun p => let (x, y) := p in
    ((eq (fst a) ∩ FormTop.gPos) x * (eq (snd a) ∩ FormTop.gPos) y)%type.
Proof.
destruct a.
apply Same_set_iff.
intros. split; intros.
- destruct X. subst. simpl. destruct p.
  split; split; (reflexivity || assumption).
- destruct x. destruct X. destruct i, i0. subst.
  simpl in *. split. reflexivity. split; assumption.
Qed.

Existing Instance FormTop.GCov_formtop.

Lemma Overt : FormTop.gtPos (prod_op leS leT) C.
Proof.
unshelve econstructor.
- exact PosProd.
- intros. destruct a, b, X. simpl in *.
  destruct X0. split. eapply OvertS; eassumption.
  eapply OvertT; eassumption.
- intros. destruct i, X. 
  + destruct (FormTop.gmono_ax (gtPos := OvertS) s i g).
    exists (a, t). destruct i0. split. simpl. 
    split. assumption. reflexivity.
    split; assumption.
  + destruct (FormTop.gmono_ax (gtPos := OvertT) t i g0).
    exists (s, a). destruct i0. split. simpl. 
    split. assumption. reflexivity. split; assumption.
- intros.
  apply (FormTop.trans (U := eq a ∩ PosProd)).
  + eapply FormTop.gsubset_equiv.
    apply PosProd_factors. destruct a.
    eapply factors; apply FormTop.gpositive; 
    intros; apply FormTop.grefl; split; (reflexivity || assumption).
  + intros. destruct X0. subst. apply X. assumption.
Qed.

End Overt.

End Product.
End Product.

Module ProductMaps.
  Generalizable All Variables.
Section Products. 
Context {S} `{POS : PreO.t S leS}.
Context {IS} {CS : forall (s : S), IS s -> Subset S}.
Variable locS : FormTop.localized leS CS.
Let CovS := FormTop.GCov leS CS.

Definition diagonal (out : S * S) (p : S) : Type :=
  let (out1, out2) := out in leS p out1 * leS p out2.

Lemma t_diagonal : Cont.t leS (prod_op leS leS)
  CovS (@Product.Cov _ _ leS leS IS IS CS CS) diagonal.
Proof.
pose proof (FormTop.GCov_formtop (C := CS)) as FTS.
constructor; intros; unfold diagonal, CovS in *.
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
    split. transitivity s; eassumption.
    transitivity s0; eassumption.
  + destruct i; simpl in *; destruct X0.
    * unfold FormTop.localized in locS. 
      specialize (locS a0 s l i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (s0 _ X0).
      destruct s0. destruct p. 
      apply X with (x0, t). simpl. 
      auto. destruct d. 
      split. assumption. transitivity a0; eassumption.
    * unfold FormTop.localized in locS. 
      specialize (locS a0 t l0 i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (s0 _ X0).
      destruct s0. destruct p. 
      apply X with (s, x0). simpl. auto.
      destruct d.
      split. transitivity a0; assumption. assumption.
Qed.
  

Context {T} `{POT : PreO.t T leT}.
Context {IT} {CT : forall (t : T), IT t -> Subset T}.
Variable locT : FormTop.localized leT CT.
Let CovT := FormTop.GCov leT CT.

Definition proj_L (out : S) (p : S * T) : Type :=
  let (s1, t1) := p in leS s1 out.

Lemma t_proj_L : Cont.t (prod_op leS leT) leS 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovS proj_L.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_L in *.
- apply FormTop.refl. destruct a. exists s. unfold In.
  constructor. reflexivity.
- destruct c, a, X. simpl in l, l0. 
  etransitivity; eassumption.
- destruct a. apply FormTop.refl. 
  exists s. split; assumption. reflexivity. 
- destruct a. generalize dependent s. induction X0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (b, t).
    split; simpl. etransitivity; eassumption. 
    reflexivity. apply IHX0. reflexivity.
  + unfold FormTop.localized in locS. 
    specialize (locS _ _ X0 i).
    destruct locS.
    apply FormTop.ginfinity with (Product.PLeft _ _ _ _ x t). 
    intros. simpl in *. destruct u. destruct X1.
    subst.
    specialize (s0 _ c). destruct s0 as (u & Caiu & downu).
    eapply X. eassumption.
    destruct downu. assumption.
Qed.

Definition proj_R (out : T) (p : S * T) : Type :=
  let (s1, t1) := p in leT t1 out.

Lemma t_proj_R : Cont.t (prod_op leS leT) leT 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovT proj_R.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_R in *.
- apply FormTop.refl. destruct a. exists t. unfold In.
  constructor. reflexivity.
- destruct c, a, X. simpl in l, l0. 
  etransitivity; eassumption.
- destruct a. apply FormTop.refl. 
  exists t. split; eauto. reflexivity. 
- destruct a. generalize dependent t. induction X0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (s, b).
    (** We would like
        eauto using (PreO.le_refl, PreO.le_trans)
        to work here, but it is dumb! *)
    split; simpl. reflexivity.
    etransitivity; eassumption.
    apply IHX0. reflexivity.
  + unfold FormTop.localized in locT. 
    specialize (locT _ _ X0 i).
    destruct locT.
    apply FormTop.ginfinity with (Product.PRight _ _ _ _ x s). 
    intros. simpl in *. destruct u. destruct X1.
    subst.
    specialize (s0 _ c). destruct s0 as (u & Caiu & downu).
    eapply X. eassumption.
    destruct downu. assumption.
Qed.

Context {A} `{POA : PreO.t A leA}.
Context {IA} {CA : forall (t : A), IA t -> Subset A}.
Variable locA : FormTop.localized leA CA.
Let CovA := FormTop.GCov leA CA.

Context {B} `{POB : PreO.t B leB}.
Context {IB} {CB : forall (t : B), IB t -> Subset B}.
Variable locB : FormTop.localized leB CB.
Let CovB := FormTop.GCov leB CB.

Definition parallelIG (F : Cont.map S A) (G : Cont.map T B)
  (out : A * B) (p : S * T) : Type :=
  let (s, t) := p in let (a, b) := out in
   F a s * G b t.

Existing Instances Product.PO Product.loc.

Local Instance product_cov :
  FormTop.t (prod_op leS leT) (@Product.Cov S T leS leT IS IT CS CT).
Proof.
apply FormTop.GCov_formtop.
Qed.

Require Import CRelationClasses. 

Theorem t_parallelIG (F : Cont.map S A) (G : Cont.map T B)
  : IGCont.t leS CovS leA CA F
  -> IGCont.t leT CovT leB CB G
  -> IGCont.t (prod_op leS leT) 
      (@Product.Cov _ _ leS leT IS IT CS CT)
       (prod_op leA leB)
      (@Product.C _ _ IA IB CA CB)
      (parallelIG F G).
Proof.
intros ContF ContG. constructor; intros.
- eapply FormTop.gmonotone with
  (fun s : S * T => let (s', t') := s in
  union (fun _ => True) F s' * union (fun _ => True) G t')%type.
  unfold Included, pointwise_rel, arrow; intros x H.
  destruct a, x. 
  destruct H. destruct u, u0.
  constructor 1 with (a, a0). 
  constructor. econstructor; eassumption.
  destruct a.
  eapply FormTop.monotone.
  Focus 2.
  apply Product.factors; try eassumption.
  apply (IGCont.here _ ContF). apply (IGCont.here _ ContG).
  unfold Included, pointwise_rel, arrow; intros. 
  destruct a. assumption.
- destruct a, b, c.
  destruct X, X0.
  pose proof (IGCont.local _ ContF _ _ _ f f0).
  pose proof (IGCont.local _ ContG _ _ _ g g0).
  eapply FormTop.monotone. Focus 2.
  eapply Product.factors; eassumption.
  unfold Included, pointwise_rel, arrow; intros x H.
  destruct x. destruct H. destruct u, u0.
  destruct i, i0.
  exists (a1, a2). unfold FormTop.down, In, prod_op; auto.
  split; assumption.
- destruct c, b, a. destruct X, X0; simpl in *.
  split. 
  eapply (IGCont.le_left _ ContF); eassumption.
  eapply (IGCont.le_left _ ContG); eassumption.
- destruct a, b, c. destruct X, X0. simpl in *.
  split. eapply (IGCont.le_right _ ContF); eassumption.
  eapply (IGCont.le_right _ ContG); eassumption.
- destruct j as [a0 i b | b i a0]; simpl in *.
  + destruct a.
  destruct X.
  pose proof (IGCont.ax_right _ ContF _ _ i f).
  assert (Product.Cov S T IS (leS := leS) (leT := leT) IT CS CT (s, t)
    (fun open => let (s', t') := open in (union (CA a0 i) F s') * (t = t')))%type.
  eapply Product.factors; try eassumption. apply FormTop.grefl. reflexivity.
  eapply FormTop.gmonotone. 2: apply X0.
  unfold Included, pointwise_rel, arrow; intros.
  destruct a. destruct X1. subst.
  destruct u.  exists (a, b). unfold In. split. assumption.
  reflexivity. split; assumption.
  + (** Same thing on this side. Yay! *)
  destruct a.
  destruct X.
  pose proof (IGCont.ax_right _ ContG _ _ i g).
  assert (Product.Cov S T IS (leS := leS) (leT := leT) IT CS CT (s, t)
    (fun open => let (s', t') := open in (s = s') * (union (CB b i) G t')))%type.
  eapply Product.factors; try eassumption. apply FormTop.grefl. reflexivity.
  eapply FormTop.gmonotone. 2: apply X0.
  unfold Included, pointwise_rel, arrow; intros.
  destruct a. destruct X1. subst.
  destruct u. exists (a0, a). unfold In. split. assumption. reflexivity.
  split; assumption.
Qed.

Definition parallel (F : Cont.map S A) (G : Cont.map T B) :=
  parallelIG (Cont.Sat (CovS := CovS) F) (Cont.Sat (CovS := CovT) G).

Theorem t_parallel (F : Cont.map S A) (G : Cont.map T B)
  : Cont.t leS leA CovS CovA F
  -> Cont.t leT leB CovT CovB G
  -> Cont.t (prod_op leS leT) (prod_op leA leB)
      (@Product.Cov _ _ leS leT IS IT CS CT)
      (@Product.Cov _ _ leA leB IA IB CA CB)
      (parallel F G).
Proof.
intros ContF ContG.
unfold parallel. apply IGCont.cont. 
apply FormTop.GCov_formtop. 
apply t_parallelIG; apply IGCont.converse; 
  try apply FormTop.GCov_formtop; eassumption.
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

Definition times `(LA : IGT) `(LB : IGT) : IGT :=
  let PO1 := PO LA in let PO2 := PO LB in
  {| PO := Product.PO (S LA) (S LB)
  ; localized := Product.loc _ _ _ _ _ _ (localized LA) (localized LB)
  ; pos := Product.Overt (S LA) (S LB) _ _ _ _ _ (OvertS := pos LA) (OvertT := pos LB) _
  |}.

Infix "*" := times : loc_scope.

Definition proj1_mp {A B : IGT} : Contmap (A * B) A
   := ProductMaps.proj_L (leS := le A).

Lemma proj1_mp_ok {A B : IGT} : Contprf (A * B) A proj1_mp.
Proof.
simpl.
pose proof (PO A).
apply ProductMaps.t_proj_L; try apply localized.
apply PO.
Qed.

Definition proj1 {A B : IGT} : A * B ~~> A :=
  {| mp := proj1_mp
  ; mp_ok := proj1_mp_ok
  |}.

Definition proj2_mp {A B : IGT} : Contmap (A * B) B
  := ProductMaps.proj_R (leT := le B).

Lemma proj2_mp_ok {A B : IGT} : Contprf (A * B) B proj2_mp.
Proof.
simpl.
pose proof (PO A).
apply ProductMaps.t_proj_R; try apply localized.
apply PO.
Qed.

Definition proj2 {A B : IGT} : A * B ~~> B :=
  {| mp := proj2_mp
  ; mp_ok := proj2_mp_ok
  |}.

Definition diagonal_mp {A : IGT} : Contmap A (A * A)
  := ProductMaps.diagonal (leS := le A).

Definition diagonal_mp_ok {A : IGT} : Contprf A (A * A) diagonal_mp.
Proof.
simpl. pose proof (PO A). apply ProductMaps.t_diagonal.
apply localized.
Qed.

Definition diagonal {A : IGT} : A ~~> A * A :=
  {| mp := diagonal_mp
  ; mp_ok := diagonal_mp_ok
  |}.

Definition parallel_mp {A B X Y : IGT} 
  (f : A ~~> X) (g : B ~~> Y) : Contmap (A * B) (X * Y)
  := ProductMaps.parallel (leS := le A) (CS := C A) 
      (leT := le B) (CT := C B) (mp f) (mp g).

Definition parallel_mp_ok {A B X Y : IGT}
  (f : A ~~> X) (g : B ~~> Y) :
  Contprf (A * B) (X * Y) (parallel_mp f g).
Proof.
simpl. apply ProductMaps.t_parallel; try typeclasses eauto.
apply (mp_ok f). apply (mp_ok g).
Qed.

Definition parallel {A B X Y : IGT} (f : A ~~> X) (g : B ~~> Y)
  : A * B ~~> X * Y :=
  {| mp := parallel_mp f g
   ; mp_ok := parallel_mp_ok f g
  |}.

Definition pair {Γ A B : IGT} (f : Γ ~~> A) (g : Γ ~~> B)
  : Γ ~~> A * B
  := parallel f g ∘ diagonal.
