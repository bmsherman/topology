Require Import 
  Basics
  FormTopC.FormTop Algebra.SetsC Algebra.FrameC
  CRelationClasses.

Set Universe Polymorphism.
Local Open Scope Subset.

(** Continuous maps. *)
Module Cont.

Definition map (S T : Type) := T -> Subset S.

Section Cont.

Context {S leS} `{POS : PreO.t S leS}.
Context {T leT} `{POT : PreO.t T leT}.

Context {CovS : S -> Subset S -> Type}.
Context {CovT : T -> Subset T -> Type}.

Record t {F_ : map S T} : Type :=
  { here : forall a, CovS a (union (fun _ => True) F_)
  ; le_left : forall a b c, leS a c -> F_ b c -> F_ b a
  ; local : forall {a b c}, F_ b a -> F_ c a
    -> CovS a (union (FormTop.down leT b c) F_)
  ; cov : forall {a b} V, F_ b a -> CovT b V
    -> CovS a (union V F_)
  }.

Arguments t F_ : clear implicits.

Definition Sat (F_ : map S T) : map S T := fun t s =>
  CovS s (F_ t).

Definition func_LE (F_ G_ : map S T) : Type :=
  RelIncl (Sat F_) (Sat G_).

Definition func_EQ (F_ G_ : map S T) : Type :=
  RelSame (Sat F_) (Sat G_).

Global Instance func_LE_PreOrder : PreOrder func_LE.
Proof.
constructor; unfold Reflexive, Transitive, func_LE; intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Global Instance func_EQ_Equivalence : Equivalence func_EQ.
Proof.
constructor; unfold Reflexive, Transitive, Symmetric, func_EQ; intros.
- reflexivity.
- symmetry; assumption.
- etransitivity; eassumption.
Qed.

Lemma func_LE_antisym : forall (F F' : map S T),
  func_LE F F' -> func_LE F' F -> func_EQ F F'.
Proof.
unfold func_LE, func_EQ. intros.
apply RelIncl_RelSame; assumption.
Qed.

Lemma RelSame_RelIncl A B (F F' : A -> Subset B) :
  RelSame F F' -> RelIncl F F'.
Proof.
unfold RelSame, RelIncl.
intros. rewrite X. reflexivity.
Qed.

Lemma func_EQ_LE F F' : func_EQ F F' -> func_LE F F'.
Proof.
unfold func_EQ, func_LE. intros. apply RelSame_RelIncl.
assumption.
Qed.

Record pt {F : Subset T} :=
  { pt_here : Inhabited F
  ; pt_local : forall {b c}, F b -> F c -> Inhabited (FormTop.down leT b c ∩ F)
  ; pt_cov : forall {b V}, F b -> CovT b V -> Inhabited (F ∩ V)
  }.

Arguments pt F : clear implicits.

(** Convert a continuous map for formal topologies to a 
    frame homomorphism (i.e., continuous map on locales)
  *)
Definition frame (F_ : map S T) (U : Subset T) : Subset S :=
  union U F_.

Hypothesis FTS : FormTop.t leS CovS. 
Hypothesis FTT : FormTop.t leT CovT.

Lemma Sat_mono2 (F_ : map S T) : RelIncl F_ (Sat F_).
Proof.
unfold RelIncl. intros. unfold Sat.
unfold Included, pointwise_rel, arrow; intros.
apply FormTop.refl. assumption.
Qed.

Lemma Sat_mono (F_ G_ : map S T) : 
  RelIncl F_ G_ -> 
  RelIncl (Sat F_) (Sat G_).
Proof.
unfold RelIncl, Sat; intros.
unfold Included, pointwise_rel, arrow; intros.
eapply FormTop.monotone. apply X. assumption.
Qed.

Lemma Sat_idempotent (F_ : map S T) :
  RelSame (Sat F_) (Sat (Sat F_)).
Proof.
apply RelIncl_RelSame. apply Sat_mono2.
unfold RelIncl, Included, pointwise_rel, arrow, Sat.
intros.
eapply FormTop.trans. eassumption.
intros. assumption.
Qed.

Section DirectedSup.
Context {Ix : Type} `{JoinLat.t Ix}.
Variable (f : Ix -> map S T).
Variable (fmono : forall i j, JoinLat.le i j -> RelIncl (f i) (f j)).
Definition func_Dsup : map S T := fun t s =>
  { i : Ix & f i t s }.

Lemma oneIncl i : RelIncl (f i) func_Dsup.
Proof.
intros. unfold RelIncl, Included, pointwise_rel, arrow; intros.
exists i. assumption.
Qed.

Lemma single_Dsup : forall i a U,
 CovS a (union U (f i)) ->
 CovS a (union U func_Dsup).
Proof.
intros.  eapply FormTop.Cov_Proper. typeclasses eauto. 
  reflexivity. apply union_monotone. apply (oneIncl i).
assumption.
Qed.

Variable nonempty : Ix.

Lemma func_Dsup_Cont : (forall i, Cont.t (f i)) -> Cont.t func_Dsup.
Proof.
intros iCont. constructor; intros.
- eapply single_Dsup. apply (Cont.here (iCont nonempty)).
- unfold func_Dsup in *. destruct X0.
  exists x. eapply (Cont.le_left (iCont x)); eassumption.
- destruct X, X0.
  pose (x' := JoinLat.max x x0).
  apply single_Dsup with x'.
  apply (Cont.local (iCont x')).
  eapply fmono; (apply JoinLat.max_ok || assumption).
  eapply fmono. eapply PreO.max_r. apply JoinLat.max_ok. 
  assumption.
- destruct X. apply single_Dsup with x.
  eapply (Cont.cov (iCont x)). eassumption. assumption.
Qed.

End DirectedSup.

Let FrameS := FormTop.Frame leS CovS.
Let FrameT := FormTop.Frame leT CovT.

Variable F_ : T -> Subset S.
Hypothesis cont : t F_.

Local Instance POFS : @PO.t (Subset S) (FormTop.leA CovS) (FormTop.eqA CovS).
Proof.
eapply FormTop.FramePO.
Qed.

Local Instance POFT : @PO.t (Subset T) (FormTop.leA CovT) (FormTop.eqA CovT).
Proof.
eapply FormTop.FramePO.
Qed.

Theorem monotone : PreO.morph (FormTop.leA CovT) (FormTop.leA CovS)
   (frame F_).
Proof.
unfold PreO.morph. intros. unfold frame.
simpl. unfold FormTop.leA, FormTop.Sat.
unfold Included, pointwise_rel, arrow.
intros a' H. simpl in H.
apply (FormTop.trans _ _ _ H). intros a1 H1.
destruct H1 as [t' at' Fa't'].
apply (cov cont _ Fa't'). apply X. unfold FormTop.Sat.
apply FormTop.refl. assumption.
Qed.

Require Import CMorphisms.

Local Instance Cov_Proper : Proper (leS --> Included ==> arrow) CovS.
Proof.
 apply FormTop.Cov_Proper. assumption.
Qed.

Local Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) CovS.
Proof.
 eapply FormTop.Cov_Proper2; eassumption.
Qed.

Theorem Sat_Proper : forall A leA `{PreO.t A leA} (Cov : A -> Subset A -> Type)
  `{FormTop.t _ leA Cov},
  Proper (Same_set ==> Same_set) (FormTop.Sat Cov).
Proof.
intros. unfold Proper, respectful. intros. unfold FormTop.Sat.
apply Same_set_iff. intros. apply FormTop.subset_equiv.
assumption.
Qed.

Local Instance Cov_Proper3 : Proper (leS ==> Included --> flip arrow) CovS.
Proof.
 eapply FormTop.Cov_Proper3; eassumption.
Qed.

Existing Instances FormTop.Cov_Proper union_Proper.

(** This shouldn't be necessary. It should essentially
    follow from union_Proper. *)
Local Instance union_Proper_flip : 
  forall A B, Proper ((@Included A) --> eq ==> flip (@Included B)) union.
Proof.
intros. unfold Proper, respectful; intros. subst. 
apply union_Proper. assumption. reflexivity.
Qed.

Theorem toLattice : 
   L.morph (FormTop.LOps leT CovT) (FormTop.LOps leS CovS) (frame F_).
Proof.
constructor.
  + constructor.
     * apply monotone.
     * repeat intro. split; apply monotone; simpl in X;
       rewrite X; apply PreO.le_refl.
  + intros. unfold frame. simpl. unfold FormTop.eqA.
    eapply Sat_Proper; try eassumption.
    symmetry. apply Union_union.
  + intros. unfold frame. simpl. apply PO.le_antisym;
    unfold FormTop.leA, FormTop.Sat, Included, pointwise_rel, arrow; intros.
    * apply (FormTop.trans _ _ _ X). clear a0 X.
      intros. unfold FormTop.minA in X.
      destruct X. destruct i. destruct d, d0.
      unfold FormTop.minA.
      apply FormTop.le_right;
      apply (cov cont _ f).
      apply FormTop.le_left with a2. assumption.
      apply FormTop.refl. assumption.
      apply FormTop.le_left with a3. assumption.
      apply FormTop.refl. assumption.
    * apply (FormTop.trans _ _ _ X). clear a0 X.
      intros. unfold FormTop.minA in *.
      destruct X. destruct d, d0. destruct i, i0.
      rewrite <- FormTop.down_downset; try eassumption.
      apply local. assumption. 
      eapply le_left with a1; eassumption.
      eapply le_left with a2; eassumption.
Qed.

(** Broken due to universe inconsistency
Theorem toFrame : Frame.morph 
  (FormTop.FOps leT CovT) (FormTop.FOps leS CovS) (frame F_).
Proof.
constructor.
- apply toLattice.
- unfold frame. simpl. intros.
  unfold FormTop.eqA. eapply Sat_Proper; try eassumption.
  intros; split; unfold Included, In; intros.
  + destruct H. destruct H. repeat econstructor; eauto.
  + destruct H. destruct H. repeat econstructor; eauto. 
- unfold frame. simpl. unfold FormTop.eqA, FormTop.Sat.
  intros. split; unfold Included, In; intros.
  + apply FormTop.refl. exists (fun _ => True). constructor.
  + pose proof (here cont x).
    eapply FormTop.trans. apply H0. clear H0. intros. 
    destruct H0. apply FormTop.refl. 
    repeat (econstructor; try eassumption).
Qed.

Definition toCmap : Frame.cmap (FormTop.FOps leS CovS)
  (FormTop.FOps leT CovT) :=
  {| Frame.finv := frame F_
   ; Frame.cont := toFrame |}.
*)


End Cont.

Arguments t {S} leS {T} leT CovS CovT F_ : clear implicits.
Arguments pt {T} leT CovT F : clear implicits.

Require Import CMorphisms.

Lemma t_Proper : forall S T (leS : crelation S) (leT : crelation T), Proper
  ((eq ==> eq ==> iffT) ==> (eq ==> eq ==> iffT) ==> eq ==> iffT) (t leS leT).
Proof.
Admitted.


Section Morph.

Context {S leS} `{POS : PreO.t S leS}.
Context {CovS} `{FTS : FormTop.t S leS CovS}.

Definition id (x y : S) := leS y x.

Theorem t_id : t leS leS CovS CovS id.
Proof.
constructor; intros; unfold id in *.
- eapply FormTop.refl. exists a; eauto. unfold In. constructor. 
  reflexivity.
- eapply PreO.le_trans; eassumption.
- apply FormTop.refl. exists a. split; eassumption.
  reflexivity.
- eapply FormTop.trans with (fun b' => b = b').
  eapply FormTop.le_left. eassumption.
  apply FormTop.refl. reflexivity. unfold In.  
  intros. subst. eapply FormTop.monotone.
  2:eassumption. apply FormTop.downset_included.
Qed.

Context {T leT} `{POT : PreO.t T leT}.
Context {CovT} `{FTT : FormTop.t T leT CovT}.

Theorem refine_Cont : forall (CovS' : S -> Subset S -> Type)
  (CovT' : T -> Subset T -> Type)
  (ref : forall a U, CovS a U -> CovS' a U)
  (ref' : forall b V, CovT' b V -> CovT b V)
  (F : map S T),
    Cont.t leS leT CovS CovT F
  -> Cont.t leS leT CovS' CovT' F.
Proof.
intros. constructor; intros.
- apply ref. apply (here X).
- eapply (le_left X); eassumption.
- apply ref. apply (local X); assumption.
- apply ref. eapply (cov X). eassumption.
  apply ref'. assumption.
Qed.

Context {U leU} `{POU : PreO.t U leU}.
Context {CovU} `{FTU : FormTop.t U leU CovU}.

(*
Everything in s maps to u
iff there is some subset T such that
  everything in s maps to T and
  everything in T maps to u
*)

Theorem t_compose : forall (F : map S T) (G : map T U),
    t leS leT CovS CovT F
  -> t leT leU CovT CovU G
  -> t leS leU CovS CovU (compose G F).
Proof.
intros. constructor; intros.
- pose proof (here X a).
  eapply FormTop.trans. eassumption.
  simpl. intros. destruct X2. destruct i.
  pose proof (here X0 a1).
  pose proof (cov X _ f X2).
  refine (FormTop.monotone _ _ _ _ X3).
  rewrite union_compose. reflexivity.
- unfold compose in *.
  intros. 
  destruct X2 as [t1 [Fat1 Gt1b]]. 
  exists t1. split. eassumption. eapply (le_left X). eassumption.
  assumption.
- destruct X1 as [t1 [Gt1b Fat1]]. 
  destruct X2 as [t2 [Gt2b Fat2]].
  pose proof (local X Fat1 Fat2).
  eapply FormTop.trans.
  eassumption. simpl. intros.
  destruct X2 as (tt & downtt & Fatt).
  apply (FormTop.monotone)
  with (union (union (FormTop.down leU b c) G) F). 
  rewrite union_compose; reflexivity.
  eapply (cov X). eassumption.
  apply (local X0).
  eapply (le_left X0). eapply downtt. eassumption.
  eapply (le_left X0). eapply Fatt. eassumption.
- destruct X1 as [t [Gtb Fat]].
  apply (FormTop.monotone) with (union (union V G) F).
  rewrite union_compose; reflexivity.
  apply (cov X _ Fat).
  apply (cov X0 _ Gtb). assumption.
Qed.

Lemma compose_proper_LE : forall (F F' : map S T) (G G' : map T U),
  Cont.t leS leT CovS CovT F' ->
  func_LE (CovS := CovS) F F' -> func_LE (CovS := CovT) G G' -> 
  func_LE (CovS := CovS) (compose G F) (compose G' F').
Proof.
unfold func_LE, compose. 
intros F F' G G' ContF X X0. unfold RelSame.
intros. unfold RelIncl, Included, pointwise_rel, arrow.
unfold Sat, In.
intros. unfold In in *.
  eapply FormTop.trans. eassumption. unfold In. intros.
  clear a0 X1. destruct X2.  destruct p. 
  apply (Sat_mono2 (leS := leT) (CovS := CovT)) in g.
  apply (Sat_mono2 (leS := leS) (CovS := CovS)) in f.
  apply X0 in g. apply X in f.
  unfold Sat in g, f. eapply FormTop.trans. eassumption.
  intros. clear a1 f.
  pose proof (fun a b => Cont.cov ContF (a := a) (b := b)).
  specialize (X2 _ _ _ X1 g).
  eapply FormTop.trans.  eassumption.
  clear a0 X1 X2 g. intros. destruct X1. 
  apply FormTop.refl. exists a1. split; assumption.
  eassumption. eassumption.
Qed.

Lemma compose_proper : forall (F F' : map S T) (G G' : map T U),
  Cont.t leS leT CovS CovT F ->
  Cont.t leS leT CovS CovT F' ->
  func_EQ (CovS := CovS) F F' -> func_EQ (CovS := CovT) G G' -> 
  func_EQ (CovS := CovS) (compose G F) (compose G' F').
Proof.
intros. apply func_LE_antisym; apply compose_proper_LE;
  repeat (assumption || apply func_EQ_LE || symmetry).
Qed.

End Morph.
End Cont.

Arguments Cont.t {S} leS {T} leT CovS CovT F_ : clear implicits.


Module IGCont.
Section IGCont.
Generalizable All Variables.
Context {S} `{POS : PreO.t S leS}.
Context {CovS : S -> Subset S -> Type}.
Variable FTS : FormTop.t leS CovS.

Context {T} `{POT : PreO.t T leT}.
Context {IT : T -> Type}.
Variable CT : forall (t : T), IT t -> Subset T.
Variable locT : FormTop.localized leT CT.
Let CovT := FormTop.GCov leT CT.

Record t {F_ : Cont.map S T} :=
  { here : forall a, CovS a (union (fun _ : T => True) F_)
  ; local : forall a b c, F_ b a -> F_ c a ->
       CovS a (union (FormTop.down leT b c) F_)
  ; le_left : forall a b c, leS a c -> F_ b c -> F_ b a
  ; le_right :  forall a b c, F_ b a -> leT b c -> F_ c a
  ; ax_right : forall a b (j : IT b), F_ b a -> 
     CovS a (union (CT b j) F_)
  }.

Arguments t : clear implicits.

(** Lemma 2.28 of "Exponentiation of unary topologies over 
    inductively generated formal topologies" *)
Theorem cont : forall F, t F -> Cont.t leS leT CovS CovT F.
Proof.
intros. constructor; intros.
- apply (here X).
- eapply le_left; eassumption.
- apply local; assumption.
- generalize dependent a. induction X1; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply IHX1. eapply le_right; eassumption.
  + pose proof (ax_right X _ _ i X1).
    apply (@FormTop.trans S leS CovS FTS _ _ _ X2).  
    intros. destruct X3. 
    eapply X0; eassumption.
Qed.

Existing Instances union_Proper FormTop.Cov_Proper.

Lemma Cov_Sat : forall a U (F : Cont.map S T), 
  CovS a (union U F) ->
  CovS a (union U (Cont.Sat (CovS := CovS) F)).
Proof.
intros. 
eapply (FormTop.Cov_Proper _ _). reflexivity. 
  eapply union_monotone.
  eapply Cont.Sat_mono2. eassumption. assumption.
Qed.

Theorem converse : forall F, Cont.t leS leT CovS CovT F 
  -> t (Cont.Sat (CovS := CovS) F).
Proof.
intros. 
constructor; intros.
- apply Cov_Sat. eauto using (Cont.here X).
- unfold Cont.Sat in *. 
  apply Cov_Sat.
  pose proof (FormTop.le_right _ _ _ X0 X1).
  clear X0 X1.
  eapply FormTop.trans. eassumption.
  clear a X2. intros. destruct X0. destruct d, d0.
  apply (Cont.local X); eapply (Cont.le_left X). 
  apply l. assumption. apply l0. assumption.
- unfold Cont.Sat in *. 
  eapply FormTop.le_left; eassumption.
- unfold Cont.Sat in *. 
  eapply FormTop.trans. eassumption.
  intros. 
  assert (CovT b (eq c)).
  eapply FormTop.gle_left. eassumption.
  apply FormTop.grefl. reflexivity.
  pose proof (Cont.cov X (a := a0) (b := b) (eq c)).
  eapply FormTop.monotone. Focus 2. apply X4.
  assumption. assumption.
  unfold Included, pointwise_rel, arrow.
  intros. destruct X5.  destruct i. assumption.
- unfold Cont.Sat in X0. 
  eapply FormTop.trans. eassumption. clear a X0.
  intros. apply Cov_Sat. eapply (Cont.cov X). eassumption.
  apply FormTop.ginfinity with j. intros. 
  apply FormTop.grefl. assumption.
Qed.

End IGCont.
End IGCont.

Arguments IGCont.t {S} leS CovS
                   {T} leT {IT} CT F_ : clear implicits.



Module ImageSpace.
Section Defn.
Context {S : Type} {leS : crelation S} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Subset S}.

Let CovS := FormTop.GCovL leS CS.
Instance FTS : FormTop.t leS CovS := 
  FormTop.GCovL_formtop CS.

Context {T : Type} {leT : crelation T} {POT : PreO.t leT}.
Context {CovT : T -> Subset T -> Type}.
Context {FTT : FormTop.t leT CovT}.
Context {F : Cont.map S T} {contF : Cont.t leS leT CovS CovT F}.

(** From Palmgren's
  [Predicativity problems in point-free topology]
*)
Inductive Ix1 {a : S} : Type :=
  | Orig : IxS a -> Ix1
  | Img : forall t, F t a -> Ix1.

Arguments Ix1 : clear implicits.

Definition C1 (a : S) (i : Ix1 a) : Subset S := match i with
  | Orig i' => CS a i'
  | Img t Fat => FormTop.downset leS (F t)
  end.

Definition Ix := FormTop.IxL (le := leS) (Ix := Ix1).
Definition C := FormTop.CL (le := leS) (Ix := Ix1) C1.

Definition loc : FormTop.localized leS C
  := FormTop.Llocalized C1.

Definition Cov := FormTop.GCov leS C.

Instance Cov_isCov : FormTop.t leS Cov.
Proof.
apply FormTop.GCov_formtop. apply loc.
Qed.

Context {U : Type} {leU : U -> U -> Prop} {POU : PreO.t leU}.
Context {CovU : U -> Subset U -> Prop}.
Context {FTU : FormTop.t leU CovU}.

Lemma AxRefine : FormTop.AxiomSetRefine CS C1.
Proof.
unfold FormTop.AxiomSetRefine. intros. 
exists (Orig i). simpl. reflexivity.
Qed.

Theorem cont_preserved : forall (G : U -> Subset S),
  Cont.t leS leU CovS CovU G ->
  Cont.t leS leU Cov  CovU G.
Proof.
intros. apply (Cont.refine_Cont (CovS := CovS) (CovT := CovU)).
- intros. unfold Cov, C. apply FormTop.cov_equiv.
  eapply FormTop.AxRefineCovL. apply AxRefine.
  apply X0. 
- auto.
- assumption.
Qed.

Theorem cont_preserved_im : forall (G : S -> Subset U)
  (G_img : forall a b V, G b a -> Cov b V -> CovS b V),
  Cont.t leU leS CovU CovS G ->
  Cont.t leU leS CovU Cov  G.
Proof.
intros G G_img H. destruct H.
constructor; intros. 
- apply here.
- eauto using le_left.
- eauto using local.
- eauto using cov, G_img.
Qed.

End Defn.

Arguments Ix {S} leS IxS {T} F a : clear implicits.
Arguments Cov {S} leS {IxS} CS {T} F _ _ : clear implicits.
Arguments C {S} leS {IxS} CS {T} F _ _ _ : clear implicits.

Section ExampleDef.

Context {S : Type} {leS : crelation S} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Subset S}.

Theorem id_same : forall a U, iffT (FormTop.GCovL leS CS a U)
  (Cov leS CS (Cont.id (leS := leS)) a U).
Proof.
unfold Cov, C. 
intros.
eapply iffT_Transitive. 2: apply FormTop.cov_equiv.
unfold Cont.id; intros; split; intros.
- induction X.
  + apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b; assumption.
  + apply FormTop.gle_infinity with b (Orig i).
    assumption. assumption.
-  induction X.
  + apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b; assumption.
  + destruct i; simpl in *.
    * apply FormTop.gle_infinity with b i; assumption.
    * eapply X. exists b. unfold FormTop.down.
      repeat (unfold In || econstructor 
            || reflexivity || assumption).
Qed.


End ExampleDef.

End ImageSpace.