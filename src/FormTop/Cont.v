Require Import 
  Basics
  FormTop.FormTop 
  Algebra.Sets
  Algebra.Frame.

Local Open Scope Ensemble.

(** Continuous maps. *)
Module Cont.

Definition map (S T : Type) := T -> Ensemble S.

Section Cont.

Context {S leS} `{POS : PreO.t S leS}.
Context {T leT} `{POT : PreO.t T leT}.

Context {CovS : S -> Ensemble S -> Prop}.
Context {CovT : T -> Ensemble T -> Prop}.

Record t {F_ : map S T} : Prop :=
  { here : forall a, CovS a (union (fun _ => True) F_)
  ; le_left : forall a b c, leS a c -> F_ b c -> F_ b a
  ; local : forall {a b c}, F_ b a -> F_ c a
    -> CovS a (union (FormTop.down leT b c) F_)
  ; cov : forall {a b} V, F_ b a -> CovT b V
    -> CovS a (union V F_)
  }.

Arguments t F_ : clear implicits.


Record pt {F : T -> Prop} :=
  { pt_here : Inhabited F
  ; pt_local : forall {b c}, F b -> F c -> Inhabited (FormTop.down leT b c ∩ F)
  ; pt_cov : forall {b V}, F b -> CovT b V -> Inhabited (F ∩ V)
  }.

Arguments pt F : clear implicits.

(** Convert a continuous map for formal topologies to a 
    frame homomorphism (i.e., continuous map on locales)
  *)
Definition frame (F_ : map S T) (U : Ensemble T) : Ensemble S :=
  union U F_.

Hypothesis FTS : FormTop.t leS CovS. 
Hypothesis FTT : FormTop.t leT CovT.

Let FrameS := FormTop.Frame leS CovS.
Let FrameT := FormTop.Frame leT CovT.

Variable F_ : T -> Ensemble S.
Hypothesis cont : t F_.

Local Instance POFS : @PO.t (Ensemble S) (FormTop.leA CovS) (FormTop.eqA CovS).
Proof.
eapply FormTop.FramePO.
Qed.

Local Instance POFT : @PO.t (T -> Prop) (FormTop.leA CovT) (FormTop.eqA CovT).
Proof.
eapply FormTop.FramePO.
Qed.

Theorem monotone : PreO.morph (FormTop.leA CovT) (FormTop.leA CovS)
   (frame F_).
Proof.
unfold PreO.morph. intros. unfold frame.
simpl. unfold FormTop.leA, FormTop.Sat.
unfold Included, In.
intros. simpl in H. unfold FormTop.leA, FormTop.Sat in H.
apply (FormTop.trans _ _ _ H0). intros.
destruct H1 as [t' at' Fa't'].
apply (cov cont _ Fa't'). apply H. unfold In. apply FormTop.refl.
assumption.
Qed.

Require Import Morphisms SetoidClass.

Instance Cov_Proper : Proper (leS --> Included ==> impl) CovS.
Proof.
 apply FormTop.Cov_Proper. assumption.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iff) CovS.
Proof.
 eapply FormTop.Cov_Proper2; eassumption.
Qed.

Theorem Sat_Proper : forall A leA `{PreO.t A leA} (Cov : A -> Ensemble A -> Prop)
  `{FormTop.t _ leA Cov},
  Proper (Same_set ==> Same_set) (FormTop.Sat Cov).
Proof.
intros. unfold Proper, respectful. intros. unfold FormTop.Sat.
apply Same_set_iff. intros. apply FormTop.subset_equiv.
assumption.
Qed.

Existing Instance union_Proper.

Theorem toLattice : 
   L.morph (FormTop.LOps leT CovT) (FormTop.LOps leS CovS) (frame F_).
Proof.
constructor.
  + constructor.
     * apply monotone.
     * repeat intro. split; apply monotone; simpl in H;
       rewrite H; apply PreO.le_refl.
  + intros. unfold frame. simpl. unfold FormTop.eqA.
    eapply Sat_Proper; try eassumption.
    symmetry. apply Union_union.
  + intros. unfold frame. simpl. apply PO.le_antisym;
    unfold FormTop.leA, FormTop.Sat, Included, In; intros.
    * apply (FormTop.trans _ _ _ H). clear x H.
      intros. unfold FormTop.minA in H.
      destruct H. destruct H. destruct H, H1.
      unfold flip in *. 
      unfold FormTop.minA.
      apply FormTop.le_right;
      apply (cov cont _ H0).
      apply FormTop.le_left with a1. assumption.
      apply FormTop.refl. assumption.
      apply FormTop.le_left with a2. assumption.
      apply FormTop.refl. assumption.
    * apply (FormTop.trans _ _ _ H). clear x H.
      intros. unfold FormTop.minA in *.
      destruct H. destruct H, H0. destruct H, H0.
      rewrite <- FormTop.down_downset; try eassumption.
      apply local. assumption. 
      eapply le_left with a0; eassumption.
      eapply le_left with a1; eassumption.
Qed.

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


End Cont.

Arguments t {S} leS {T} leT CovS CovT F_ : clear implicits.
Arguments pt {T} leT CovT F : clear implicits.

Require Import Morphisms.

Lemma t_Proper : forall S T (leS : S -> S -> Prop) (leT : T -> T -> Prop), Proper
  ((eq ==> eq ==> iff) ==> (eq ==> eq ==> iff) ==> eq ==> iff) (t leS leT).
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

Theorem refine_Cont : forall (CovS' : S -> Ensemble S -> Prop)
  (CovT' : T -> Ensemble T -> Prop)
  (ref : forall a U, CovS a U -> CovS' a U)
  (ref' : forall b V, CovT' b V -> CovT b V)
  (F : map S T),
    Cont.t leS leT CovS CovT F
  -> Cont.t leS leT CovS' CovT' F.
Proof.
intros. constructor; intros.
- apply ref. apply (here H).
- eapply (le_left H); eassumption.
- apply ref. apply (local H); assumption.
- apply ref. eapply (cov H). eassumption.
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
- pose proof (here H a).
  eapply FormTop.trans. eassumption.
  simpl. intros. destruct H2. destruct H2.
  pose proof (here H0 a1).
  pose proof (cov H _ H3 H2).
  refine (FormTop.monotone _ _ _ _ H4).
  apply union_compose.
- unfold compose in *.
  intros. 
  destruct H2 as [t1 [Fat1 Gt1b]]. 
  exists t1. split. eassumption. eapply (le_left H). eassumption.
  assumption.
- destruct H1 as [t1 [Gt1b Fat1]]. 
  destruct H2 as [t2 [Gt2b Fat2]].
  pose proof (local H Fat1 Fat2).
  eapply FormTop.trans.
  eassumption. simpl. intros.
  destruct H2 as (tt & downtt & Fatt).
  apply (FormTop.monotone)
  with (union (union (FormTop.down leU b c) G) F). 
  apply union_compose.
  eapply (cov H). eassumption.
  apply (local H0).
  eapply (le_left H0). eapply downtt. eassumption.
  eapply (le_left H0). eapply Fatt. eassumption.
- destruct H1 as [t [Gtb Fat]].
  apply (FormTop.monotone) with (union (union V G) F).
  apply union_compose.
  apply (cov H _ Fat).
  apply (cov H0 _ Gtb). assumption.
Qed.

End Morph.
End Cont.

Arguments Cont.t {S} leS {T} leT CovS CovT F_ : clear implicits.


Module IGCont.
Section IGCont.
Generalizable All Variables.
Context {S} `{POS : PreO.t S leS}.
Context {CovS : S -> Ensemble S -> Prop}.
Variable FTS : FormTop.t leS CovS.

Context {T} `{POT : PreO.t T leT}.
Context {IT : T -> Type}.
Variable CT : forall (t : T), IT t -> (T -> Prop).
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
- apply (here H).
- eapply le_left; eassumption.
- apply local; assumption.
- generalize dependent a. induction H1; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply IHGCov. eapply le_right; eassumption.
  + pose proof (ax_right H _ _ i H2).
    apply (@FormTop.trans S leS CovS FTS _ _ _ H3).  
    intros. destruct H4. 
    eapply H1; eassumption.
Qed.

(** This is actually not true, and it's a problem with
    my definition of general continuity. Really annoying. *)
Lemma saturation : forall F, Cont.t leS leT CovS CovT F ->
  forall a b W, CovS a W -> (forall w, In W w -> F b w) -> F b a.
Proof.
Admitted.

Theorem converse : forall F, Cont.t leS leT CovS CovT F -> t F.
Proof.
intros. 
constructor; intros.
- eauto using (Cont.here H).
- eauto using (Cont.local H).
- eauto using (Cont.le_left H).
- eapply saturation. eassumption. 
  eapply (Cont.cov H (b := b) (eq c)). eassumption.
  apply FormTop.gle_left with c. assumption.
  apply FormTop.grefl. reflexivity.
  intros. destruct H2. destruct H2. assumption.
- eapply FormTop.monotone. Focus 2.  eapply (Cont.cov H).
  eassumption. apply FormTop.ginfinity with j.
  intros. apply FormTop.grefl. eassumption.
  unfold Included, In; intros. destruct H1.
  exists a0; eauto.
Qed.

End IGCont.
End IGCont.

Arguments IGCont.t {S} leS CovS
                   {T} leT {IT} CT F_ : clear implicits.



Module ImageSpace.
Section Defn.
Context {S : Type} {leS : S -> S -> Prop} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Ensemble S}.

Let CovS := FormTop.GCovL leS CS.
Instance FTS : FormTop.t leS CovS := 
  FormTop.GCovL_formtop CS.

Context {T : Type} {leT : T -> T -> Prop} {POT : PreO.t leT}.
Context {CovT : T -> Ensemble T -> Prop}.
Context {FTT : FormTop.t leT CovT}.
Context {F : Cont.map S T} {contF : Cont.t leS leT CovS CovT F}.

(** From Palmgren's
  [Predicativity problems in point-free topology]
*)
Inductive Ix1 {a : S} : Type :=
  | Orig : IxS a -> Ix1
  | Img : forall t, F t a -> Ix1.

Arguments Ix1 : clear implicits.

Definition C1 (a : S) (i : Ix1 a) : Ensemble S := match i with
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
Context {CovU : U -> Ensemble U -> Prop}.
Context {FTU : FormTop.t leU CovU}.

Lemma AxRefine : FormTop.AxiomSetRefine CS C1.
Proof.
unfold FormTop.AxiomSetRefine. intros. 
exists (Orig i). simpl. reflexivity.
Qed.

Theorem cont_preserved : forall (G : U -> Ensemble S),
  Cont.t leS leU CovS CovU G ->
  Cont.t leS leU Cov  CovU G.
Proof.
intros. apply (Cont.refine_Cont (CovS := CovS) (CovT := CovU)).
- intros. unfold Cov, C. rewrite <- FormTop.cov_equiv.
  eapply FormTop.AxRefineCovL. apply AxRefine.
  apply H0. 
- auto.
- assumption.
Qed.

Theorem cont_preserved_im : forall (G : S -> Ensemble U)
  (G_img : forall a b V, G b a -> Cov b V -> CovS b V),
  Cont.t leU leS CovU CovS G ->
  Cont.t leU leS CovU Cov  G.
Proof.
intros. destruct H.
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

Context {S : Type} {leS : S -> S -> Prop} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Ensemble S}.

Theorem id_same : forall a U, FormTop.GCovL leS CS a U <-> 
  Cov leS CS (Cont.id (leS := leS)) a U.
Proof.
unfold Cov, C. 
intros. rewrite <- FormTop.cov_equiv.
unfold Cont.id; intros; split; intros.
- induction H.
  + apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b; assumption.
  + apply FormTop.gle_infinity with b (Orig i).
    assumption. assumption.
-  induction H.
  + apply FormTop.glrefl. assumption.
  + apply FormTop.glle_left with b; assumption.
  + destruct i; simpl in *.
    * apply FormTop.gle_infinity with b i; assumption.
    * eapply H1. exists b. unfold FormTop.down.
      repeat (unfold In || econstructor 
            || reflexivity || assumption).
Qed.


End ExampleDef.

End ImageSpace.