Require Import Coq.Program.Basics
  FormTop.FormTop Frame Algebra.Sets.

(** Information bases, which are the predicative versions of
    Scott domains. Perhaps, see Definition 1.9 of [2].
    Though my formulation is a little different; I build off
    of a pre-existing notion of a meet semi-lattice.

    Also, I directly show that this formal topology is
    inductively generated by generating it with an axiom set. *)
Module InfoBase. 
Section InfoBase.

Generalizable All Variables.

Context {S : Type} `{PO : PO.t S leS eqS}.

(** The axiom set essentially says that if [s <= t], then
    [s] is covered by the singleton set [{t}]. *)
Definition Ix (s : S) : Type := { t : S & leS s t }.
Definition C (s : S) (s' : Ix s) s'' : Prop := eqS (projT1 s') s''.

(** This axiom set is localized. *)
Definition loc : FormTop.localized leS C.
Proof.
pose proof (@PO.t_equiv _ _ _ PO) as eqEquiv.
unfold FormTop.localized. intros. simpl.
unfold Ix, C in *.
destruct i. simpl.
assert (leS a a).
apply PreO.le_refl.
exists (existT _ a H0).
intros.  simpl in *. 
exists x. split. reflexivity.
split. 
rewrite H1. apply PreO.le_refl.
rewrite <- H1.
eapply PreO.le_trans. eapply H. eassumption.
Qed.

Definition Cov (s : S) (U : Ensemble S) : Prop :=
  In (FormTop.downset leS U) s.

(** The covering relation for information bases,
    which we derive from the axiom set above. *)
Definition GCov := @FormTop.GCov _ leS Ix C.

Require Import Morphisms SetoidClass.
Theorem CovEquiv : forall s U, Cov s U <-> GCov s U.
Proof.
intros. unfold Cov, GCov. split; intros.
- destruct H as [t Ut st].
  apply FormTop.ginfinity with (existT _ t st).
  unfold C. simpl. intros.
  apply FormTop.gle_left with t.
  rewrite H. apply PreO.le_refl.
  apply FormTop.grefl. assumption.
- induction H. 
  + exists a. assumption. unfold flip. apply PreO.le_refl.
  + destruct IHGCov as [t Ut bt].
    exists t. assumption. unfold flip. eapply PreO.le_trans; eassumption.
  + destruct i. unfold C in *. simpl in *.
    assert (eqS x x) as eqx. reflexivity.
    specialize (H x eqx).
    specialize (H0 x eqx). destruct H0 as [t Ut xt].
    exists t. assumption. unfold flip in *. eapply PreO.le_trans; eassumption.
Qed.

(** The proof that [Cov] is a valid formal topology. *)
Instance isCovG : FormTop.t leS GCov := 
  FormTop.GCov_formtop _ Ix C loc.

Require Import Morphisms.
Instance isCov : FormTop.t leS Cov.
Proof.
assert ((eq ==> eq ==> iff)%signature Cov GCov).
pose proof CovEquiv.
simpl_relation. rewrite H. apply isCovG.
Qed.

End InfoBase.
End InfoBase.

Module InfoBaseCont.
Section InfoBaseCont.

Generalizable All Variables.

Require Import Morphisms.

Context {S} `{MLS : MeetLat.t S}.
Context {T} `{MLT : MeetLat.t T}.

Record pt {F : Ensemble T} : Prop :=
  { pt_local : forall {a b}, F a -> F b -> F (MeetLat.min a b)
  ; pt_le_right : forall a b, MeetLat.le a b -> F a -> F b
  ; pt_here : Inhabited F
  }.

Arguments pt : clear implicits.

Instance pt_proper : Proper ((eq ==> iff) ==> iff) pt.
Proof.
Admitted.


(** I have no idea whether this is in fact
    a good definition *)
Record t {F : S -> T -> Prop} :=
  { le_left : forall a b c, MeetLat.le a b -> F b c -> F a c
  ; le_right :  forall a b c,  F a b -> MeetLat.le b c -> F a c
  ; local : forall {a b c}, F a b -> F a c -> F a (MeetLat.min b c)
  ; here : forall s, Inhabited (F s)
  }.

Arguments t : clear implicits.


Let CovS : S -> (Ensemble S) -> Prop := @InfoBase.Cov _ MeetLat.le.
Let CovT : T -> (T -> Prop) -> Prop := @InfoBase.Cov _ MeetLat.le.

Theorem cont : forall (F : S -> T -> Prop),
  t F
  -> Cont.t MeetLat.le MeetLat.le CovS CovT F.
Proof.
intros. constructor; intros.
- unfold CovS, InfoBase.Cov. exists a. 
  apply (here H). unfold flip. apply PreO.le_refl.
- eapply (le_left H); eassumption. 
- unfold CovS, InfoBase.Cov. exists a. 
  exists (MeetLat.min b c). split. 
  split; apply MeetLat.min_ok. apply local; assumption.
  unfold flip. reflexivity.
- unfold CovT, CovS, InfoBase.Cov in *. 
  destruct H1 as [t0 Vt0 bt0].
  exists a. exists t0. assumption.
  apply (le_right H) with b; assumption.
  unfold flip. reflexivity.
Qed.

End InfoBaseCont.

Arguments t {_} {_} {_} {_} F.
Arguments pt {_} {_} F.

Section Compose.

Context {S : Type} {SOps} {MLS : MeetLat.t S SOps}.

Instance OneOps : MeetLat.Ops True := MeetLat.one_ops.

Theorem to_pt : forall (F : True -> Ensemble S), t F ->
  pt (F I).
Proof.
intros. constructor; intros.
- apply (local H); assumption. 
- eapply (le_right H); eassumption. 
- apply (here H).
Qed.

Theorem from_pt : forall (F : Ensemble S), pt F -> t (fun _ => F).
Proof.
intros. constructor; intros.
- assumption.
- eapply (pt_le_right H); eassumption.
- apply (pt_local H); assumption.
- apply (pt_here H).
Qed.

Context {T TOps} {MLT : MeetLat.t T TOps}.
Context {U UOps} {MLU : MeetLat.t U UOps}.

Theorem t_compose (F : S -> T -> Prop) (G : T -> U -> Prop)
  : t F -> t G
  -> t (compose F G).
Proof.
intros HF HG.
constructor; unfold compose; intros.
- destruct H0 as (t & Fbt & Gtc).
  exists t. split. 
  + eapply (le_left HF); eassumption.
  + assumption.
- destruct H as (t & Fat & Gtb).
  exists t. split. assumption. eapply (le_right HG); eassumption.
- destruct H as (t & Fat & Gtb).
  destruct H0 as (t' & Fat' & Gt'c).
  exists (MeetLat.min t t'). split. 
  + apply (local HF); assumption.
  + apply (local HG); eapply (le_left HG). 
    apply MeetLat.min_l. assumption. 
    apply MeetLat.min_r. assumption. 
- destruct (here HF s). destruct (here HG x).
  exists x0. exists x. auto.
Qed.

End Compose.

Section EvalPt.

Context {S SOps} {MLS : MeetLat.t S SOps}.
Context {T TOps} {MLT : MeetLat.t T TOps}.

Definition eval (F : S -> T -> Prop) (x : Ensemble S) (t : T) : Prop :=
  exists s, x s /\ F s t.

Require Import Morphisms.
Theorem eval_pt (F : S -> T -> Prop) (x : Ensemble S)
  : pt x -> t F -> pt (eval F x).
Proof.
intros Hx HF.
pose proof (t_compose (fun _ => x) F (from_pt _ Hx) HF).
apply to_pt in H. 
eapply pt_proper. 2: eassumption. simpl_relation.
Qed.

End EvalPt.

End InfoBaseCont.

Arguments InfoBaseCont.t {S} SOps {T} TOps F : rename, clear implicits.

Module One.
Section One.

Definition Cov (_ : True) (U : True -> Prop) : Prop := U I.

Require Import Morphisms.
Theorem CovEquiv : (eq ==> eq ==> iff)%signature Cov (@InfoBase.Cov _ (fun _ _ => True)).
Proof.
simpl_relation.
intros. unfold Cov, InfoBase.Cov. split; intros.
- exists I; unfold flip; tauto.
- destruct H as [[] Ut _]. assumption.
Qed.

Instance MLOne : MeetLat.t True MeetLat.one_ops := MeetLat.one.
Instance POOne : @PO.t True (fun _ _ => True) (fun _ _ => True) := @MeetLat.PO _ _ MLOne.

Instance FTOne : FormTop.t (@MeetLat.le _ MeetLat.one_ops) Cov.
Proof.
rewrite CovEquiv.
apply InfoBase.isCov.
Qed.

Instance one_ops : MeetLat.Ops True := MeetLat.one_ops.

Require Import Morphisms.
Definition FTtoFrame : 
  Frame.morph (FormTop.FOps MeetLat.le Cov) Frame.prop_ops (fun U => U I).
Proof.
simpl. unfold Cov.
constructor.
- constructor.
  + constructor. simpl. unfold FormTop.leA, FormTop.Sat, Cov.
    unfold PreO.morph. intros. 
    unfold Included, In in H. auto.
    simpl_relation. simpl in *. unfold FormTop.eqA, FormTop.Sat in *.
    unfold Same_set in *. destruct H.
    unfold Included, In in *. split; auto.
  + simpl. intros. split. intros. destruct H; tauto.
    intros. destruct H. left. assumption. right. assumption.
  + simpl. unfold FormTop.minA. unfold FormTop.downset, flip. intros.
    split; intros. destruct H. destruct H, H0.
    destruct x, a0, a1. auto.
    destruct H. constructor; econstructor; eauto. 
- simpl. intros. split; intros. destruct H. destruct s. 
  exists i. assumption. destruct H. econstructor; eauto.
- simpl. split; intros []; intros. 
  exists True. constructor. constructor 1 with (fun _ => True). constructor.
Qed.

Context {S} {leS eqS : S -> Ensemble S} {POS : PO.t leS eqS}.
Variable CovS : S -> (Ensemble S) -> Prop.

Definition Point (f : Ensemble S) := Cont.t MeetLat.le leS Cov CovS (fun _ => f).

Hypothesis FTS : FormTop.t leS CovS.

Instance FrameS : Frame.t (Ensemble S) (FormTop.FOps leS CovS)
  := FormTop.Frame leS CovS _ FTS.

Instance FrameOne : Frame.t (True -> Prop) (FormTop.FOps MeetLat.le Cov)
  := FormTop.Frame MeetLat.le Cov _ FTOne.

Definition toFPoint (f : Ensemble S) (pointf : Point f) :
  Frame.cmap Frame.prop_ops (FormTop.FOps leS CovS) :=
  {| Frame.finv := fun x => Cont.frame (fun _ => f) x I 
  ; Frame.cont := Frame.morph_compose _ _
    (Cont.toFrame FTOne FTS (fun _ => f) pointf) FTtoFrame |}.

End One.
End One.

Module Discrete.
Section Discrete.

Generalizable All Variables.

Variable A : Type.

Hypothesis deceq : forall a a' : A, {a = a'} + {a <> a'}.

Definition Ix := @InfoBase.Ix _ (@Logic.eq A).
Definition C := @InfoBase.C _ (@Logic.eq A).
Definition CovI := @InfoBase.Cov _ (@Logic.eq A).

(** Woops I should have a positivity predicate to say that the
    "None" is covered by nothing *)
Definition Cov (a : A) (U : A -> Prop) : Prop := U a.

Require Import Morphisms.
Theorem CovEquiv : (eq ==> eq ==> iff)%signature CovI Cov.
Proof.
simpl_relation. unfold Cov, CovI, InfoBase.Cov.
split; intros.
- destruct H as [x t xt leat]. unfold flip in *. subst. assumption. 
-  exists y; unfold flip; auto.
Qed.

Instance FTproper : Proper _ FormTop.t := @FormTop.t_proper A.
Instance discretePO : PO.t Logic.eq Logic.eq := PO.discrete A.

Instance isCov : FormTop.t Logic.eq Cov.
Proof.
rewrite <- CovEquiv.
apply InfoBase.isCov.
Qed.

End Discrete.

Section FinFunc.

Context {A B : Type}.
Hypothesis deceqA : forall a a' : A, {a = a'} + {a <> a'}.
Hypothesis deceqB : forall b b' : B, {b = b'} + {b <> b'}.

Definition discrF (f : A -> B) (x : A) (y : B) : Prop := f x = y.

Instance POB : PO.t Logic.eq Logic.eq := PO.discrete B.

Ltac inv H := inversion H; clear H; subst.

Theorem fCont (f : A -> B) :
  Cont.t Logic.eq Logic.eq (Cov A) (Cov B) (discrF f).
Proof.
constructor; unfold Cov; intros.
- exists (f a). constructor.
- subst. assumption.
- inv H. inv H0. exists (f a). split.
  split; reflexivity. constructor.
- exists b; unfold In; auto.
Qed.

End FinFunc.

End Discrete.