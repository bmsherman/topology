Require Import
  Algebra.SetsC
  Algebra.FrameC
  FormTopC.FormTop
  FormTopC.Cont
  Coq.Classes.CMorphisms.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Module Lift.

Section Lift.

Context {S} {leS : crelation S} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Subset S}.
Context {locS : FormTop.localized leS CS}.

Let CovS := FormTop.GCov leS CS.

Section Collapse.

Context {T} {leT : crelation T} {POT : PreO.t leT}.
Context {IxT : T -> Type}.
Context {CT : forall a, IxT a -> Subset T}.
Context {locT : FormTop.localized leT CT}.

Let CovT := FormTop.GCov leT CT.

Context {tPosS : FormTop.gtPos leS CS}.
Context {tPosT : FormTop.gtPos leT CT}.


Variable f : S -> T.
Hypothesis fmono : forall x y, leS x y -> leT (f x) (f y).
Hypothesis fPos : forall x, FormTop.gPos x -> FormTop.gPos (f x).

Definition lift : Cont.map S T := fun t s => leT (f s) t.

Lemma le_Cov : forall a b, leT a b -> CovT a (eq b).
Proof.
intros. apply FormTop.gle_left with b. assumption.
apply FormTop.grefl. reflexivity.
Qed.

Local Instance FTT : FormTop.t leT CovT := 
  FormTop.GCov_formtop.

Local Open Scope Subset. 

Lemma downset_idempotent U : 
 FormTop.downset leT (FormTop.downset leT U) === FormTop.downset leT U.
Proof.
unfold FormTop.downset. apply Same_set_iff. intros. split; intros.
- destruct X. destruct i. econstructor. eassumption.
  etransitivity; eassumption.
- exists x. assumption. reflexivity.
Qed.

Theorem lift_cont : IGCont.t leS CovS leT CT lift.
Proof.
constructor; intros.
- apply FormTop.grefl. exists (f a). constructor. unfold lift.
  reflexivity.
- unfold lift in *.
  apply FormTop.grefl. exists (f a).
  split; eassumption. reflexivity.
- unfold lift in *. rewrite <- X0. apply fmono. assumption.
- unfold lift in *. etransitivity; eassumption.
- unfold lift in *.
  apply (FormTop.gpositive).
  intros pa. pose proof (fPos _ pa) as pfa.
  assert (Inhabited (CT b j ∩ FormTop.gPos)).
  eapply FormTop.gmono_ax. 
  eapply FormTop.gmono_le; eassumption.
  admit. (* This is a big hole. *)
Abort. 

End Collapse.

Definition lift_subset (U : Subset S) : Subset (option S) :=
  fun ms => match ms with
    | Some x => In U x
    | None => False
  end.

Definition unlift_subset (U : Subset (option S)) : Subset S :=
  fun s => U (Some s).

Definition le (mx my : option S) : Type := match my with
  | None => True
  | Some y => match mx with
    | None => False
    | Some x => leS x y
    end
  end.

Local Instance PreO_le : PreO.t le.
Proof.
constructor; intros.
- destruct x; simpl; auto. reflexivity.
- destruct x, y, z; simpl in *; 
    constructor || contradiction || 
  (etransitivity ; eassumption) || eassumption.
Qed. 

Definition Ix (ma : option S) : Type := match ma with
  | Some a => IxS a
  | None => False
  end.

Definition C (ma : option S) : Ix ma -> Subset (option S) := 
  match ma as ma' return Ix ma' -> _ with
  | Some a => fun i => lift_subset (CS a i)
  | None => fun contra => False_rect _ contra
  end.

Local Instance loc : FormTop.localized le C.
Proof.
unfold FormTop.localized in *.
intros. destruct c; try contradiction.
destruct a; try contradiction.
destruct (locS s0 s X i). clear locS.
exists x. simpl.  intros. destruct s2; try contradiction. 
destruct (s1 s2 X0).  clear X0.
exists (Some x0). destruct p.  split. simpl. assumption.
assumption.
Qed.

Inductive bottom : Subset (option S) :=
  | MkBottom : bottom None.

Definition Cov := FormTop.GCov le C.

Theorem Cov_None V : Cov None V -> In V None.
Proof.
intros cov. remember None as none.
induction cov; subst; simpl in *; try contradiction; auto.
destruct b; simpl in *. contradiction.
apply IHcov. reflexivity.
Qed.

Theorem pt_bottom : Cont.pt le Cov bottom.
Proof.
constructor. 
- constructor 1 with None. constructor.
- intros b c X X0. induction X, X0.
  constructor 1 with None.
  repeat (econstructor || eauto).
- intros. constructor 1 with None.
  destruct X; try contradiction.
  constructor. constructor. apply Cov_None. assumption.
Qed.

Definition inj : Cont.map S (option S) := fun my x => match my with
  | None => True
  | Some y => leS x y
  end.

Local Open Scope Subset.

Lemma inj_lift V x : In (union (lift_subset V) inj) x -> 
  CovS x V.
Proof. intros X. destruct X. unfold In in *.
destruct a; simpl in *. apply FormTop.gle_left with s. 
assumption. apply FormTop.grefl. assumption.
contradiction.
Qed.

Theorem inj_cont : Cont.t leS le CovS Cov inj.
Proof.
constructor; intros.
- apply FormTop.grefl. constructor 1 with None.
  constructor. simpl. constructor.
- destruct b; simpl in *.
  etransitivity; eassumption. constructor.
- apply FormTop.grefl. destruct b; simpl in *.
  + constructor 1 with (Some a).
    split; assumption. simpl. reflexivity.
  + destruct c; simpl in *.
    * constructor 1 with (Some a). split; assumption.
      simpl. reflexivity.
    * constructor 1 with None. split; constructor.
      simpl. constructor.
- destruct b; simpl in *. 
  + remember (Some s) as somes.
    assert (le (Some a) somes). subst. simpl. assumption. clear Heqsomes.
    clear X. 
    generalize dependent a. 
    induction X0; intros.
    * destruct a; simpl in *.
      { apply FormTop.gle_left with s0. assumption.
        apply FormTop.grefl. constructor 1 with (Some s0).
        assumption. simpl. reflexivity. }
      { apply FormTop.grefl. constructor 1 with None.
      assumption. simpl. assumption. }
    * apply IHX0. etransitivity; eassumption.
    * destruct a; try contradiction.
      simpl in *. 
      apply FormTop.gle_left with s0. assumption.
      apply FormTop.ginfinity with i.
      intros. apply (X (Some u)). simpl. assumption.
      reflexivity.
  + apply FormTop.grefl. constructor 1 with None.
    apply Cov_None. assumption. simpl. constructor.
Qed.

End Lift.

End Lift.