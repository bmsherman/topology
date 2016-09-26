Require Import
  Algebra.Sets
  Algebra.Frame
  FormTop.FormTop
  FormTop.Cont.

Module Alexandroff.

Section Alexandroff.

Context {S} {leS : S -> S -> Prop} {POS : PreO.t leS}.
Context {IxS : S -> Type}.
Context {CS : forall a, IxS a -> Ensemble S}.
Context {locS : FormTop.localized leS CS}.

Let CovS := FormTop.GCov leS CS.

Section Collapse.

Context {T} {leT : T -> T -> Prop} {POT : PreO.t leT}.
Context {IxT : T -> Type}.
Context {CT : forall a, IxT a -> Ensemble T}.
Context {locT : FormTop.localized leT CT}.

Let CovT := FormTop.GCov leT CT.

Variable f : S -> T.
Hypothesis fmono : forall x y, leS x y -> leT (f x) (f y).

Definition lift : Cont.map S T := fun t s => leT (f s) t.

Lemma le_Cov : forall a b, leT a b -> CovT a (eq b).
Proof.
intros. apply FormTop.gle_left with b. assumption.
apply FormTop.grefl. reflexivity.
Qed.

Local Instance FTT : FormTop.t leT CovT := 
  FormTop.GCov_formtop _ _.

Theorem lift_cont : Cont.t leS leT CovS CovT lift.
Proof.
constructor; intros.
- apply FormTop.grefl. exists (f a). constructor. unfold lift.
  reflexivity.
- unfold lift in *. rewrite <- H0. apply fmono. assumption.
- unfold lift in *.
  apply le_Cov in H. apply le_Cov in H0.
  pose proof (FormTop.le_right (f a) (eq b) (eq c) H H0).
  (** I need to use the "monotonicity property"
      of a positivity predicate... *)
Abort. 

End Collapse.

Definition lift_subset (U : Ensemble S) : Ensemble (option S) :=
  fun ms => match ms with
    | Some x => In U x
    | None => False
  end.

Definition unlift_subset (U : Ensemble (option S)) : Ensemble S :=
  fun s => U (Some s).

Definition le (mx my : option S) : Prop := match my with
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

Definition C (ma : option S) : Ix ma -> Ensemble (option S) := 
  match ma as ma' return Ix ma' -> _ with
  | Some a => fun i => lift_subset (CS a i)
  | None => fun contra => False_rect _ contra
  end.

Local Instance loc : FormTop.localized le C.
Proof.
unfold FormTop.localized in *.
intros. destruct c; try contradiction.
destruct a; try contradiction.
destruct (locS s0 s H i). clear locS.
exists x. simpl.  intros. destruct s1; try contradiction. 
destruct (H0 s1 H1).  clear H0.
exists (Some x0). destruct H2.  split. simpl. assumption.
assumption.
Qed.

Inductive bottom : Ensemble (option S) :=
  | MkBottom : bottom None.

Definition Cov := FormTop.GCov le C.

Theorem Cov_None : forall V, Cov None V -> In V None.
Proof.
intros. remember None as none.
induction H; subst; simpl in *; try contradiction; auto.
destruct b; simpl in *. contradiction.
apply IHGCov. reflexivity.
Qed.

Theorem pt_bottom : Cont.pt le Cov bottom.
Proof.
constructor. 
- constructor 1 with None. constructor.
- intros. induction H, H0.
  constructor 1 with None.
  repeat (econstructor || eauto).
- intros. constructor 1 with None.
  destruct H; try contradiction.
  constructor. constructor. apply Cov_None. assumption.
Qed.

Definition inj : Cont.map S (option S) := fun my x => match my with
  | None => True
  | Some y => leS x y
  end.

Local Open Scope Ensemble.

Lemma inj_lift : forall V x, In (union (lift_subset V) inj) x -> 
  CovS x V.
Proof. intros. destruct H. unfold In in *.
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
    clear H. 
    generalize dependent a. 
    induction H0; intros.
    * destruct a; simpl in *.
      { apply FormTop.gle_left with s0. assumption.
        apply FormTop.grefl. constructor 1 with (Some s0).
        assumption. simpl. reflexivity. }
      { apply FormTop.grefl. constructor 1 with None.
      assumption. simpl. assumption. }
    * apply IHGCov. etransitivity; eassumption.
    * destruct a; try contradiction.
      simpl in *. 
      apply FormTop.gle_left with s0. assumption.
      apply FormTop.ginfinity with i.
      intros. apply (H0 (Some u)). simpl. assumption.
      reflexivity.
  + apply FormTop.grefl. constructor 1 with None.
    apply Cov_None. assumption. simpl. constructor.
Qed.


Require Import FormTop.Product.

(** Simple thing which will help make fixpoint
    Take the left-biased answer
    A generalization of the OR function for Sierpinski
    space
  A⊥ * A⊥ ~~> A⊥
*)

Definition f_or : Cont.map (option S * option S) (option S) :=
  fun my => match my with
  | None => fun _ => True
  | Some y => fun mx => match mx with
    | (Some x1, _) => leS x1 y
    | (None, Some x2) => leS x2 y
    | (None, None) => False
    end
  end.


End Alexandroff.

End Alexandroff.