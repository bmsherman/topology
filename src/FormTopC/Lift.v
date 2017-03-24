Require Import
  Coq.Classes.CMorphisms
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.FormalSpace
  FormTopC.Cont.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Local Open Scope FT.
Local Open Scope Subset. 

Module Lift.

Section Lift.

Variable (S : IGt).

Section Collapse.

Variable (T : IGt).

Variable f : S -> T.
Hypothesis fmono : forall x y, x <=[S] y -> f x <=[T] f y.
Hypothesis fPos : forall x, FormTop.gPos x -> FormTop.gPos (f x).

Definition lift : Cont.map S T := fun t s => f s <=[T] t.

Lemma le_Cov : forall a b, a <=[T] b -> a <|[T] eq b.
Proof.
intros. apply FormTop.le_left with b. assumption.
apply FormTop.refl. reflexivity.
Qed.

Lemma downset_idempotent (U : Open T) : 
 ⇓ (⇓ U) === ⇓ U.
Proof.
unfold FormTop.downset. apply Same_set_iff. intros. split; intros.
- destruct X. destruct i. econstructor. eassumption.
  etransitivity; eassumption.
- exists x. assumption. reflexivity.
Qed.

Theorem lift_cont : IGCont.t S T lift.
Proof.
constructor; intros.
- apply FormTop.refl. exists (f a). constructor. unfold lift.
  reflexivity.
- unfold lift in *.
  apply FormTop.refl. exists (f a).
  split; le_down; eassumption. reflexivity.
- unfold lift in *. rewrite <- X0. apply fmono. assumption.
- unfold lift in *. etransitivity; eassumption.
- unfold lift in *.
  apply (FormTop.gpositive).
  intros pa. pose proof (fPos _ pa) as pfa.
  assert (Inhabited ((eq t ↓ PreISpace.C T t' j) ∩ FormTop.gPos)).
  eapply FormTop.gmono_ax. assumption.
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
    | Some x => x <=[S] y
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
  | Some a => PreISpace.Ix S a
  | None => False
  end.

Definition C (ma : option S) : Ix ma -> Subset (option S) := 
  match ma as ma' return Ix ma' -> _ with
  | Some a => fun i => lift_subset (PreISpace.C S a i)
  | None => fun contra => False_rect _ contra
  end.

Definition LiftedPO : FormTop.PreOrder :=
  {| PO_car := option S
   ; FormTop.le := le
  |}.

Definition Lifted : PreISpace.t :=
  {| PreISpace.S := LiftedPO 
   ; PreISpace.Ix := Ix
   ; PreISpace.C := C
  |}.

Local Instance loc (H : FormTop.localized S) : FormTop.localized Lifted.
Proof.
unfold FormTop.localized in *.
intros. destruct c; try contradiction.
destruct a; try contradiction.
destruct (H p0 p X i).
exists x. simpl.  intros. simpl in X.
intros u Pu. destruct u; try contradiction.
simpl in Pu. destruct (i0 _ Pu). clear i0.
le_downH d. destruct d0. 
split. le_down. assumption.
exists (Some a). unfold In. simpl. assumption. assumption. 
Qed.

Inductive bottom : Subset (option S) :=
  | MkBottom : bottom None.

Theorem Cov_None V : None <|[toPSL Lifted] V -> In V None.
Proof.
intros cov. remember None as none.
induction cov; subst; simpl in *; try contradiction; auto.
- destruct b; simpl in *. contradiction.
  apply IHcov. reflexivity.
- induction b; simpl in *; contradiction.
Qed.

Theorem pt_bottom : Cont.pt (toPSL Lifted) bottom.
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

Definition inj : Cont.map S (toPSL Lifted) := fun my x => match my with
  | None => True
  | Some y => x <=[S] y
  end.

Local Open Scope Subset.

Lemma inj_lift V x : In (union (lift_subset V) inj) x -> 
  x <|[S] V.
Proof. intros X. destruct X. unfold In in *.
destruct a; simpl in *. apply FormTop.le_left with p. 
assumption. apply FormTop.refl. assumption.
contradiction.
Qed.

Theorem inj_cont : Cont.t S (toPSL Lifted) inj.
Proof.
constructor; intros.
- apply FormTop.refl. constructor 1 with None.
  constructor. simpl. constructor.
- destruct b; simpl in *.
  etransitivity; eassumption. constructor.
- apply FormTop.refl. destruct b; simpl in *.
  + constructor 1 with (Some a).
    split; le_down; assumption. simpl. reflexivity.
  + destruct c; simpl in *.
    * constructor 1 with (Some a). split; le_down; assumption.
      simpl. reflexivity.
    * constructor 1 with None. split; le_down; constructor.
      simpl. constructor.
- destruct b; simpl in *. 
  + remember (Some p) as somes.
    assert (le (Some a) somes). subst. simpl. assumption. clear Heqsomes.
    clear X. 
    generalize dependent a. 
    induction X0; intros.
    * destruct a; simpl in *.
      { apply FormTop.le_left with p0. assumption.
        apply FormTop.refl. constructor 1 with (Some p0).
        assumption. simpl. reflexivity. }
      { apply FormTop.glrefl. constructor 1 with None.
      assumption. simpl. assumption. }
    * apply IHX0. etransitivity; eassumption.
    * destruct a; try contradiction.
      simpl in *. 
      apply FormTop.le_left with p0. assumption.
      destruct b. simpl in l. 
      simpl in i.
      apply FormTop.gle_infinity with p1 i. assumption.
      intros. destruct X0. le_downH d. destruct d0.
      eapply X. split. le_down. instantiate (1 := Some u). 
      eassumption. exists (Some a). simpl. unfold In.
      simpl. assumption. simpl. assumption. reflexivity.
      induction i. 
      induction b; simpl in *; contradiction.
  + apply FormTop.glrefl. constructor 1 with None.
    apply Cov_None. assumption. simpl. constructor.
Qed.

End Lift.

End Lift.