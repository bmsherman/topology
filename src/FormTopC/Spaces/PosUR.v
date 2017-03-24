Require Import
  CoRN.model.structures.QposInf

  Prob.StdLib
  Numbers.QPosFacts
  FormTopC.FormTop
  FormTopC.Cont
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder.

Set Universe Polymorphism.

Local Open Scope FT.

(** I get a Coq error with using the typeclasses
    if I leave le as returning Prop *)
Definition le (x y : QposInf) : Type := QposInf_le x y.

Definition PosURPO : PreOrder :=
  {| PO_car := QposInf
   ; PreOrder.le := le
  |}.

Definition lt (x y : QposInf) : Type :=
  ((x <=[PosURPO] y) * ((y <=[PosURPO] x) -> False))%type.

Local Infix "<" := lt.

Inductive Ix : QposInf -> Type :=
  | IxFinite : forall x, Ix (Qpos2QposInf x).

Definition C (q : QposInf) (ix : Ix q) : Subset QposInf
  := match ix with
  | IxFinite x => fun q' => lt q' x
  end.

Instance PO : PreO.t le.
Proof.
constructor; unfold le; intros.
- destruct x; simpl. apply Qle_refl. constructor.
- destruct x, y, z; simpl in *; try (constructor || contradiction).
 eapply Qle_trans; eassumption.
Qed.

Existing Instance PreO.PreOrder_I.

Lemma lt_le_trans (x y z : QposInf) : x < y -> y <=[PosURPO] z -> x < z.
Proof.
unfold lt in *. 
intros P Q. destruct P as (P1 & P2). split.
etransitivity; eassumption.
intros.  apply P2. etransitivity; eassumption.
Qed.

Lemma lt_le_weak (x y : QposInf) : x < y -> x <=[PosURPO] y.
Proof.
intros H. destruct H. assumption.
Qed. 

Definition PosUR : PreISpace.t :=
  {| PreISpace.S := PosURPO
   ; PreISpace.C := C
  |}.

Instance loc : FormTop.localized PosUR.
Proof.
unfold FormTop.localized.
intros. destruct i; simpl in *.
destruct a.
- exists (IxFinite q). simpl. intros s Ps.
  split. le_down. eapply lt_le_weak. eassumption.
  exists s. unfold In. eapply lt_le_trans; eassumption. 
  reflexivity.
- contradiction.
Qed.

Definition fromQpos (x : Qpos) (y : QposInf) := x < y.

Definition Pt := IGCont.pt PosUR.

Local Open Scope Subset.

Lemma Qpos_lt_equiv (x y : Qpos) :
  (x < y) <--> (x < y)%Q.
Proof.
split; intros.
- destruct X. simpl in *. apply Qnot_le_lt.
  unfold not; intros contra. apply f.
  unfold le. simpl. apply contra.
- split. apply Qlt_le_weak. assumption.
  intros. pose proof (Qlt_not_le _ _ H).
  apply H0. assumption.
Qed.

Definition Qpos_smaller' (x : Qpos) : { y : Qpos & y < x }.
Proof.
destruct (Qpos_smaller x) as [x' prf].
exists x'. apply Qpos_lt_equiv. apply prf.
Qed.

Definition QposInf_smaller (x : QposInf) : { y : Qpos & y < x }.
Proof.
destruct x.
- apply Qpos_smaller'.
- exists Qpos_one. unfold lt. simpl. auto.
Qed.

Lemma Qpos_plus_lt (x y : Qpos) : x < x + y.
Proof.
unfold lt. split.
- unfold le. simpl.
  setoid_replace (x : Q) with (x + 0)%Q at 1.
  apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak.
  apply Qpos_prf. ring.
- unfold le. simpl. 
  setoid_replace (x : Q) with (x + 0)%Q at 2 by ring.
  intros. apply Q.Qplus_le_r in H.
  eapply Qlt_not_le. 2:eassumption. apply Qpos_prf.
Qed.

Lemma QposInf_between (x y : QposInf) : x < y ->
  { z : QposInf & ((x < z) * (z < y))%type }.
Proof.
intros H. destruct x, y.
Admitted.

Definition Qpos_pt (x : Qpos) : Pt (fromQpos x).
Proof.
apply IGLCont.localized_pt_impl.
constructor; intros.
- simpl. exists (x + 1)%Qpos. unfold In, fromQpos.
  apply Qpos_plus_lt.
- exists (QposInf_min b c). constructor.
  split; le_down. apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  unfold fromQpos in *.
  unfold QposInf_min. destruct b.
  + destruct c.
    apply QposMinMax.Qpos_min_case; intros; assumption.
    assumption.
  + assumption.
- unfold fromQpos in *. eapply lt_le_trans; eassumption.
- destruct i.
  unfold fromQpos in *. unfold C.
  destruct (QposInf_between x x0 X).
  destruct p. exists x1. split; assumption.
Qed.


Definition URzero (x : QposInf) : Type := unit.

Definition URzero_pt : Pt URzero.
Proof.
apply IGLCont.localized_pt_impl.
constructor; intros.
- simpl. exists 1%Qpos. constructor.
- exists (QposInf_min b c). constructor.
  split; le_down. apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  constructor.
- constructor.
- destruct i. 
  destruct (QposInf_smaller x).
  simpl. exists x0. split. constructor. assumption.
Qed.

Inductive URinfty : QposInf -> Type :=
  MkURinfty : URinfty QposInfinity.

Definition URinfty_pt : Pt URinfty.
Proof.
apply IGLCont.localized_pt_impl.
constructor; intros.
- exists QposInfinity. constructor.
- exists (QposInf_min b c). constructor.
  split; le_down.  apply QposInf_min_lb_l. apply QposInf_min_lb_r.
  destruct X, X0. simpl. constructor.
- destruct X. destruct b; simpl in *. contradiction. 
  econstructor.
- destruct i. exists QposInfinity. split. constructor.
  simpl. inversion X. 
Qed.

Record pt :=
  { LT :> Subset QposInf
  ; LT_pt : Pt LT
  }.

Definition pt_le (x y : pt) := forall q, LT x q -> q <|[toPSL PosUR] LT y.

Definition pt_eq (x y : pt) := (pt_le x y * pt_le y x)%type.
Definition zero : pt :=
  {| LT := URzero ; LT_pt := URzero_pt |}.