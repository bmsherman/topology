Require Import Coq.Program.Basics 
  FormTop.FormTop 
  FormTop.Cont
  FormTop.InfoBase FormTop.Product
  Frame Algebra.Sets.

(** Here we intend to define the formal topology for the lower real
    numbers, realizing that the lower real numbers can be made into 
    a formal topology by showing that they are an information base,
    taking the rational numbers, together with the
    maximum operation, as the meet semilattice for an information base.
*)

Module LowerR.
Require Import QArith QArith.Qminmax.

Definition opsU : MeetLat.Ops Q := 
  {| MeetLat.le := Qle ; MeetLat.eq := Qeq; MeetLat.min := Qmin |}.

Definition ops : MeetLat.Ops Q := 
  {| MeetLat.le := fun x y => x >= y ; MeetLat.eq := Qeq; MeetLat.min := Qmax |}.

Instance UML : MeetLat.t Q opsU.
Proof.
constructor. constructor. constructor. 
- intros; apply Qle_refl.
- intros. eapply Qle_trans; eassumption.
- solve_proper.
- intros; apply Qle_antisym; assumption.
- solve_proper.
- intros. constructor; simpl.
  + apply Q.le_min_l. 
  + apply Q.le_min_r. 
  + intros. apply Q.min_glb; assumption.
Qed.

Instance ML : MeetLat.t Q ops.
Proof.
constructor. constructor. constructor. 
- intros; apply Qle_refl.
- simpl. intros. eapply Qle_trans; eassumption.
- simpl. solve_proper.
- intros; apply Qle_antisym; assumption.
- solve_proper.
- intros. constructor; simpl.
  + apply Q.le_max_l. 
  + apply Q.le_max_r. 
  + intros. apply Q.max_lub; assumption.
Qed.

Definition Ix := @InfoBase.Ix Q (fun x y => x >= y).
Definition C := @InfoBase.C Q (fun x y => x >= y).

Definition Cov := @InfoBase.Cov Q (fun x y => x >= y).

Definition isCov := @InfoBase.isCov Q (fun x y => x >= y) Qeq (@MeetLat.PO _ _ ML).

Instance Cov_isCov : FormTop.t (fun x y => x >= y) Cov
  := isCov.


Definition Cov' (a : Q) (U : Q -> Prop) :=
  forall u, a < u -> Cov u U.

Definition Ix' (a : Q) := option Q.

Definition C' (a : Q) (p : Ix' a) : Q -> Prop := match p with
  | None => fun u => a < u
  | Some l => fun l' => l <= a -> l == l'
  end.

Require Import QFacts.
Definition Cov'Equiv : forall a U,
  Cov' a U <-> @FormTop.GCov _ (fun x y => x >= y) Ix' C' a U.
Proof.
intros. unfold Cov'. split; intros.
- apply FormTop.ginfinity with None. simpl.
  intros. unfold Cov, InfoBase.Cov in H.
  specialize (H u H0). destruct H as (t & Ut).
  unfold flip in *.
  apply FormTop.gle_left with t. assumption.
  apply FormTop.grefl. assumption.
- generalize dependent u. 
  induction H; intros.
  + exists a. assumption. apply Qlt_le_weak. assumption.
  + apply IHGCov. eapply Qle_lt_trans; eassumption.
  + destruct i; simpl in *. 
    * apply (H0 (Qmin a q)). intros. symmetry.
      apply Q.min_r_iff. assumption.
      eapply Qle_lt_trans. apply Q.le_min_l. assumption.
    * destruct (Qbetween H1) as (mid & mida & midu).
      apply H0 with mid; assumption.
Qed.

(* Think: how can this be generalized? *)
(* Now I could use the previous proof instead. *)
Theorem isCov' : FormTop.t (fun x y => x >= y) Cov'.
Proof.
constructor; unfold Cov'; intros.
- apply FormTop.le_left with a.
  apply Qlt_le_weak. assumption. apply FormTop.refl.
  assumption.
- destruct (Qbetween H1) as (mid & mida & midu).
  unfold Cov, InfoBase.Cov in *.
  specialize (H mid mida). 
  destruct H as [t Ut lt].
  eapply H0.
  apply Ut. eapply Qle_lt_trans. apply lt. assumption.
- apply H0. eapply Qle_lt_trans; eassumption.
- apply FormTop.le_right; auto.
Qed.

End LowerR.





Require Import Algebra.Sets.

Module LPRFuncs.
Require Import QArith.

Definition lift_op (op : Q -> Q) (arg result : Q) : Prop := result < op arg.

Definition lift_binop (op : Q -> Q -> Q) (result : Q) (args : Q * Q) : Prop :=
  let (l, r) := args in (result < op l r).

Definition plusL := lift_binop Qplus.

Definition plusU (addends : Q * Q) (sum : Q) :  Prop :=
  let (l, r) := addends in (l + r <= sum).

Require Import QArith.Qminmax.

Local Instance prod_ops : MeetLat.Ops (Q * Q) := 
  MeetLat.product_ops LowerR.ops LowerR.ops.

Theorem lift_binop_cont_ib : forall op
  (le_compat : forall a a' b b', a <= a' -> b <= b' -> op a b <= op a' b'), 
  InfoBaseCont.t MeetLat.le (TOps := LowerR.ops) (lift_binop op).
Proof.
intros. constructor; unfold lift_binop; intros;
repeat match goal with
| [ a : (_ * _)%type |- _ ] => destruct a
| [ H : MeetLat.le (_, _) (_, _) |- _ ] => destruct H
end; simpl in *.
- eapply Qlt_le_trans. apply H0. 
  apply le_compat; assumption.
- eapply Qle_lt_trans; eassumption.
- apply Q.max_lub_lt; assumption.
- exists (op q q0 - 1). constructor. apply Qlt_minus_iff.
  ring_simplify. reflexivity.
Qed.

Require Import QFacts LReal.

Definition ProdCov := FormTop.GCov (prod_op (fun x y => x >= y) (fun x y => x >= y)) (Product.C _ _ _ _ LowerR.C' LowerR.C').

Theorem lift_binop_cont : forall op
  (le_compat : forall a a' b b', a <= a' -> b <= b' -> op a b <= op a' b'),
  IGCont.t (prod_op (fun x y => x >= y) (fun x y => x >= y)) 
           ProdCov
           (fun x y => x >= y) LowerR.C'
           (lift_binop op).
Proof.
intros.
constructor; intros.
- apply FormTop.grefl. destruct a as (a & b). exists (op a b - 1).
  constructor.
  apply Qlt_minus_iff. ring_simplify.
  reflexivity.
- destruct a as (a1 & a2). simpl in *.
  apply FormTop.grefl. exists (Qmax b c).
  split; [apply Q.le_max_l | apply Q.le_max_r ].
  simpl. apply Q.max_lub_lt; assumption.
- destruct a, c. simpl in *. unfold prod_op in *.
  destruct H as (pr1 & pr2). simpl in *.
  eapply Qlt_le_trans. apply H0. apply le_compat; assumption.
- destruct a as (a1 & a2). simpl in *.
  eapply Qle_lt_trans; eassumption.
- destruct a as (a1 & a2). 
  simpl; apply FormTop.grefl; destruct j; simpl in *.
  + exists (Qmin q b). unfold In. symmetry. apply Q.min_l_iff. assumption.
    eapply Qle_lt_trans. apply Q.le_min_r. assumption.
  + destruct (Qbetween H) as (mid & between).
    exists mid. apply between. apply between.
Qed.

Instance FTR : FormTop.t (fun x y => x >= y) LowerR.Cov'
  := LowerR.isCov'.

Definition pt_to_LReal (x : Q -> Prop) (ptx : Cont.pt (fun x y => x >= y) LowerR.Cov' x)
  : LReal.
Proof.
refine ({| lbound := fun q => exists u, q <= u /\ x u |}); intros.
- destruct H as (u & qu & xu).
  exists u. split. eapply Qle_trans; eassumption. assumption.
- destruct H as (u & qu & xu).
  assert (LowerR.Cov' u (fun q' => q < q')).
  unfold LowerR.Cov'.
  intros. unfold LowerR.Cov, InfoBase.Cov.
  exists u0. eapply Qle_lt_trans; eassumption. apply Qle_refl.
  pose proof (Cont.pt_cov ptx xu H).
  simpl in H0. destruct H0 as (q' & xq' & qq'); unfold In in *.
  exists xq'. split. assumption. exists xq'. split. apply Qle_refl.
  assumption.
- destruct (Cont.pt_here ptx) as (l & xl).
  exists l. exists l. split. apply Qle_refl. assumption.
Qed.

Require Import Morphisms SetoidClass.
Definition LReal_to_pt (x : LReal) : Cont.pt (fun x y => x >= y) LowerR.Cov' (lbound x).
Proof.
constructor; intros.
- apply nonempty.
- exists (Qmax b c). split. constructor. apply Q.le_max_l. apply Q.le_max_r.
  unfold In;
  destruct (Q.max_dec b c); setoid_rewrite q; assumption.
- unfold LowerR.Cov', LowerR.Cov, InfoBase.Cov in H0.
  destruct (uopen x _ H) as (x0 & bx0 & xx0).
  specialize (H0 x0 bx0).
  destruct H0 as [t Vt tl].
  exists t. split. apply dclosed with x0; assumption. assumption.
Qed.

Require Import Qnn.

Definition lift_binop_nn (op : Qnn -> Qnn -> Qnn) (result : Q) (args : Q * Q) : Prop :=
  let (l, r) := args in result >= 0 -> (Qnn_truncate result < op (Qnn_truncate l) (Qnn_truncate r))%Qnn.

Require Import Qcanon. 
Local Close Scope Qc.

Definition Qnn_truncate_mult : forall x y,
   (Qnn_truncate x * Qnn_truncate y)%Qnn = Qnn_truncate (x * y).
Proof.
intros. apply Qnneq_prop. unfold Qnneq. simpl.
apply Qc_is_canon. simpl.
Admitted.

Lemma Qnn_truncate_mono : forall x y,
  x <= y -> (Qnn_truncate x <= Qnn_truncate y)%Qnn.
Proof.
intros. unfold Qnnle. simpl. 
Admitted.

Lemma Qnn_truncate_inc : forall x y,
  x >= 0 -> x < y -> Qnn_truncate x < Qnn_truncate y.
Proof.
Admitted.

Lemma Qnn_truncate_co_inc : forall x y,
  Qnn_truncate x < Qnn_truncate y -> x < y.
Proof.
Admitted.

Lemma Qnn_truncate_co_mono : forall x y, 
  0 <= Qmax x y -> (Qnn_truncate x <= Qnn_truncate y)%Qnn
  -> x <= y.
Proof.
intros. Admitted.

Lemma Qnn_truncate_max : forall x y,
   Qnn_truncate (Qmax x y) = Qnnmax (Qnn_truncate x) (Qnn_truncate y).
Proof.
Admitted.

Definition Qnn_truncate_0 : forall x, (x <= 0) -> Qnn_truncate x = 0%Qnn.
Proof.
intros. apply Qnn_zero_prop. unfold Qnnle. simpl.
Admitted. 

Definition mult_cont : IGCont.t (prod_op (fun x y => x >= y) (fun x y => x >= y))
  (FormTop.GCov (prod_op (fun x y => x >= y) (fun x y => x >= y)) (Product.C _ _ _ _ LowerR.C' LowerR.C'))
  (fun x y => x >= y) LowerR.C'
  (lift_binop_nn Qnnmult).
Proof.
constructor; intros.
- apply FormTop.grefl. unfold lift_binop_nn. simpl.
  destruct a as (l & r).
  exists (l * r - 1). unfold In. constructor. intros.
  rewrite Qnn_truncate_mult.
  apply Qnn_truncate_inc. assumption.
  rewrite Qlt_minus_iff. ring_simplify. firstorder.
- unfold lift_binop_nn in *.
  destruct a.  simpl. 
  apply FormTop.grefl. exists (Qmax b c).
  split. apply Q.le_max_l. apply Q.le_max_r.
  
  intros. rewrite Qnn_truncate_mult in *. intros.
  apply Qnn_truncate_inc. assumption.
  destruct (Q.max_dec b c) as [bc | bc]; rewrite bc in *;
  apply Qnn_truncate_co_inc.
  + apply H. assumption.
  + apply H0. assumption.
- unfold lift_binop_nn in *. destruct a, c.
  destruct H. simpl in *. intros.  
  eapply Qlt_le_trans. apply H0. assumption.
  apply Qnnmult_le_compat; apply Qnn_truncate_mono; assumption.
- unfold lift_binop_nn in *. destruct a. intros. 
  eapply Qle_lt_trans. 2: apply H. apply Qnn_truncate_mono.
  assumption. rewrite <- H0. assumption.
- unfold lift_binop_nn in *. destruct a.
  destruct j; simpl.
  + apply FormTop.grefl. exists (Qmin q1 b). unfold In; intros. 
    symmetry. apply Q.min_l_iff. assumption. 
    intros. 
    eapply Qle_lt_trans. 2: apply H.
    apply Qnn_truncate_mono. apply Q.le_min_r.
    etransitivity. apply H0. apply Q.le_min_r.
  + apply FormTop.ginfinity with (inr (q, None)). simpl. intros.
    destruct u. destruct H0. subst. 
    apply FormTop.ginfinity with (inl (None, q2)). simpl. intros.
    destruct u. destruct H0. subst.
    apply FormTop.grefl.
    destruct (Qlt_le_dec b 0).
    * destruct (Qbetween q3) as (mid & (midl & midh)).
      exists mid. assumption. intros. rewrite Qnn_truncate_0. 
      rewrite <- Qnn_truncate_0 with b.
      apply Qle_not_lt in H2. contradiction.
      apply Qlt_le_weak; assumption. apply Qlt_le_weak; assumption.
    * specialize (H q3). 
      destruct (@Qbetween b (q * q0)) as (mid & (midl & midh)). 
      apply Qnn_truncate_co_inc. rewrite <- Qnn_truncate_mult. apply H.
      exists mid. assumption. intros. 
      eapply Qlt_le_trans. apply Qnn_truncate_inc. assumption.
      apply midh. rewrite <- Qnn_truncate_mult.
      apply Qnnmult_le_compat; apply Qnn_truncate_mono; 
      apply Qlt_le_weak; assumption.
Qed.

Definition LPRC := ImageSpace.C (fun x y => x >= y) LowerR.C' (lift_op (Qmax 0)).

Definition LPRIx := ImageSpace.Ix (fun x y => x >= y) LowerR.Ix' (lift_op (Qmax 0)).

Existing Instance LowerR.ML.

Local Instance preOQ : PreO.t (fun x y : Q => y <= x). 
apply LowerR.ML. 
Qed.

Local Instance prodPreO : PreO.t (prod_op (fun x y : Q => y <= x)
                                     (fun x y : Q => y <= x)).
Proof.
apply PreO.product; typeclasses eauto.
Qed.

Definition mult_cont_LPR : IGCont.t (prod_op (fun x y => x >= y) (fun x y => x >= y))
  (FormTop.GCovL (prod_op (fun x y => x >= y) (fun x y => x >= y)) (Product.C _ _ _ _ LPRC LPRC))
  (fun x y => x >= y) LPRC
  (lift_binop_nn Qnnmult).
Proof.
Abort.

End LPRFuncs.