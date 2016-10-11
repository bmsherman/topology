Require Import 
  Algebra.FrameC
  FormTopC.Product
  FormTopC.Discrete
  FormTopC.Bundled.

Module Scott.

Section Scott.

Variable A B : IGT.

Definition le_Open (U V : Subset (S B)) :=
  V ⊆ FormTop.Sat (Cov B) U.

Lemma Sat_Cov : forall U V,
  U ⊆ FormTop.Sat (Cov B) V
  -> FormTop.Sat (Cov B) U ⊆ FormTop.Sat (Cov B) V.
Proof.
intros. unfold FormTop.Sat, Included, pointwise_rel, arrow in *.
intros. FormTop.trans X0. apply X; assumption. 
Qed.

Local Instance PreOrder_le_Open : PreO.t le_Open.
Proof.
unfold le_Open; constructor; 
  unfold Reflexive, Transitive; intros.
- apply (FormTop.Sat_mono _ _ _).
- rewrite X0. apply Sat_Cov; assumption.
Qed.

Definition eq_Open := PO.eq_PreO le_Open.

(** Define abstraction to Sierpinski space
    S * T ~~> Σ   -->    S ~~> Open T  
*)

Existing Instances Sierpinski.ops Sierpinski.SML.

Let prod_le := prod_op leS leT.
Let prodC := Product.C _ _ IxS IxT CS CT.
Let prodCov := FormTop.GCov prod_le prodC.
Let sierpCov := FormTop.GCov MeetLat.le Sierpinski.C.

Variable F : Contmap (S * T) (discrete bool).
Hypothesis contF : Cont.t
   prod_le MeetLat.le prodCov sierpCov F.

(** "false" is the smallest open set in the Sierpinski space,
    which confusingly is the open set surrounding the
    "top" or "true" point. *)


Definition absF (subset : Subset T) (s : S) : Type :=
  le_Open (fun t => F false (s, t)) subset.

Let OpenCov := FormTop.GCov le_Open (InfoBase.C
  (leS := le_Open)
  (eqS := eq_Open)).

Local Instance FTS : FormTop.t leS CovS.
Proof.
apply FormTop.GCov_formtop.
Qed.

Lemma le_Open_mono U V :
  V ⊆ U -> le_Open U V.
Proof.
intros H. unfold le_Open.
rewrite H. apply (FormTop.Sat_mono leT CovT).
Qed.

Local Instance PO_le_eq : PO.t le_Open eq_Open
  := PO.fromPreO _. 
Existing Instance PO.fromPreO.

(** This seems really suspicious. It's probably wrong. *)
Theorem absF_cont : Cont.t leS le_Open CovS OpenCov absF.
Proof.
constructor; intros.
- apply FormTop.grefl. constructor 1 with (fun _ => False).
  constructor. unfold absF. unfold le_Open. 
  unfold Included, pointwise_rel, arrow; intros.
  contradiction.
- unfold absF in *. rewrite <- X0.
  apply le_Open_mono.
  unfold Included, pointwise_rel, arrow; intros.
  eapply (Cont.le_left contF (a, a0) false (c, a0)).
  unfold prod_le, prod_op. simpl. split. eassumption.
  reflexivity. assumption.
- unfold absF in *.
  apply FormTop.grefl.
  exists (b ∪ c). split; apply le_Open_mono.
  apply Union_Included_l.
  apply Union_Included_r.
  unfold Included, In in *.
  unfold le_Open in *.
  unfold Included, pointwise_rel, arrow; intros.
  destruct X1. apply X. assumption. apply X0. assumption.
- induction X0; simpl in *. 
  + apply FormTop.grefl. constructor 1 with a0; assumption.
  + apply IHX0. unfold absF. 
    unfold absF in X.
    unfold le_Open in *.
    rewrite l. apply Sat_Cov. assumption.
  + destruct i; simpl in *.
    apply (X0 t). reflexivity.
    unfold absF, le_Open in *.
    rewrite l. apply Sat_Cov. assumption.
Qed.

End Scott.

End Scott.

(** Spaces of open sets (using Scott topology *)
Definition Open (A : IGT) : IGT :=
  let LE := @Scott.le_Open (S A) (le A) (Ix A) (C A) in 
  let PreO : PreO.t (le A) := IGT_PreO A in
  let PO := 
   @PO.PreO (Subset (S A)) LE _ (Scott.PO_le_eq (POT := PreO)
  (locT := localized A)) in
  {| S := Subset (S A)
   ; le := LE
   ; PO := PO
   ; Ix := InfoBase.Ix
   ; C := InfoBase.C (leS := LE) (eqS := PO.eq_PreO LE)
   ; localized := InfoBase.loc (PO := PO.fromPreO LE)
   ; pos := InfoBase.Pos (PO := PO.fromPreO LE)
  |}.

Definition open_abstract_mp {Γ A : IGT}
  (f : Cont.map (S (Γ * A)) (S Σ))
     : Cont.map (S Γ) (S (Open A))
  := Scott.absF (leT := le A) (IxT := Ix A) (CT := C A) f.

Existing Instances Bundled.PO Bundled.local.

Definition open_abstract_mp_ok {Γ A : IGT}
  (f : Cont.map (S (Γ * A)) (S Σ))
  : Cont.t (le (Γ * A)) (le Σ) (Cov (Γ * A)) (Cov Σ) f
  -> Cont.t (le Γ) (le (Open A)) (Cov Γ) (Cov (Open A)) 
    (open_abstract_mp f).
Proof.
intros H.
apply Scott.absF_cont. apply H.
Qed.

Definition open_abstract {Γ A : IGT} (f : Γ * A ~~> Σ) : Γ ~~> Open A
  := 
  {| mp := open_abstract_mp (mp f)
   ; mp_ok := open_abstract_mp_ok (mp f) (mp_ok f)
  |}.