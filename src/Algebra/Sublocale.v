Require Import
  Algebra.FrameC
  Algebra.OrderC
  CMorphisms.

Set Universe Polymorphism.
Local Open Scope Frame.

Section Congruence.
Context {A : Type} {OA : @Frame.Ops A} {FA : Frame.t OA}
        {B : Type} {OB : @Frame.Ops B} {FB : Frame.t OB}.

Variable f : A -> B.
Hypothesis f_L : L.morph (Frame.LOps (Ops := OA)) (Frame.LOps (Ops := OB)) f.
Hypothesis f_sup : forall (Ix : Type) (g : Ix -> A),
  f (Frame.sup g) == Frame.sup (fun i => f (g i)).

Definition LOpsA' : L.Ops A :=
  {| L.le := fun U V => f U <= f V
   ; L.eq :=  fun U V => f U == f V
   ; L.min := fun U V => U ∧ V
   ; L.max := fun U V => U ∨ V
  |}.

Definition OpsA' : @Frame.Ops A := 
  {| Frame.LOps := LOpsA'
  ; Frame.top := Frame.top
  ; Frame.sup := fun Ix f => Frame.sup f
  |}.

Lemma eq_le (x y : B) : x == y -> x <= y.
Proof.
  intros. rewrite X. reflexivity.
Qed.

Lemma LatticeC : L.t _ LOpsA'.
Proof.
econstructor.
- constructor.
  + constructor. intros. simpl.
    reflexivity. simpl. intros. etransitivity; eassumption.
  + unfold Proper, respectful. simpl.
    intros. rewrite X, X0. reflexivity.
  + simpl. intros. apply PO.le_antisym; assumption.
- unfold Proper, respectful. simpl. intros.
  transitivity (f x ∨ f x0).
  apply f_L. transitivity (f y ∨ f y0).
  rewrite X, X0. reflexivity.
  symmetry. apply f_L.
- simpl. intros. econstructor.
  + transitivity (f l ∨ f r). apply L.max_ok.
    apply eq_le. symmetry. apply f_L.
  + transitivity (f l ∨ f r). apply L.max_ok.
    apply eq_le. symmetry. apply f_L.
  + intros. transitivity (f l ∨ f r).
    apply eq_le. apply f_L.
    apply L.max_ok; assumption.
- unfold Proper, respectful. simpl. intros.
  transitivity (f x ∧ f x0).
  apply f_L. transitivity (f y ∧ f y0).
  rewrite X, X0. reflexivity. symmetry. apply f_L.
- intros. econstructor.
  + simpl. transitivity (f l ∧ f r).
    apply eq_le. apply f_L. apply L.min_ok.
  + simpl. transitivity (f l ∧ f r).
    apply eq_le. apply f_L. apply L.min_ok.
  + simpl. intros. transitivity (f l ∧ f r).
    apply L.min_ok; assumption. apply eq_le. 
    symmetry. apply f_L.
Qed.

Instance FrameC : Frame.t OpsA'.
Proof.
econstructor.
- apply LatticeC.
- unfold PreO.top. intros. simpl. apply f_L. apply Frame.top_ok.
- unfold Proper, pointwise_relation, respectful. simpl.
  intros. transitivity (Frame.sup (fun i => f (x i))). 
  apply f_sup. transitivity (Frame.sup (fun i => f (y i))).
  apply Frame.sup_proper. unfold pointwise_relation.
  assumption. symmetry. apply f_sup.
- intros. econstructor.
  + intros. simpl. apply f_L. apply Frame.sup_ok.
  + simpl. intros. transitivity (Frame.sup (fun i => f (f0 i))).
    apply eq_le. apply f_sup. apply Frame.sup_ok.
    assumption.
- simpl. intros. apply f_L. apply Frame.sup_distr.
Qed.

Lemma incl_cont : Frame.morph OA OpsA' (fun a => a).
Proof.
unshelve eapply Frame.morph_easy.
- unfold Proper, respectful. simpl. intros.
  apply f_L. assumption.
- reflexivity.
- intros. simpl. apply f_L. reflexivity.
- simpl. intros. apply f_L. reflexivity.
Qed. 

End Congruence.

Section Nucleus.

Context {A : Type} `{FA : Frame.t A}.

Variable j : A -> A.

Class nucleus : Type :=
  { j_Proper : Proper (L.eq ==> L.eq) j 
  ; j_meet : forall U V : A, j (U ∧ V) == j U ∧ j V 
  ; j_mono : forall U, U <= j U
  ; j_idempotent : forall U, j (j U) <= j U }.

Instance j_ProperI `{nucleus} : Proper (L.eq ==> L.eq) j.
Proof. apply j_Proper. Qed.

Hypothesis j_nucleus : nucleus.

Definition LOpsAj : L.Ops A :=
  {| L.le := fun U V => j U <= j V
   ; L.eq :=  fun U V => j U == j V
   ; L.min := fun U V => j (U ∧ V)
   ; L.max := fun U V => j (U ∨ V)
  |}.

Definition OpsAj : @Frame.Ops A := 
  {| Frame.LOps := LOpsAj
  ; Frame.top := Frame.top
  ; Frame.sup := fun Ix f => j (Frame.sup f)
  |}.

Lemma j_top : j Frame.top == Frame.top.
Proof.
apply PO.le_antisym. apply Frame.top_ok.
apply j_mono.
Qed.

Lemma j_mono2 (U V : A) : U <= V -> j U <= j V.
Proof.
intros H. apply Frame.le_min. apply Frame.le_min in H.
rewrite <- j_meet. rewrite H. reflexivity.
Qed.

Lemma j_idem_eq (U : A) : j (j U) == j U.
Proof.
apply PO.le_antisym. apply j_idempotent. apply j_mono.
Qed.

Lemma j_join_le (x y x' y' : A) : j x <= j y
  -> j x' <= j y' -> j (j (x ∨ x')) <= j (j (y ∨ y')).
Proof.
intros. rewrite j_idempotent.
apply j_mono2. apply L.max_ok. rewrite j_mono.
rewrite X. apply j_mono2. apply L.max_ok.
rewrite j_mono. rewrite X0. apply j_mono2. apply L.max_ok.
Qed.

Lemma j_sup_le {Ix : Type} (f f' : Ix -> A) :
  (forall i, j (f i) <= j (f' i)) -> 
  j (j (Frame.sup f)) <= j (j (Frame.sup f')).
Proof.
intros. rewrite j_idempotent. apply j_mono2.
apply Frame.sup_ok. intros. rewrite j_mono.
rewrite X. apply j_mono2. apply Frame.sup_ok.
Qed.

Lemma max_idempotent (x : A) : x ∨ x == x.
Proof.
apply PO.le_antisym; apply L.max_ok; reflexivity.
Qed.

Lemma LatticeJ : L.t _ LOpsAj.
Proof.
econstructor.
- constructor.
  + constructor. intros. simpl.
    reflexivity. simpl. intros. etransitivity; eassumption.
  + unfold Proper, respectful. simpl.
    intros. rewrite X, X0. reflexivity.
  + simpl. intros. apply PO.le_antisym; assumption.
- unfold Proper, respectful. simpl. intros. 
  apply PO.le_antisym; apply j_join_le.
  rewrite X; reflexivity. rewrite X0. reflexivity.
  rewrite <- X. reflexivity. rewrite <- X0. reflexivity.
- simpl. intros. econstructor.
  + apply j_mono2. rewrite <- j_mono. apply L.max_ok.
  + apply j_mono2. rewrite <- j_mono. apply L.max_ok.
  + intros. rewrite j_join_le; try eassumption.
    rewrite max_idempotent. apply j_idempotent.
- unfold Proper, respectful. simpl. intros.
  apply j_Proper. rewrite !j_meet. apply L.min_proper; assumption.
- simpl. intros. econstructor.
  + rewrite j_idempotent. apply j_mono2. apply L.min_ok.
  + rewrite j_idempotent. apply j_mono2. apply L.min_ok.
  + intros. rewrite !j_meet, !j_idem_eq. apply L.min_ok; assumption.
Qed.

Instance FrameJ : Frame.t OpsAj.
Proof.
econstructor.
- apply LatticeJ.
- unfold PreO.top. intros. simpl. apply j_mono2. apply Frame.top_ok.
- unfold Proper, pointwise_relation, respectful. simpl.
  intros. apply PO.le_antisym; apply j_sup_le; intros; 
    rewrite X; reflexivity.
- simpl. intros. econstructor.
  + intros. apply j_mono2. rewrite j_mono. apply j_mono2.
    apply Frame.sup_ok.
  + intros. rewrite j_sup_le. Focus 2. intros.
    apply X. rewrite j_idem_eq. apply j_mono2.
    apply Frame.sup_ok. intros. reflexivity.
- simpl. intros. rewrite j_meet.
  apply PO.le_antisym.
  + rewrite <- j_meet. rewrite j_idem_eq. apply j_mono2.
    transitivity (j (Frame.sup (fun i : Ix => j x ∧ j (f i)))).
    rewrite <- Frame.sup_distr. rewrite j_meet.
    apply L.min_ok. rewrite j_idem_eq.
    transitivity x. apply L.min_ok. apply j_mono.
    transitivity (j (Frame.sup f)). apply L.min_ok.
    apply j_mono2. apply Frame.sup_ok. intros.
    transitivity (j (f i)). apply j_mono.
    apply (Frame.sup_ok (fun i0 : Ix => j (f i0))).
    apply j_mono2. apply Frame.sup_ok. intros.
    rewrite <- j_meet. 
    pose proof (Frame.sup_ok (fun i0 : Ix => j (x ∧ f i0))).
    apply X.
  + rewrite j_idem_eq. apply j_mono2. apply L.min_ok.
    * apply Frame.sup_ok. intros. rewrite j_meet. apply L.min_ok.
    * apply Frame.sup_ok. intros. apply j_mono2.
      transitivity (j (f i)). transitivity (f i). apply L.min_ok.
      apply j_mono. apply j_mono2. apply Frame.sup_ok.
Qed.

Lemma incl_contN : Frame.morph OA OpsAj (fun a => a).
Proof.
unshelve eapply Frame.morph_easy.
- unfold Proper, respectful. simpl. intros.
  rewrite X. reflexivity.
- reflexivity.
- intros. simpl. rewrite j_idem_eq. reflexivity.
- simpl. intros. rewrite j_idem_eq. reflexivity.
Qed. 

End Nucleus.

Section OpenSubN.

Context {A : Type} `{FA : Frame.t A}.

(** We need our open [V] defining our subspace to be exponentiable.
    Impredicatively, any frame is a heyting algebra, so all objects
    are exponentiable: just take the supremum of all opens [Γ] such
    that [Γ ∧ U <= V]. But predicatively, we can't do this. But if we
    have access to a set-indexed base, then we can just take the
    supremum over the base. Here we will just assume demand that
    we are given an exponentiable open to define our subspace.
*)

Require Import Algebra.SetsC.
Local Open Scope Subset.

Definition is_implies (U V UV : A) :=
  forall Γ : A, Γ <= UV <--> Γ ∧ U <= V.

Lemma is_implies_unique (U V : A) : forall (UV UV' : A),
  is_implies U V UV -> is_implies U V UV'
  -> UV == UV'.
Proof.
unfold is_implies. intros. apply PO.le_antisym.
- apply (X0 UV). apply X. reflexivity.
- apply (X UV'). apply X0. reflexivity.
Qed.

Instance min_mono : Proper (L.le ==> L.le ==> L.le) L.min.
Proof.
unfold Proper, respectful.
intros. apply L.min_ok. rewrite <- X. apply L.min_ok.
rewrite <- X0. apply L.min_ok.
Qed.

Definition min_comm (U V : A) : U ∧ V == V ∧ U.
Proof.
apply PO.le_antisym; repeat apply L.min_ok.
Qed.

Lemma implies_meet (U X Y UX UY UXY : A)
  : is_implies U X UX -> is_implies U Y UY
  -> is_implies U (X ∧ Y) UXY
  -> UXY == UX ∧ UY.
Proof.
unfold is_implies. intros. apply PO.le_antisym.
- apply L.min_ok. 
  + apply X0. transitivity (X ∧ Y).
    apply X2. reflexivity. apply L.min_ok.
  + apply X1. transitivity (X ∧ Y).
    apply X2. reflexivity. apply L.min_ok.
- apply X2. apply L.min_ok.
  + transitivity (UX ∧ U). apply min_mono.
    apply L.min_ok. reflexivity. apply X0. reflexivity.
  + transitivity (UY ∧ U). apply min_mono.
    apply L.min_ok. reflexivity. apply X1. reflexivity.
Qed.

Lemma impl_apply_le (x a b xa xb : A) :
  is_implies x a xa -> is_implies x b xb
  -> xa <= xb -> a ∧ x <= b ∧ x.
Proof.
intros. unfold is_implies in *.
apply L.min_ok. apply X0. rewrite <- X1. apply X.
  apply L.min_ok. apply L.min_ok.
Qed.

Lemma impl_apply (x a b xa xb : A) :
  is_implies x a xa -> is_implies x b xb
  -> xa == xb -> a ∧ x == b ∧ x.
Proof.
intros. apply PO.le_antisym; eapply impl_apply_le;
  try eassumption. rewrite X1. reflexivity.
rewrite <- X1. reflexivity.
Qed.

Instance is_implies_Proper : Proper (L.eq ==> L.eq ==> L.eq ==> arrow) is_implies.
Proof.
unfold Proper, respectful, arrow, is_implies.
intros. rewrite <- X1, <- X0, <- X. apply X2.
Qed.

Variable V : A.
Variable Vimpl : A -> A.
Hypothesis Vimpl_ok : forall U, is_implies V U (Vimpl U).

Instance Vimpl_Proper : Proper (L.eq ==> L.eq) Vimpl.
Proof.
unfold Proper, respectful. intros.
eapply is_implies_unique. apply Vimpl_ok.
rewrite X. apply Vimpl_ok.
Qed.

Theorem Vimpl_nucleus : nucleus Vimpl.
Proof.
econstructor.
- apply Vimpl_Proper.
- intros. eapply implies_meet; apply Vimpl_ok.
- unfold is_implies in Vimpl_ok.
  intros. apply Vimpl_ok. apply L.min_ok.
- intros. apply Vimpl_ok.
  transitivity (Vimpl U ∧ V). apply L.min_ok.
  apply (Vimpl_ok (Vimpl U) (Vimpl (Vimpl U))).
  reflexivity. apply L.min_ok. apply Vimpl_ok. reflexivity.
Qed.

Definition OpenSubOpsN : @Frame.Ops A :=
  OpsAj Vimpl.

Instance OpenSubFrameN : Frame.t OpenSubOpsN.
Proof.
  apply FrameJ. apply Vimpl_nucleus.
Qed.

Lemma open_incl_contN : Frame.morph OA OpenSubOpsN (fun a => a).
Proof.
apply incl_contN. apply Vimpl_nucleus.
Qed.

End OpenSubN.




Section OpenSub.

Context {A : Type} `{FA : Frame.t A}.

Require Import Algebra.SetsC.
Local Open Scope Subset.

Variable V : A.

Definition intV (U : A) := U ∧ V.

Lemma min_distr1 (a b c : A) :
  (a ∧ b) ∧ c == (a ∧ c) ∧ (b ∧ c).
Proof.
apply PO.le_antisym.
- repeat apply L.min_ok.
  transitivity (a ∧ b); apply L.min_ok.
  transitivity (a ∧ b); apply L.min_ok.
- repeat apply L.min_ok. transitivity (a ∧ c);
  apply L.min_ok. transitivity (b ∧ c); apply L.min_ok.
  transitivity (b ∧ c); apply L.min_ok.
Qed.

Lemma intV_L : L.morph Frame.LOps Frame.LOps intV.
Proof.
unfold intV. econstructor.
- econstructor.
  + unfold PreO.morph. intros. apply min_mono.
    assumption. reflexivity.
  + unfold Proper, respectful. intros. rewrite X. reflexivity.
- intros. rewrite !Frame.max_sup. 
  rewrite min_comm. rewrite Frame.sup_distr.
  apply Frame.sup_proper. unfold pointwise_relation.
  intros. rewrite min_comm. destruct a0; reflexivity.
- intros. apply min_distr1.
Qed.

Lemma intV_sup : forall Ix (g : Ix -> A),
  intV (Frame.sup g) == Frame.sup (fun i => intV (g i)).
Proof.
unfold intV. intros. rewrite min_comm.
rewrite Frame.sup_distr. apply Frame.sup_proper.
unfold pointwise_relation; intros.
apply min_comm.
Qed.

Definition OpenSubOps : @Frame.Ops A := OpsA' intV.

Instance OpenSubFrame : Frame.t OpenSubOps.
Proof.
  apply FrameC. apply intV_L. apply intV_sup.
Qed.

Lemma open_incl_cont : Frame.morph OA OpenSubOps (fun a => a).
Proof.
apply incl_cont. apply intV_L. apply intV_sup.
Qed.

End OpenSub.




Section Pattern.

Context {A : Type} {OA : @Frame.Ops A} {FA : Frame.t OA}
        {B : Type} {OB : @Frame.Ops B} {FB : Frame.t OB}.


Variable Ix : Type.
Variable V : Ix -> A.
Variable f : Ix -> B -> A.
Variable f_cont : forall i : Ix, Frame.morph OB (OpenSubOps (V i)) (f i).

Definition f' (i : Ix) (b : B) : A := intV (V i) (f i b).

Definition union_f (b : B) : A := Frame.sup (fun i => f' i b).

Hypothesis covering : Frame.top <= union_f Frame.top.

(** This is copied. I should put it somewhere good. *)
Instance min_mono2 {Z} `{Frame.t Z} : Proper (L.le ==> L.le ==> L.le) L.min.
Proof.
unfold Proper, respectful.
intros. apply L.min_ok. rewrite <- X. apply L.min_ok.
rewrite <- X0. apply L.min_ok.
Qed.


Instance max_mono {Z} `{Frame.t Z} : Proper (L.le ==> L.le ==> L.le) L.max.
Proof.
unfold Proper, respectful.
intros. apply L.max_ok. rewrite X. apply L.max_ok.
rewrite X0. apply L.max_ok.
Qed.

Lemma f'_mono (i : Ix) (b b' : B) :
  b <= b' -> f' i b <= f' i b'.
Proof.
intros. unfold f'.
apply (f_cont i). assumption.
Qed.

Variable glue_f : Ix -> Ix -> B -> A.
Variable glue_f_cont : forall i j : Ix, 
  Frame.morph OB (OpenSubOps (V i ∧ V j)) (glue_f i j).

Definition union_f2 (b : B) : A :=
  Frame.sup (fun p : (Ix * Ix) => let (i, j) := p in 
  intV (V i ∧ V j) (glue_f i j b)).

Lemma min_idempotent (x : A) : x ∧ x == x.
Proof.
apply PO.le_antisym; apply L.min_ok; reflexivity.
Qed.


(** Need to talk about inclusions of open subspaces into other
    open subspaces to state gluing. Also specialization preorders would
    be nice. *)
Hypothesis gluing : forall i j : Ix, 
  let Vij := V i ∧ V j in
  forall b : B, PreO.max (le := L.le (Ops := @Frame.LOps _ OA)) (f i b ∧ Vij) (f j b ∧ Vij) (glue_f i j b ∧ Vij).

Lemma union_f_same (b : B) :
  union_f b == union_f2 b.
Proof.
unfold union_f, union_f2.
apply PO.le_antisym.
- apply Frame.sup_ok. intros.
  etransitivity. Focus 2. 
  apply (Frame.sup_ok (Ix := Ix * Ix)).
  instantiate (1 := (i, i)).
  simpl. unfold f', intV.
  rewrite min_idempotent.
  pose proof (gluing i i).
  simpl in X. specialize (X b).
  apply PreO.max_l in X.
  rewrite !min_idempotent in X.
  assumption.
- apply Frame.sup_ok. intros. destruct i.
  rewrite <- (max_idempotent (Frame.sup (fun i1 : Ix => f' i1 b))).
  etransitivity. Focus 2.
  apply max_mono.
  unshelve apply Frame.sup_ok. exact i.
  unshelve apply Frame.sup_ok. exact i0.
  unfold f'.
  pose proof (gluing i i0).
  simpl in X. specialize (X b).
  destruct X. clear max_l max_r.
  etransitivity. apply max_least. 3:reflexivity.
  transitivity (f i b ∧ V i).
  apply min_mono. reflexivity. apply L.min_ok.
  apply L.max_ok.
  transitivity (f i0 b ∧ V i0).
  apply min_mono. reflexivity. apply L.min_ok.
  apply L.max_ok.
Qed.

Existing Instances Frame.f_eq L.min_proper.

Theorem pattern : Frame.morph OB OA union_f.
Proof.
apply Frame.morph_easy.
- unfold Proper, respectful, union_f. intros.
  apply Frame.sup_proper. unfold pointwise_relation. intros.
  unfold f'. apply (f_cont a). assumption.
- apply PO.le_antisym. apply Frame.top_ok.
  apply covering.
- intros. apply PO.le_antisym.
  + unfold union_f. apply L.min_ok.
  apply Frame.sup_pointwise. intros i.
  exists i. apply f'_mono. apply L.min_ok.
  apply Frame.sup_pointwise. intros i.
  exists i. apply f'_mono. apply L.min_ok.
  + rewrite (union_f_same (U ∧ V0)).
    unfold union_f, union_f2.
    rewrite Frame.sup_distr. apply Frame.sup_ok.
    intros i. rewrite min_comm. 
    rewrite Frame.sup_distr. apply Frame.sup_ok.
    intros j. etransitivity.
    Focus 2. apply (Frame.sup_ok (Ix := Ix * Ix)).
    instantiate (1 := (i, j)).
    simpl.
    pose proof (gluing i j) as glue. simpl in glue.
    unfold f'.
    transitivity ((f i V0 ∧ f j U) ∧ (V i ∧ V j)).
    apply L.min_ok. apply L.min_ok.
    transitivity (f i V0 ∧ V i). apply L.min_ok.
    apply L.min_ok.
    transitivity (f j U ∧ V j).
    apply L.min_ok. apply L.min_ok.
    apply L.min_ok.
    transitivity (f i V0 ∧ V i). apply L.min_ok.
    apply L.min_ok. transitivity (f j U ∧ V j).
    apply L.min_ok. apply L.min_ok.
    rewrite (min_comm (f i V0) (f j U)).
    destruct (glue V0). clear max_least max_r.
    destruct (glue U). clear max_l0 max_least.
    pose proof (glue_f_cont i j) as H.
    destruct H.
    destruct f_L. simpl in f_min.
    specialize (f_min U V0).
    unfold intV.
    unfold intV in f_min. rewrite f_min.
    rewrite (min_distr1 (f j U)).
    rewrite (min_distr1 (glue_f i j U)).
    apply min_mono. apply max_r. apply max_l.
- intros. unfold union_f. apply PO.le_antisym.
  apply Frame.sup_ok. intros. 
  unfold f'.
  pose proof (Frame.f_sup (f_cont i) g).
  simpl in X.
  rewrite X. unfold intV.
  rewrite min_comm. rewrite Frame.sup_distr. 
  apply Frame.sup_pointwise. intros.
  exists i0. rewrite min_comm.
  eapply (PreO.sup_ge (fun i1 : Ix => f i1 (g i0) ∧ V i1) _ (Frame.sup_ok (fun i1 : Ix => f i1 (g i0) ∧ V i1)) i).
  apply Frame.sup_ok. intros. apply Frame.sup_pointwise.
  intros.  exists i0. unfold f'.
  pose proof (PO.f_PreO (L.f_PO (Frame.f_L (f_cont i0)))) as X.
  unfold PreO.morph in X. simpl in X.
  apply X. apply Frame.sup_ok.
Qed.

End Pattern.