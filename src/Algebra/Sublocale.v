Require Import
  Algebra.FrameC
  Algebra.OrderC
  CMorphisms.

Set Universe Polymorphism.
Local Open Scope Frame.

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

Lemma incl_cont : Frame.morph OA OpsAj (fun a => a).
Proof.
unshelve eapply Frame.morph_easy.
- unfold Proper, respectful. simpl. intros.
  rewrite X. reflexivity.
- reflexivity.
- intros. simpl. rewrite j_idem_eq. reflexivity.
- simpl. intros. rewrite j_idem_eq. reflexivity.
Qed. 

End Nucleus.

Section OpenSub.

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

Definition OpenSubOps : @Frame.Ops A :=
  OpsAj Vimpl.

Instance OpenSubFrame : Frame.t OpenSubOps.
Proof.
  apply FrameJ. apply Vimpl_nucleus.
Qed.

Lemma open_incl_cont : Frame.morph OA OpenSubOps (fun a => a).
Proof.
apply incl_cont. apply Vimpl_nucleus.
Qed.

End OpenSub.




Section Pattern.

Context {A : Type} {OA : @Frame.Ops A} {FA : Frame.t OA}
        {B : Type} {OB : @Frame.Ops B} {FB : Frame.t OB}.

Variable Ix : Type.
Variable V : Ix -> A.
Variable Vimpl : Ix -> A -> A.
Variable Vimpl_ok : forall (i : Ix) (U : A), is_implies (V i) U (Vimpl i U).
Variable f : Ix -> B -> A.
Variable f_cont : forall i : Ix, Frame.morph OB (OpenSubOps (Vimpl i)) (f i).

Definition f' (i : Ix) (b : B) : A := f i b ∧ V i.

Definition union_f (b : B) : A := Frame.sup (fun i => f' i b).

Hypothesis covering : Frame.top <= union_f Frame.top.

Definition VVimpl (i j : Ix) (U : A) : A :=
  Vimpl i (Vimpl j U).

(** This is copied. I should put it somewhere good. *)
Instance min_mono2 {Z} `{Frame.t Z} : Proper (L.le ==> L.le ==> L.le) L.min.
Proof.
unfold Proper, respectful.
intros. apply L.min_ok. rewrite <- X. apply L.min_ok.
rewrite <- X0. apply L.min_ok.
Qed.

Lemma VVimpl_ok : forall (i j : Ix) (U : A),
  is_implies (V i ∧ V j) U (VVimpl i j U).
Proof.
unfold is_implies, VVimpl in *. intros.
split; intros.
- do 2 apply Vimpl_ok in X. rewrite X.
Admitted.

Variable glue_f : Ix -> Ix -> B -> A.
Variable glue_f_cont : forall i j : Ix, 
  Frame.morph OB (OpenSubOps (VVimpl i j)) (glue_f i j).

(** Need to talk about inclusions of open subspaces into other
    open subspaces to state gluing. Also specialization preorders would
    be nice. *)
Hypothesis gluing : forall i j : Ix, True.

End Pattern.