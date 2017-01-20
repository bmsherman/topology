Require Import Spec.Category.

Import CMorphisms Category.
Local Open Scope obj.
Local Open Scope morph.

Module Sum.
Section Sum.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Class SumTys : Type :=
  { False : U
  ; sum : U -> U -> U }.

Infix "+" := sum : obj_scope.

Context `{sts : SumTys}.

(** Does sum_elim need to have the context Γ? It seems
    like it may *)
Class SumOps : Type :=
  { False_elim : forall {A}, False ~~> A
  ; inl : forall {A B}, A ~~> A + B
  ; inr : forall {A B}, B ~~> A + B
  ; sum_elim : forall {Γ A B C}, Γ * A ~~> C -> Γ * B ~~> C 
                            -> Γ * (A + B) ~~> C
  ; False_elim_eq : forall {A B} {f g : A ~~> B}, A ~~> False -> f == g                                          
  }.

Context `{sos : SumOps}.

Class SumProps : Type :=
  { False_elim_unique : forall {A} (x y : False ~~> A), x == y
  ; sum_elim_inl : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inl) == f
  ; sum_elim_inr : forall {Γ A B C} (f : Γ * A ~~> C) (g : Γ * B ~~> C),
      sum_elim f g ∘ (id ⊗ inr) == g
  ; sum_determines : forall {Γ A B C} (f f' : Γ * (A + B) ~~> C),
      f ∘ (id ⊗ inl) == f' ∘ (id ⊗ inl) ->  f ∘ (id ⊗ inr) == f' ∘ (id ⊗ inr) -> f == f'
  ; sum_elim_Proper : forall {Γ A B C}, Proper (eq ==> eq ==> eq) (@sum_elim _ Γ A B C)                         
  }.

Definition sum_match {Γ A B C}
  (e : Γ ~~> A + B)
  (l : Γ * A ~~> C) (r : Γ * B ~~> C) : Γ ~~> C :=
  sum_elim l r ∘ ⟨ id , e ⟩.

Definition copair {A B C} : (A ~~> C) -> (B ~~> C) -> (A + B ~~> C) :=
  fun f g =>
    sum_elim (Γ := unit) (f ∘ snd) (g ∘ snd) ∘ add_unit_left.


Definition sum_comm {A B} : A + B ~~> B + A :=
  copair inr inl.
       

Context {sps : SumProps} {cps : CMC_Props U}.

Lemma inj_eq : forall {A B C} (f g : A + B ~~> C), (f ∘ inl == g ∘ inl) -> (f ∘ inr == g ∘ inr) -> f == g.
Proof. intros A B C f g l r.
       eapply (Iso_Epi unit_isom_left). simpl.
       apply sum_determines.
       rewrite <- !compose_assoc.
       rewrite !parallel_snd.
       rewrite !compose_assoc.
       rewrite l. reflexivity.
       rewrite <- !compose_assoc.
       rewrite !parallel_snd.
       rewrite !compose_assoc.
       rewrite r. reflexivity.
Qed.

Lemma sum_elim_duple : forall {Γ A B C : U} (f : Γ ~~> C),
    sum_elim (A:=A) (B:=B) (f ∘ fst) (f ∘ fst) == f ∘ fst.
Proof. intros.
       apply sum_determines.
       - rewrite sum_elim_inl.
         rewrite <- compose_assoc, parallel_fst, compose_id_left.
         reflexivity.
       - rewrite sum_elim_inr.
         rewrite <- compose_assoc, parallel_fst, compose_id_left.
         reflexivity.
Qed.

Lemma copair_inl : forall {A B C :U} {f : A ~~> C} {g : B ~~> C}, copair f g ∘ inl == f.
Proof. intros A B C f g.
       unfold copair. 
       transitivity (sum_elim (f ∘ snd) (g ∘ snd) ∘ (id ⊗ inl) ∘ add_unit_left).
       rewrite <- !compose_assoc; apply compose_Proper; try reflexivity.
       unfold add_unit_left. rewrite parallel_pair, pair_f.
       apply proj_eq; rewrite ?pair_fst, ?pair_snd.
       apply unit_uniq. rewrite compose_id_left, compose_id_right. reflexivity.
       rewrite sum_elim_inl. unfold add_unit_left. rewrite <- compose_assoc.
       rewrite pair_snd. rewrite compose_id_right. reflexivity.
Qed.


Lemma copair_inr : forall {A B C :U} {f : A ~~> C} {g : B ~~> C}, copair f g ∘ inr == g.
Proof. intros A B C f g.
       unfold copair. 
       transitivity (sum_elim (f ∘ snd) (g ∘ snd) ∘ (id ⊗ inr) ∘ add_unit_left).
       rewrite <- !compose_assoc; apply compose_Proper; try reflexivity.
       unfold add_unit_left. rewrite parallel_pair, pair_f.
       apply proj_eq; rewrite ?pair_fst, ?pair_snd.
       apply unit_uniq. rewrite compose_id_left, compose_id_right. reflexivity.
       rewrite sum_elim_inr. unfold add_unit_left. rewrite <- compose_assoc.
       rewrite pair_snd. rewrite compose_id_right. reflexivity.
Qed.

Lemma copair_snd : forall {A B C D : U} {f : A ~~> C * D} {g : B ~~> C * D},
    snd ∘ copair f g == copair (snd ∘ f) (snd ∘ g).
Proof. intros A B C D f g.
       apply inj_eq.
       - rewrite <- compose_assoc, -> !copair_inl. reflexivity.
       - rewrite <- compose_assoc, -> !copair_inr. reflexivity.
Qed.

Lemma copair_Proper : forall {A B C}, Proper (eq ==> eq ==> eq) (copair (A:=A)(B:=B)(C:=C)).
Proof. intros A B C. unfold Proper, respectful. intros x y H x0 y0 H0.
       apply inj_eq; rewrite ?copair_inl; rewrite ?copair_inr; assumption.
Qed.

Definition coparallel : forall {A B C D}, A ~~> B -> C ~~> D -> A + C ~~> B + D :=
  fun _ _ _ _ f g => copair (inl ∘ f) (inr ∘ g).

Lemma coparallel_Proper : forall {A B C D}, Proper (eq ==> eq ==> eq) (@coparallel A B C D).
Proof. intros A B C D.
       unfold Proper, respectful.
       intros x0 y0 H0 x1 y1 H1.
       unfold coparallel.
       apply copair_Proper; apply compose_Proper; try reflexivity; assumption.
Qed.


Lemma coparallel_inl : forall {A B C D} {f : A ~~> B} {g : C ~~> D}, coparallel f g ∘ inl == inl ∘ f.
Proof. intros A B C D f g.
       unfold coparallel. rewrite copair_inl. reflexivity.
Qed.

Lemma coparallel_inr : forall {A B C D} {f : A ~~> B} {g : C ~~> D}, coparallel f g ∘ inr == inr ∘ g.
Proof. intros A B C D f g.
       unfold coparallel. rewrite copair_inr. reflexivity.
Qed.

Lemma copair_coparallel_id : forall {A A' B C} (f : A ~~> A') (f' : A' ~~> B) (g : C ~~> B),
    copair (f' ∘ f) g == copair f' g ∘ coparallel f id.
Proof. intros A A' B C f f' g.
       apply inj_eq.
       - rewrite <- compose_assoc, -> coparallel_inl.
         rewrite -> compose_assoc, -> !copair_inl. reflexivity.
       - rewrite <- compose_assoc, -> coparallel_inr.
         rewrite -> compose_assoc, -> !copair_inr. rewrite compose_id_right. reflexivity.
Qed.

Lemma copair_coparallel : forall {A B C D E} (f : A ~~> B) (g : B ~~> C) (h : D ~~> E) (k : E ~~> C),
    copair (g ∘ f) (k ∘ h) == copair g k ∘ coparallel f h.
Proof. intros A B C D E f g h k.
       apply inj_eq;
         rewrite <- compose_assoc; rewrite ?coparallel_inr, ?coparallel_inl;
           rewrite -> compose_assoc; rewrite ?copair_inl, ?copair_inr; reflexivity.
Qed.


Lemma coparallel_compose : forall {A B C D E F : U} {f : A ~~> B} {g : B ~~> C} {h : D ~~> E} {k : E ~~> F},
    (coparallel g k) ∘ (coparallel f h) == coparallel (g ∘ f) (k ∘ h).
Proof. intros A B C D E F f g h k.
       apply inj_eq.
       - rewrite <- compose_assoc, !coparallel_inl.
         rewrite !compose_assoc, coparallel_inl. reflexivity.
       - rewrite <- compose_assoc, !coparallel_inr.
         rewrite !compose_assoc, coparallel_inr. reflexivity.
Qed.

Definition distrib_left : forall {A B C}, A * (B + C) ~~> A * B + A * C :=
  fun _ _ _ => sum_elim inl inr.
Definition undistrib_left : forall {A B C}, A * B + A * C ~~> A * (B + C) :=
  fun _ _ _ => copair (id ⊗ inl) (id ⊗ inr).

Lemma copair_fst : forall {A B C D} (f : A ~~> C * D) (g : B ~~> C * D),
    fst ∘ copair f g == copair (fst ∘ f) (fst ∘ g).
Proof.
  intros.
  apply inj_eq.
  - rewrite <- compose_assoc; rewrite !copair_inl. reflexivity.
  - rewrite <- compose_assoc; rewrite !copair_inr. reflexivity.
Qed.

Definition distrib_Iso_left : forall {A B C}, A * (B + C) ≅ A * B + A * C.
Proof.
  intros. unshelve eapply Build_Iso. apply distrib_left. apply undistrib_left.
  - apply inj_eq.
    + rewrite <- compose_assoc; unfold undistrib_left.
      rewrite copair_inl; unfold distrib_left.
      rewrite sum_elim_inl. rewrite compose_id_left. reflexivity.
    + rewrite <- compose_assoc; unfold undistrib_left.
      rewrite copair_inr; unfold distrib_left.
      rewrite sum_elim_inr. rewrite compose_id_left. reflexivity.
  - apply sum_determines.
    + rewrite <- compose_assoc; unfold distrib_left.
      rewrite sum_elim_inl; unfold undistrib_left.
      rewrite copair_inl. rewrite compose_id_left. reflexivity.
    + rewrite <- compose_assoc; unfold distrib_left.
      rewrite sum_elim_inr; unfold undistrib_left.
      rewrite copair_inr. rewrite compose_id_left. reflexivity.
Defined.

Definition Iso_Sum : forall {A A' B B'}, A ≅ A' -> B ≅ B' -> A + B ≅ A' + B'.
Proof.
  intros A A' B B' s t.
  unshelve eapply Build_Iso; try eapply coparallel.
  exact (to s). exact (to t). exact (from s). exact (from t).
  apply inj_eq.
  rewrite <- compose_assoc, -> coparallel_inl, -> compose_assoc, -> coparallel_inl.
  rewrite compose_id_left, <- compose_assoc.
  rewrite (to_from s), compose_id_right. reflexivity.
  rewrite <- compose_assoc, -> coparallel_inr, -> compose_assoc, -> coparallel_inr.
  rewrite compose_id_left, <- compose_assoc.
  rewrite (to_from t), compose_id_right. reflexivity.
  apply inj_eq.
  rewrite <- compose_assoc, -> coparallel_inl, -> compose_assoc, -> coparallel_inl.
  rewrite compose_id_left, <- compose_assoc.
  rewrite (from_to s), compose_id_right. reflexivity.
  rewrite <- compose_assoc, -> coparallel_inr, -> compose_assoc, -> coparallel_inr.
  rewrite compose_id_left, <- compose_assoc.
  rewrite (from_to t), compose_id_right. reflexivity.
Defined.

Lemma copair_distrib_elim : forall {Γ A B C} {f : Γ * A ~~> C}{g : Γ * B ~~> C},
    copair f g ∘ (sum_elim (Γ:=Γ)(A:=A)(B:=B) inl inr) == sum_elim f g.
Proof. intros Γ A B C f g.
       apply sum_determines.
       - rewrite <- compose_assoc, -> !sum_elim_inl. apply copair_inl.
       - rewrite <- compose_assoc, -> !sum_elim_inr. apply copair_inr.
Qed.

  
End Sum.

Infix "+" := sum : obj_scope.
End Sum.