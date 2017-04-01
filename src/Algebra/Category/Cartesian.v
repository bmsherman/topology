Require Import 
  CMorphisms
  Types.Setoid
  Algebra.Category.

Set Universe Polymorphism. 

Local Open Scope obj.
Local Open Scope morph.
Local Open Scope setoid.

Class Cartesian {U : Category} : Type :=
  { unit : U
  ; BProd : U -> U -> U
  ; unit_Is_Terminal : Is_Terminal_Object unit
  ; BProd_Is_Binary_Product : 
     forall A B, Is_Binary_Product A B (BProd A B)
  }.

Arguments Cartesian : clear implicits.

Infix "*" := BProd : obj_scope.

Section CartesianOps.
Context {U} {CU : Cartesian U}.

Definition tt {Γ} : Γ ~~> unit.
Proof.
pose proof (Product_least (unit_Is_Terminal)).
specialize (X Γ (Empty_set_rect _)).
apply X.
Defined.

Definition fst {A B} : A * B ~~> A
  := (Product_proj (BProd_Is_Binary_Product A B) true).

Definition snd {A B} : A * B ~~> B
  := (Product_proj (BProd_Is_Binary_Product A B) false).

Definition pair {Γ A B : U} (f : Γ ~~> A) (g : Γ ~~> B)
  : Γ ~~> A * B.
Proof.
pose proof (Product_least 
  (BProd_Is_Binary_Product A B) Γ). 
simpl in X.
specialize (X (fun b : bool => match b as b' return 
   Γ ~~> (if b' then A else B) with
  | true => f
  | false => g
  end)).
simpl in X.
apply X.
Defined.


Global Instance pair_Proper {Γ A B : U} 
 : Proper (seq _ ==> seq _ ==> seq _)%signature 
     (@pair Γ A B).
Proof.
Admitted.

End CartesianOps.

Notation "⟨ f , g ⟩" := (pair f g) : morph_scope.

Section MoreCartesianOps.
Context {U} {CU : Cartesian U}.

Lemma pair_fst : forall {A B C} (f : A ~~> B) (g : A ~~> C), fst ∘ ⟨f, g⟩ == f.
Proof.
Admitted.

Lemma pair_snd : forall {A B C} (f : A ~~> B) (g : A ~~> C), snd ∘ ⟨f, g⟩ == g.
Proof.
Admitted.

Lemma unit_uniq : forall {A} (h k : A ~~> unit), h == k.
Proof.
Admitted.

Definition parallel {A B C D : U} 
  (f : A ~~> B) (g : C ~~> D) : A * C ~~> B * D :=
  ⟨ f ∘ fst , g ∘ snd ⟩.

Local Infix "⊗" := parallel (at level 25) : morph_scope.

Definition add_unit_left {A : U} : A ~~> unit * A
  := ⟨tt, id⟩.

Definition add_unit_right {A : U} : A ~~> A * unit
  := ⟨id, tt⟩.

Definition prod_assoc_left {A B C : U} 
  : A * (B * C) ~~> (A * B) * C := 
  ⟨id ⊗ fst, snd ∘ snd⟩.

Definition prod_assoc_right {A B C : U} 
  : (A * B) * C ~~> A * (B * C) := 
  ⟨fst ∘ fst, snd ⊗ id⟩.

Lemma pair_uniq : forall {A B C} (h : A ~~> B * C), h == ⟨fst ∘ h, snd ∘ h⟩.
Proof.
Admitted.

Theorem proj_eq : forall {A B C : U} {f f' : A ~~> B * C},
      (fst ∘ f) == (fst ∘ f') -> (snd ∘ f == snd ∘ f') -> f == f'.
Proof. 
intros A B C f f' Hfst Hsnd. 
rewrite (pair_uniq f). rewrite (pair_uniq f').
rewrite Hfst, Hsnd. reflexivity.
Defined.

Lemma pair_f : forall {A B C D : U} (f : A ~~> B) (h : B ~~> C) (k : B ~~> D),
  ⟨h, k⟩ ∘ f == ⟨h ∘ f, k ∘ f⟩.
Proof. 
intros A B C D f h k. apply proj_eq.
- rewrite pair_fst, compose_assoc, pair_fst. reflexivity.
- rewrite pair_snd, compose_assoc, pair_snd. reflexivity.
Defined.

Lemma parallel_compose {A B C A' B' C'} 
      (f' : A ~~> B) (f : B ~~> C) (g' : A' ~~> B') (g : B' ~~> C') :
  f ⊗ g ∘ f' ⊗ g' == (f ∘ f') ⊗ (g ∘ g').
Proof.
unfold parallel. rewrite pair_f.
apply pair_Proper; rewrite <- !compose_assoc;
  (apply compose_Proper; [ reflexivity |]).
rewrite pair_fst. reflexivity.
rewrite pair_snd. reflexivity.
Qed.

Theorem unit_isom_left : forall {A : U}, (unit * A) ≅ A.
Proof. 
intros A. unshelve eapply 
                   (Build_Iso (unit * A) A snd ⟨tt, id⟩ _ _).
- rewrite pair_snd. reflexivity.
- apply proj_eq.
  + apply unit_uniq.
  + rewrite compose_id_right. rewrite compose_assoc. 
    rewrite pair_snd. rewrite compose_id_left.
    reflexivity.
Defined.

Theorem unit_isom_right : forall {A : U}, (A * unit) ≅ A.
Proof. 
intros A. unshelve eapply 
                   (Build_Iso (A * unit) A fst ⟨id, tt⟩ _ _).
- rewrite pair_fst. reflexivity.
- apply proj_eq.
  + rewrite compose_id_right. rewrite compose_assoc. 
    rewrite pair_fst. rewrite compose_id_left.
    reflexivity.
  + apply unit_uniq.            
Defined.

Lemma pair_id {A B : U} :
  ⟨ fst, snd ⟩ == id (A := A * B).
Proof.
rewrite (pair_uniq id).
rewrite !compose_id_right. reflexivity.
Qed.


Lemma parallel_pair : forall {A B C D E : U} (f : A ~~> B) (g : A ~~> C) (h : B ~~> D) (k : C ~~> E), (h ⊗ k) ∘ ⟨f, g⟩ == ⟨h ∘ f, k ∘ g⟩.
Proof. 
intros A B C D E f g h k.
unfold parallel. apply proj_eq.
- rewrite compose_assoc. rewrite pair_fst, pair_fst.
  rewrite <- compose_assoc. rewrite pair_fst. reflexivity.
- rewrite compose_assoc. rewrite pair_snd, pair_snd.
  rewrite <- compose_assoc. rewrite pair_snd. reflexivity.
Defined.


Lemma parallel_fst : forall {A B C D : U} (f : A ~~> B) (g : C ~~> D),
  fst ∘ (f ⊗ g) == f ∘ fst. (* Have I already proven this somewhere else maybe? *)
Proof. 
intros A B C D f g.
unfold parallel.
rewrite pair_fst.
reflexivity.
Qed.

Lemma parallel_snd : forall {A B C D : U} (f : A ~~> B) (g : C ~~> D),
  snd ∘ (f ⊗ g) == g ∘ snd.
Proof. 
intros A B C D f g.
unfold parallel.
rewrite pair_snd.
reflexivity.
Qed.

Lemma parallel_id A B
  : id (A := A) ⊗ id (A := B) == id.
Proof.
unfold parallel.  rewrite !compose_id_left.
apply pair_id.
Qed.

Theorem parallel_proper : forall {A B C D} (f f' : A ~~> B) (g g' : C ~~> D),
  f == f' -> g == g' -> parallel f g == parallel f' g'.
Proof. 
intros A B C D f f' g g' ff' gg'.
unfold parallel. rewrite ff', gg'. reflexivity.
Qed.

Definition diagonal {A : U} : A ~~> A * A := ⟨ id , id ⟩.
Definition swap {A B : U} : A * B ~~> B * A := ⟨snd, fst⟩.

Global Instance parallel_Proper : forall A B C D : U,
  Proper (seq (A ~~> B) ==> seq (C ~~> D) ==> seq _) parallel.
Proof. 
intros. unfold Proper, respectful.
intros. apply parallel_proper; assumption.
Qed.

Lemma Iso_Prod {A B A' B'} (a : A ≅ A') (b : B ≅ B')
  : A * B ≅ A' * B'.
Proof.
refine (
    {| to := to a ⊗ to b
       ; from := from a ⊗ from b
    |}
  ); rewrite parallel_compose.
rewrite !to_from. apply parallel_id.
rewrite !from_to. apply parallel_id.
Defined.

End MoreCartesianOps.

Infix "⊗" := parallel (at level 25) : morph_scope.
