Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Stream.
Section Stream.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Context {Stream : U -> U}.

Class StreamOps : Type :=
  { stream : forall {Γ X A}, Γ ~~> X -> X ~~> A * X -> Γ ~~> Stream A
  ; hd : forall {A}, Stream A ~~> A
  ; tl : forall {A}, Stream A ~~> Stream A
  }.

Context `{sps : StreamOps}.  

Fixpoint idx (n : nat) {A} : Stream A ~~> A := match n with
  | 0 => hd
  | S n' => idx n' ∘ tl
  end.

Require Import Morphisms.
Class StreamProps : Prop :=
  { stream_Proper : forall Γ X A, Proper (eq ==> eq ==> eq) (@stream _ Γ X A)
  ; stream_ext1 : forall Γ Δ X A (g : Γ ~~> Δ) (x : Δ ~~> X) (f : X ~~> A * X),
    stream (x ∘ g) f == stream x f ∘ g
  ; stream_hd : forall {Γ X A} (x : Γ ~~> X) (f : X ~~> A * X),
    hd ∘ stream x f == fst ∘ f ∘ x
  ; stream_tl : forall {Γ X A} (x : Γ ~~> X) (f : X ~~> A * X),
    tl ∘ stream x f == stream (snd ∘ f ∘ x) f
(* Is this the best way to state the property about when two streams
   are equal? *)
  ; stream_bisim : forall {Γ A} (x y : Γ ~~> Stream A),
     (forall n, idx n ∘ x == idx n ∘ y) -> x == y
  }.

Require Import Spec.Sum.
Import Sum.

Context {stys : SumTys (U := U)}.
Context {sops : SumOps (U := U)}.

(** Not particularly easy to read... *)
Definition cons {Γ A} (x : Γ ~~> A) (xs : Γ ~~> Stream A)
  : Γ ~~> Stream A :=
  stream ⟨ xs , inl ∘ x ⟩ 
    (sum_elim ⟨ snd      , ⟨ fst      , inr ∘ tt ⟩ ⟩
              ⟨ hd ∘ fst , ⟨ tl ∘ fst , inr ∘ tt ⟩ ⟩).
    
Context {SProps : StreamProps}.
Context {cmcprops : CMC_Props U}.
Context {sumProps : SumProps}.


Theorem cons_Proper : forall {Γ A}, Proper (eq ==> eq ==> eq) (@cons Γ A).
Proof. unfold Proper, respectful.
       intros Γ A x y xy xs ys xsys.
       unfold cons.
       eapply stream_Proper; try reflexivity.
       apply pair_Proper; try assumption.
       apply compose_Proper; try assumption; try reflexivity.
Qed.

Theorem cons_ext : forall {Γ Δ A} (g : Γ ~~> Δ) (x : Δ ~~> A) (xs : Δ ~~> Stream A),
    cons x xs ∘ g == cons (x ∘ g) (xs ∘ g).
Proof. intros Γ Δ A g x xs.
       unfold cons.
       rewrite <- stream_ext1.
       apply stream_Proper; try reflexivity.
       rewrite pair_f. rewrite compose_assoc.
       reflexivity.
Qed.



Theorem cons_hd {Γ A} (x : Γ ~~> A) (xs : Γ ~~> Stream A)
  : hd ∘ cons x xs == x.
Proof.
unfold cons. rewrite stream_hd. 
rewrite <- (compose_id_left xs).
rewrite <- (parallel_pair _ _ id).
rewrite compose_assoc.
rewrite <- (compose_assoc _ _ fst).
rewrite sum_elim_inl. rewrite pair_fst.
rewrite pair_snd. reflexivity.
Qed.

Lemma tt_beta {A B : U} (f : A ~~> B) : tt ∘ f == tt.
Proof.
apply (unit_uniq (tt ∘ f)).
Qed.

Lemma pair_parallel_id {Γ A B C} (f : Γ ~~> A)
  (g : Γ ~~> B) (h : B ~~> C)
  : ⟨ f, h ∘ g ⟩ == (id ⊗ h) ∘ ⟨ f , g ⟩.
Proof.
rewrite <- (compose_id_left f).
rewrite parallel_pair.
rewrite !compose_id_left. reflexivity.
Qed.

(* What a painful proof! *)
Theorem cons_tl {Γ A X} (a : Γ ~~> A) (x : Γ ~~> X) (f : X ~~> A * X)
  : tl ∘ cons a (stream x f) == stream x f.
Proof.
unfold cons. rewrite stream_tl.
apply stream_bisim. intros n.
generalize dependent x. generalize dependent f.
induction n; simpl; intros.
- rewrite !stream_hd.
  rewrite (pair_parallel_id (stream x f)).
  rewrite (compose_assoc _ (id ⊗ inl) _).
  rewrite <- (compose_assoc _ _ snd).
  rewrite sum_elim_inl.
  rewrite pair_snd.
  rewrite <- compose_assoc.
  rewrite (pair_parallel_id fst tt inr) at 2.
  rewrite (compose_assoc _ _ (sum_elim _ _)).
  rewrite (compose_assoc _ (id ⊗ inr)).
  rewrite sum_elim_inr.
  rewrite (compose_assoc ⟨ _, _ ⟩ _ fst).
  rewrite (compose_assoc _ _ fst).
  rewrite pair_fst. 
  rewrite <- (compose_assoc _ _ hd).
  rewrite pair_fst. rewrite <- (compose_assoc _ _ hd).
  rewrite pair_fst. rewrite stream_hd.
  reflexivity.
- rewrite <- !(compose_assoc _ _ (idx _)).
  rewrite !stream_tl.
  rewrite <- IHn. apply compose_Proper. reflexivity.
  apply stream_Proper; try reflexivity.
  rewrite (pair_parallel_id (stream x f)).
  rewrite (compose_assoc _ (id ⊗ inl) _).
  rewrite <- (compose_assoc (id ⊗ inl)). 
  rewrite sum_elim_inl.
  rewrite pair_snd.
  rewrite (pair_parallel_id (stream _ f)).
  rewrite (compose_assoc _ (id ⊗ inl)).
  rewrite <- !(compose_assoc _ _ snd).
  rewrite sum_elim_inl.
  rewrite (pair_parallel_id fst tt inr) at 2.
  rewrite <- (compose_assoc _ _ (id ⊗ inr)).
  rewrite (compose_assoc _ _ (sum_elim _ _)).
  rewrite sum_elim_inr.
  rewrite !(compose_assoc _ _ snd).
  rewrite !pair_snd.
  rewrite !pair_f.
  apply pair_Proper. rewrite !pair_fst.
  rewrite <- (compose_assoc _ _ tl).
  rewrite pair_fst. rewrite stream_tl. reflexivity.
  rewrite <- !(compose_assoc _ tt).
  rewrite !tt_beta. reflexivity.
Qed.

Theorem stream_uniq : forall {Γ A} (xs : Γ ~~> Stream A),
    xs == stream (X := Stream A) xs ⟨hd, tl⟩.
Proof. intros Γ A xs. apply stream_bisim.
       intros n. generalize dependent A. generalize dependent Γ.
       induction n.
       - intros Γ A xs.
         simpl.
         rewrite stream_hd, pair_fst.
         reflexivity.
       - intros Γ A xs.
         simpl. rewrite <- !compose_assoc.
         rewrite stream_tl.
         assert (stream (snd ∘ ⟨ hd, tl ⟩ ∘ xs) ⟨ hd, tl ⟩ == stream (tl ∘ xs) ⟨hd, tl⟩) as H.
         {
           apply stream_Proper; try reflexivity.
           rewrite pair_snd; reflexivity.
         }
         rewrite H.
         apply IHn.
Qed.




Theorem cons_tl' : forall {Γ A} (a : Γ ~~> A) (aa : Γ ~~> Stream A), (tl ∘ (cons a aa)) == aa.
Proof. intros Γ A a aa.
       assert (cons a aa == cons a (stream aa ⟨hd, tl⟩)) as should_be_obvious.
       {
         apply cons_Proper; try reflexivity.
         apply stream_uniq.
       }
       rewrite should_be_obvious.
       rewrite cons_tl.
       symmetry. apply stream_uniq.
Qed.

Theorem stream_ext2 :  forall Γ X X' A (g : X ~~> X') (x : Γ ~~> X) (f : X ~~> A * X) (f' : X' ~~> A * X'),
    f' ∘ g == (id ⊗ g) ∘ f -> stream x f == stream (g ∘ x) f'.
Proof. intros Γ X X' A g x f f' f'g_gf.
       apply stream_bisim.
       intros n.
       generalize dependent X'.
       generalize dependent X.
       generalize dependent Γ.
       generalize dependent A.
       induction n.
       - intros A Γ X x f X' g f' f'g_gf.
         simpl. rewrite !stream_hd.
         rewrite <- (compose_assoc _ f'), -> (compose_assoc x g f').
         rewrite f'g_gf.
         rewrite !compose_assoc, parallel_fst, compose_id_left.
         reflexivity.
       - intros A Γ X x f X' g f' f'g_gf.
         simpl.
         rewrite <- !compose_assoc.
         rewrite !stream_tl.
         assert (snd ∘ f' ∘ (g ∘ x) == g ∘ (snd ∘ f ∘ x)) as H0.
         { rewrite !compose_assoc.
           apply compose_Proper; try reflexivity.
           rewrite <- compose_assoc.
           rewrite f'g_gf, compose_assoc, parallel_snd.
           reflexivity.
         }
         assert (stream (snd ∘ f' ∘ (g ∘ x)) f' == stream (g ∘ (snd ∘ f ∘ x)) f') as H1.
         {
           apply stream_Proper; try reflexivity. apply H0.
         }
         rewrite H1. (* Not sure how better to phrase this. *)
         apply IHn. assumption.
Qed.
         

         

End Stream.

End Stream.