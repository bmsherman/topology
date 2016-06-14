Require Import Coq.Lists.List.
Import ListNotations.
Require Import ContPL.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream.
Import Category.
Import ContPL.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Lift.
Import Stream.
Import Discrete.
Local Open Scope morph.
Local Open Scope obj.

Section Samplers.

  Context {U : Type}.
  Context `{mops : MeasOps U}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) U 
   (LRnn := LRnn)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (R := R)
  (Σ := Σ)}.
  Context {sumops : SumOps}.
  Context `{sigmaops : ΣOps (U := U) (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)}.

  Definition swap {A B : U} : A * B ~~> B * A :=
    ⟨snd, fst⟩.

  Lemma snd_swap {A B : U} : snd ∘ (@swap A B) == fst.
  Proof. unfold swap. rewrite pair_snd. reflexivity.
  Defined.
  
 
  (* Local Instance smd : SMonad U Prob := ProbMonad. *)

Definition indep {A B : U} : [Prob A ; Prob B] ~> Prob (A * B) := 
   makeFun [Prob A ; Prob B] (fun Γ DA DB =>
                                  a <- !DA;
                                  b <- !DB;
                                  Ret ⟨!a, !b⟩).

Definition emap {Γ A B : U} (f : Γ * A ~~> B) : Γ * (Prob A) ~~> Prob B :=
  (map f) ∘ strong.

Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : indep ∘ ⟨DS, ⟨DA, tt⟩⟩ == (emap sample) ∘ ⟨id, DS⟩
      }.

Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.

Definition const_sampler {A : U} : Sampler (Δ := A) (S := unit) (ret ∘ tt) ret.
Proof. refine (sampler swap _). unfold emap. eapply (isom_eq_left _ _ (M_iso unit_isom_left)).
       unfold M_iso. simpl. rewrite (compose_assoc _ (map swap ∘ strong)), (compose_assoc _ (map swap)).
       rewrite map_compose. rewrite snd_swap.
       assert ((strong ∘ ⟨id (A:=A), ret ∘ tt⟩) == (ret ∘ ⟨id, tt⟩)) as beginning.
       { assert (⟨id (A:=A), ret ∘ tt⟩ == (id ⊗ ret) ∘ ⟨id, tt⟩) as Δ0.
         { rewrite parallel_pair. rewrite compose_id_left. reflexivity.
         } rewrite Δ0. rewrite compose_assoc. rewrite <- strength_ret. reflexivity.
       }
       rewrite <- compose_assoc, beginning. eapply (isom_eq_right _ _ (unit_isom_right)).
       simpl. rewrite <- (compose_assoc _ (ret ∘ ⟨id, tt⟩)). rewrite <- (compose_assoc _ ⟨id, tt⟩).
       assert (⟨id (A:=A), tt⟩ ∘ fst == id) as cancel.
       { apply (from_to unit_isom_right). }
       rewrite cancel. rewrite compose_id_right. rewrite <- ret_nat.
       unfold indep. unfold makeFun. simpl.