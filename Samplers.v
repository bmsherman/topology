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

  Definition swap {A B : U} : A * B ~~> B * A :=
    pair snd fst.
  
  Local Instance smd : SMonad U Prob := ProbMonad.

Definition indep {A B : U} : [Prob A ; Prob B] ~> Prob (A * B) := 
   makeFun [Prob A ; Prob B] (fun Γ DA DB =>
                                  a <- !DA;
                                  b <- !DB;
                                  Ret (pair (!a) (!b))).

Definition emap {Γ A B : U} (f : Γ * A ~~> B) : Γ * (Prob A) ~~> Prob B :=
  (map f) ∘ strong.

Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : indep ∘ (pair DS  (pair DA tt)) == (emap sample) ∘ (pair id DS)
      }.

Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.

Definition const_sampler {A : U} : Sampler (Δ := A) (S := unit) (ret ∘ tt) ret.
Proof. refine (sampler swap _). unfold emap.