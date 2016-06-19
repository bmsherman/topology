Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Prob.
Section Prob.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Require Import Spec.Sierpinski Spec.Real Spec.Sum Spec.Stream.
Import Sierp.
Import Real.
Import Sum.
Import Stream.

Context `{sierpops : ΣOps U (ccat := ccat) (cmc := cmc)}.
Context `{lrnnops : LRnnOps U (ccat := ccat) (cmc := cmc) 
  (Σ := Σ)}.
Context `{realops : ROps U (ccat := ccat) (cmc := cmc) 
  (Σ := Σ)}.
Context `{sumops : SumOps U (ccat := ccat)}.
Context `{streamops : StreamOps U (ccat := ccat)}.

Context {Open : U -> U}.

Class OpenOps : Type :=
  { open_abstract : forall {Γ A : U}, Γ * A ~~> Σ -> Γ ~~> Open A }.

Context {Meas Prob SubProb : U -> U}.

Require Import Prob.ContPL.

Class MeasOps : Type :=
  { MeasMonad : SMonad (ccat := ccat) (cmc := cmc) U Meas
  ; ProbMonad : SMonad  (ccat := ccat) (cmc := cmc) U Prob
  ; SubProbMonad : SMonad  (ccat := ccat) (cmc := cmc) U SubProb
  ; Prob_to_SubProb : forall {A}, Prob A ~~> SubProb A
  ; SubProb_to_Meas : forall {A}, SubProb A ~~> Meas A
  ; MeasEval : forall {A}, Meas A * Open A ~~> LRnn
  (** A real number telling us the probability that we
      are in the left-hand side *)
  ; ProbEval : forall {A B : U}, Prob (A + B) ~~> R
  ; coinflip : unit ~~> Prob (unit + unit)
  ; normal : unit ~~> Prob R
  ; pstream : forall {Γ A X}, Γ ~~> X -> Γ * X ~~> Prob (A * X)
                       -> Γ ~~> Prob (Stream A)
  ; unit_Prob : (id (A := Prob unit)) == ret ∘ tt
  ; fst_strong : forall {A B}, (map fst) ∘ (strong (M:=Prob)(A:=A)(B:=B)) == ret ∘ fst
  }.

Context {mops : MeasOps}.

Existing Instance ProbMonad.

(* This should probably get moved somewhere else *)
Definition liftF {Γ Δ A B : U} 
  {ext : Extend U ccat Γ Δ} (f : Γ * A ~~> B) : Δ * A ~~> B :=
  f ∘ (ext ⊗ id).

Axiom pstream_unfold : forall (Γ A X : U) 
  (x : Γ ~~> X) (f : Γ * X ~~> Prob (A * X)),
      pstream x f == (
         y <- f ∘ ⟨ id , x ⟩ ;
         zs <- pstream (X := X) (snd ∘ y) (liftF f) ;
         Ret (cons (fst ∘ !y) zs) 
         ).  

End Prob.

End Prob.