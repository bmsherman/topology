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
  ; pstream : forall {Γ A X}, Γ ~~> Prob X -> Γ * X ~~> Prob (A * X)
                       -> Γ ~~> Prob (Stream A)
  ; unit_Prob : (id (A := Prob unit)) == ret ∘ tt
  ; fst_strong : forall {A B}, (map fst) ∘ (strong (M:=Prob)(A:=A)(B:=B)) == ret ∘ fst
  }.

Context `{MeasOps}.
Definition pstream_axiom {Γ A X} (x : Γ ~~> Prob X) (h : Γ * X ~~> Prob (A * X)) : Prop.
Proof. intros.
       refine (((map (SMonad:=ProbMonad) ⟨hd, tl⟩)∘(pstream x h)) == _).
       assert (Γ * X ~~> Prob X) as x'.
       { exact (ret (SMonad :=ProbMonad) ∘ snd). }
       assert ((Γ * X) * X ~~> Prob (A * X)) as h'.
       { exact (h ∘ (fst ⊗ id)). }
       Check (pstream x' h').
  refine (_ ∘ ⟨id, x⟩).
  refine (_ ∘ strong).
  refine (_ ∘ map ⟨fst, h⟩). 
  refine (_ ∘ (map (strong (M:=Prob)))).
  refine (_ ∘ join).
  refine (_ ∘ map (prod_assoc_left ∘ (id ⊗ ⟨snd, fst⟩))).
  refine (_ ∘ map ((pstream x' h') ⊗ id)).
  refine (_ ∘ map ⟨snd, fst⟩).
  refine (_ ∘ map (strong (M:=Prob))).
  exact (join (SMonad:=ProbMonad)). exact ProbMonad. exact ProbMonad. exact ProbMonad.
  Print Hint SMonad.
  exact ProbMonad. exact ProbMonad. exact ProbMonad. exact ProbMonad. exact ProbMonad.
  exact ProbMonad. exact ProbMonad.
  Show Proof.
Defined.            

End Prob.

End Prob.