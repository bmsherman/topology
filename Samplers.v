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
Require Import Coq.Lists.List.
Import ListNotations.
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

  Definition prod_pair {Γ A B : U} (f : Γ ~~> A) (g : Γ ~~> B) : Γ ~~> A * B :=
    (f ⊗ g) ∘ diagonal.

  Notation "( x , y )" := (prod_pair x y) : morph_scope.

  Check ap0.
(*    makeFun [Prob A ; Prob B] *) 
(* : [(Prob A) ; (Prob B)] ~> Prob (A * B)*)

Local Instance smd : SMonad U Prob := ProbMonad.
  
  
  Definition indep {Γ X Y : U} (DA : Γ ~~> Prob X) (DB : Γ ~~> Prob Y)  :=
    a <- DA; (b <- DB; Ret (!a , !b)).

  Check indep.
                

  (* TODO rewrite with ContPL? *)
  
  Theorem indep' : forall {X A B : U} (DA : X ~~> Prob A) (DB : X ~~> Prob B), X ~~> Prob (A * B).
  Proof.
    intros.
    eapply compose.
    apply (join (SMonad := ProbMonad)).
    eapply compose.
    apply (map (SMonad := ProbMonad) (strong (SMonad := ProbMonad))).
    eapply compose.
    apply (map (SMonad := ProbMonad) ((snd ⊗ fst) ∘ diagonal)).
    eapply compose.
    apply (strong (SMonad := ProbMonad)).
    eapply compose.
    apply (DB ⊗ DA).
    apply diagonal.
Defined.

  Print indep.

  Theorem sampling_cond : forall {X A S : U} (DS : X ~~> Prob S) (DA : X ~~> Prob A) (transform : X * S ~~> S * A), Type.
  Proof. intros. eapply eq.
         - eapply compose. apply (map (SMonad := ProbMonad) transform).
         eapply compose. apply (strong (SMonad := ProbMonad)).
         eapply compose. apply (id ⊗ DS).
         apply diagonal.
         - eapply compose. apply (indep (X := (Prob S) * (Prob A))).
           { apply fst. }
           { apply snd. }
           eapply compose. apply (DS ⊗ DA).
           apply diagonal.
  Defined.
  

  Record Sampler {X A S : U} (DS : X ~~> Prob S) (DA : X ~~> Prob A) : Type :=
    sampler
      {
        transform : X * S ~~> S * A;
        samples : sampling_cond DS DA transform
      }.

  Theorem id_sampling_cond_stmnt {X S : U} {DS : X ~~> Prob S} (A : U) (a : X ~~> A) : Type.
  Proof. intros. eapply sampling_cond. exact DS. eapply compose. eapply (ret (SMonad := ProbMonad)). apply a. eapply compose. apply ((snd ⊗ fst) ∘ diagonal). apply (a ⊗ id).
  Defined.

  Theorem id_sampling_cond {X S : U} {DS : X ~~> Prob S} (A : U) (a : X ~~> A) : (@id_sampling_cond_stmnt X S DS A a).
  Proof. unfold id_sampling_cond_stmnt. unfold sampling_cond. unfold indep.
         admit.
         Admitted.
