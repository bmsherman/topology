Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Prob.
Section Prob.

Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmcprops : CMC_Props U}.

Require Import Spec.Sierpinski Spec.Real Spec.Sum Spec.Stream Spec.Discrete
  Spec.SMonad Spec.Vec.
Require Import Morphisms.
Import Sierp.
Import Real.
Import Sum.
Import Vec.
Import Stream.
Import Discrete.

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
Context {discrete : Type -> U}.
Context {pow : Type -> U -> U}.
Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete pow}.
Context {DProps : (@DiscreteProps U ccat cmc discrete pow DOps)}.


Require Import Spec.CCC.CCC.
Require Import Spec.CCC.Presheaf.
Require Import Prob.Language.ContPL.

Import CCC.
Import Presheaf.

Existing Instances CCat_PSh CMC_Psh CMCProps_PSh CCCOps_PSh.

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
  ; pstream_Proper : forall Γ A X, Proper (eq ==> eq ==> eq) (@pstream Γ A X)
  ; pstream_ext1 : forall {Γ Δ A X} (g : Γ ~~> Δ) (x : Δ ~~> X) (f : Δ * X ~~> Prob (A * X)),
      (pstream x f) ∘ g == pstream (x ∘ g) (f ∘ (g ⊗ id))
  ; unit_Prob : (id (A := Prob unit)) == ret ∘ tt
  ; fst_strong : forall {A B}, (map fst) ∘ (strong (M:=Prob)(A:=A)(B:=B)) == ret ∘ fst

  ; Pstream : forall {A X : U}, Const (Y X ==> (Y X ==> Y (Prob (A * X))) ==> Y (Prob (Stream A)))
  ; Coinflip : Const (Y (Prob (unit + unit)))
  ; Normal : Const (Y (Prob R))
  ; Prob_discrete : forall {A}, (Prob (discrete A)) ~~> pow A LRnn
  ; Prob_discrete_mono : forall {A}, Mono (Prob_discrete (A:=A))                                             
  }.

Context {mops : MeasOps}.

Existing Instance ProbMonad.

Lemma Prob_unit_Iso : Prob unit ≅ unit.
Proof. eapply Build_Iso. Unshelve.
       Focus 3. exact tt.
       Focus 3. exact ret.
       rewrite unit_uniq, (unit_uniq id).
       reflexivity.
       symmetry. exact unit_Prob.
Defined.


Axiom pstream_unfold : forall (Γ A X : U) 
 (x : Γ ~~> X) (f : Γ * X ~~> Prob (A * X)),
      pstream x f == (
        y <-  (f ∘ ⟨ id , x ⟩);
        zs <- pstream (X := X) (snd ∘ y) (liftF f) ;
         Ret (cons (fst ∘ !y) zs) 
      ).

Definition Prob_Stream_eq_type : forall {Γ A} {s t : Γ ~~> Prob (Stream A)}, Prop.
(*    (forall n, (map (prefix n)) ∘ s == (map (prefix n)) ∘ t) -> (s == t). *)
Proof. intros.
       assert (Prop -> Prop -> Prop) as implies. { intros P Q. exact (P -> Q). }
       refine (implies _ (s == t)).
       refine (forall n, (map (prefix n)) ∘ s == (map (prefix n)) ∘ t).
       (* Show Proof. *)
Defined.

Axiom Prob_Stream_eq : forall {Γ A} {s t : Γ ~~> Prob (Stream A)},
    Prob_Stream_eq_type (Γ:=Γ) (A:=A) (s:=s) (t:=t).

Notation "'LAM'<< Γ | E >> x => f" := (makeFun1E (fun Γ E x => f))
                                        (at level 120, right associativity). 

Notation "x <- e ;<< Γ | E >> f" := (Bind e (makeFun1E (fun Γ E x => f))) 
                                      (at level 120, right associativity).

Axiom Fubini : forall {Γ A B C} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B) 
                 (f g : forall Δ (ext : Extend Γ Δ), (Δ ~~> A) -> (Δ ~~> B) -> (Δ ~~> Prob C)),
      (forall Δ ext a b, (f Δ ext a b) == (g Δ ext a b) )->
      (x <- mu;<< Δ | e >> y <- !nu;<< Δ' | e' >> (f Δ' (e∘e') (!x) y))
      == (y <- nu;<< Δ | e >> x <- !mu;<< Δ' | e' >> (g Δ' (e∘e') x (!y))).


  (* Maybe this should be elsewhere? *)
  
Theorem Fubini_pair : forall {Γ A B} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
    (x <- mu; y <- !nu; Ret ⟨!x, y⟩) == (y <- nu; x <- !mu; Ret ⟨x, !y⟩).
Proof. intros Γ A B mu nu.  
         unshelve eapply (Fubini mu nu (fun _ _ a b => Ret ⟨a, b⟩) (fun _ _ a b => Ret ⟨a, b⟩) _).
         intros. reflexivity.         
Qed.


Definition marg {A B : U} : Prob (A * B) ~~> (Prob A) * (Prob B) :=
  ⟨map fst , map snd⟩.
(* 'marg' for 'marginal' *)


End Prob.

End Prob.