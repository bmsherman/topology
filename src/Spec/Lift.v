(** Definition of "lifted" spaces, which are spaces with a "bottom"
    (think non-termination) element adjoined. *)

Require Import 
  Spec.Category
  Spec.Stream 
  Spec.Sum 
  Spec.Pullback 
  Spec.Sup 
  Fix 
  Spec.Sierpinski.

Import Category.
Import Stream.
Import Sum Pullback.
Import Sup.
Import Fix.
Import Sierp.
Local Open Scope obj.
Local Open Scope morph.

Module Lift.
Section Lift.

Context `{SOps : StreamOps}.
Context {cmc : CMC U}.
Context `{sumOps : SumOps (U := U) (ccat := ccat)}.
Context {Lift : U -> U}.
(*Context {Embedding : forall A B, A ~~> B -> Prop}.*)
Context {Σ : U}.
Context {σos : ΣOps (Σ:=Σ)}.
Context {σps : ΣProps (Σ:=Σ)}.

(*Arguments Embedding {A} {B} f.*)

Class LiftOps : Type :=
  { strict : forall {A}, A ~~> Lift A
    ; bottom : forall {A}, unit ~~> Lift A
    ; lift_rec : forall {A X} (x : unit ~~> X) (f : A ~~> X),
        (forall {a : unit ~~> A}, sleq(Σ:=Σ) x (f ∘ a)) -> Lift A ~~> X 
    ; gen_recursion : forall {A}, Stream (unit + A) ~~> Lift A 
    ; bottom_min : forall {A B}, isBot (Σ:=Σ) (bottom (A:=A) ∘ tt(Γ:=B))
    ; apart : forall {X A} (f : X ~~> unit) (g : X ~~> A), (bottom ∘ f == strict ∘ g) -> Logic.False 
  }.


(* If I haven't messed up, Lift A has the following universal property. I do not know if this will be useful.
 A map from Lift A to B is equivalent to the following data:
  a map f from A to B and a global point b of B ("default"), 
  such that for all opens U of B, b in U implies forall a : A, f(a) in U. *)

Context `{los : LiftOps}.

Class LiftProps : Type :=
  { strict_mono : forall {A}, Mono (strict (A := A))
    (*; strict_embedding :  forall {A}, OpenEmbedding (Σ:=Σ) (strict (A:=A))*)
    ; lift_rec_bottom : forall {A X x f p}, (@lift_rec _ A X x f p) ∘ bottom == x
    ; lift_rec_strict : forall {A X x f p}, (@lift_rec _ A X x f p) ∘ strict == f
  ; gen_recursion_tl : forall {A},
    gen_recursion (A := A) == sum_elim fst (strict ∘ snd) 
                              ∘ ⟨(gen_recursion ∘ tl (StreamOps := SOps)),  hd (StreamOps := SOps)⟩
  } .


Definition recursion {Γ X A : U} : (Γ ~~> X) -> (X ~~> A + X) -> Γ ~~> Lift A.
Proof. intros x0 h.
       assert (Γ ~~> Stream (unit + A)) as Y.
       {
         eapply (stream (X:=X)).
         - exact x0.
         - eapply (_ ∘ ⟨id, h⟩). Unshelve.
           eapply sum_elim.
           + exact ⟨inr ∘ snd, fst⟩. 
           + exact (⟨inl ∘ tt, id⟩ ∘ snd).
       }
       exact (gen_recursion ∘ Y).
Defined.

Context {cps : CMC_Props U} {sps : StreamProps}.

Lemma recursion_ext1 : forall {Γ Γ' X A : U} (f : Γ ~~> Γ') (g : Γ' ~~> X) (h : X ~~> A + X),
    recursion (g ∘ f) h == recursion g h ∘ f.
Proof. intros Γ Γ' X A f g h. 
       unfold recursion. remove_eq_left.
       apply stream_ext1.
Qed.
       


Context `{lps : LiftProps}.

Existing Instance sleq_Proper.

Definition terminates : forall {A}, Lift A ~~> Σ.
Proof. intros A. unshelve eapply lift_rec.
       - exact false.
       - exact (true ∘ tt).
       - intros a.
         rewrite <- compose_assoc, -> (unit_uniq _ id), -> compose_id_right.
         apply false_sleq_anything.
Defined.

Axiom Σ_to_Lift : Σ ~~> Lift unit.
Axiom Σ_to_Σ : terminates ∘ Σ_to_Lift == id.
Axiom Lift_to_Lift : Σ_to_Lift ∘ terminates == id.
Axiom true_to_Lift : Σ_to_Lift ∘ true == strict.
Axiom false_to_Lift : Σ_to_Lift ∘ false == bottom.

Lemma Σ_cong_Lu : Σ ≅ Lift unit.
Proof. unshelve eapply Build_Iso.
       exact Σ_to_Lift.
       exact terminates.
       exact Lift_to_Lift.
       exact Σ_to_Σ.
Defined.

(*Section Prob.
  Require Import Spec.Prob.
  Import Prob. Import SMonad.
  Context `{mos : MeasOps (U:=U)(Σ:=Σ)(ccat:=ccat)(cmc:=cmc)(sts:=sts)(Stream:=Stream)}.
  Existing Instance ProbMonad. Existing Instance MeasMonad.
  
  Definition precursion {Γ X A : U} : Γ ~~> X -> Γ * X ~~> Prob (A + X) -> Γ ~~> Prob (Lift A).
  Proof. intros x0 h.
         refine ((map gen_recursion) ∘ _).
         eapply pstream.
         - (* inital state *) exact x0.
         - unshelve eapply (_ ∘ ⟨snd, h⟩).
           unshelve eapply (_ ∘ strong). 
           refine (map _).
            eapply sum_elim.
           + exact ⟨inr ∘ snd, fst⟩. 
           + exact (⟨inl ∘ tt, id⟩ ∘ snd).
  Defined.

  End Prob. *)

Definition throw {A B C} := fun (f : C ~~> _) => ((inl (A:=A)(B:=B)) ∘ f).
Definition recall {A B C} := fun (f : C ~~> _) => ((inr (A:=A)(B:=B)) ∘ f).

End Lift.


End Lift.