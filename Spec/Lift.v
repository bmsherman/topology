(** Definition of "lifted" spaces, which are spaces with a "bottom"
    (think non-termination) element adjoined. *)

Require Import Spec.Category Spec.Stream Spec.Sum Spec.Pullback Spec.Sup Fix Spec.Sierpinski.

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
Context {Embedding : forall A B, A ~~> B -> Prop}.
Context {Σ : U}.
Context {σos : ΣOps (Σ:=Σ)}.
Context {σps : ΣProps (Σ:=Σ)}.

Arguments Embedding {A} {B} f.

Class LiftOps : Type :=
  { strict : forall {A}, A ~~> Lift A
    ; bottom : forall {A}, unit ~~> Lift A
    ; gen_recursion : forall {A}, Stream (unit + A) ~~> Lift A
    ; bottom_min : forall {A B}, isBot (Σ:=Σ) (bottom (A:=A) ∘ tt(Γ:=B))
    ; apart : forall {X A} (f : X ~~> unit) (g : X ~~> A), ~ (bottom ∘ f == strict ∘ g)
  }.


(* If I haven't messed up, Lift A has the following universal property. I do not know if this will be useful.
 A map from Lift A to B is equivalent to the following data:
  a map f from A to B and a global point b of B ("default"), 
  such that for all opens U of B, b in U implies forall a : A, f(a) in U. *)

Context `{LiftOps}.

Definition sum_elim' {A B C : U} (l : A ~~> C) (r : B ~~> C) 
  : (A + B) ~~> C
  := sum_elim (l ∘ snd) (r ∘ snd) ∘ add_unit_left.

Class LiftProps : Prop :=
  { strict_mono : forall {A}, Mono (strict (A := A))
  ; strict_embedding : forall {A}, Embedding (strict (A:=A))
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

Section Prob.
  Require Import Spec.Prob.
  Import Prob. Import SMonad.
  Context `{mos : MeasOps (U:=U)(Σ:=Σ)(ccat:=ccat)(cmc:=cmc)(sts:=sts)(Stream:=Stream)(Embedding:=@Embedding)}.
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

  Definition unlift {A} : Meas (Lift A) ~~> Meas A :=
    Meas_Embed _ (strict_embedding).

  Context {mps : SMonad_Props (M:=Meas)} `{sumps : SumProps(U:=U)(ccat:=ccat)(cmc:=cmc)(sts:=sts)}.

  Lemma unlift_strict : forall {A}, unlift ∘ (map strict) == id (A:=Meas A).
  Proof. intros A. unfold unlift. apply Embed_map.
  Qed.

  Lemma unlift_bot : forall {A : U}, unlift ∘ (map bottom) == zero(A:=A).
  Proof.
    intros A. unfold unlift. etransitivity.
    apply (Embed_nat tt bottom False_elim (strict(A:=A)) zero_one_embedding strict_embedding).

    unfold Pullback. split. split.
    - apply False_elim_unique.

    - unfold Mono; intros.
      apply (Embed_Mono (Embedding:=@Embedding) zero_one_embedding).
      rewrite (unit_uniq (tt ∘ g1)), (unit_uniq (tt ∘ g2)). reflexivity.

    - intros X j k stricteqbot. (* This is a kind of "inequality of distinct constructors" for Lift. *)
      exfalso.
      apply (apart _ _ stricteqbot).
    
    -  assert (forall {X}, map (M:=Meas) False_elim == zero(A:=X)). {
         intros X. rewrite <- (zero_scale (f:=(map False_elim))).
         rewrite (unit_uniq tt (tt ∘ (map(B:=X) False_elim))).
         rewrite -> compose_assoc.
         rewrite <- (compose_id_left (map False_elim)) at 3.
         rewrite <- pair_f.
         rewrite !compose_assoc.
         pose (map_scale (B:=X) (r:=Real.Real.LRnnzero _)(f:=False_elim)).
         etransitivity; symmetry; etransitivity. apply e.
         rewrite <- (compose_id_right (map False_elim)) at 2.
         remove_eq_left.
         rewrite <- compose_id_left.
         rewrite <- (from_to Meas_false) at 1.
         rewrite <- (from_to Meas_false) at 2.
         rewrite <- !compose_assoc.
         apply compose_Proper; try reflexivity.
         apply unit_uniq.
         reflexivity.
         remove_eq_right. remove_eq_left.
         unfold add_unit_left. rewrite parallel_pair, compose_id_left. reflexivity.
       }
       rewrite H0. rewrite zero_ext. reflexivity.
       Grab Existential Variables. apply tt. (* no idea why this is necessary. *)
  Qed.

  End Prob.

Definition throw {A B C} := fun (f : C ~~> _) => ((inl (A:=A)(B:=B)) ∘ f).
Definition recall {A B C} := fun (f : C ~~> _) => ((inr (A:=A)(B:=B)) ∘ f).

End Lift.


End Lift.