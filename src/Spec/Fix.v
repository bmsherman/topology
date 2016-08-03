Require Import Spec.Category Spec.Sierpinski Spec.Sum.

Import Category Sierp Sum.
Import Morphisms.
Local Open Scope obj.
Local Open Scope morph.

Section Specialization.

  Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmp : CMC_Props U}
          {Σ : U} {Σos : @ΣOps U ccat cmc Σ} {Σps : ΣProps}
          {sts : SumTys} {sos : SumOps (U:=U)}.
  
  Axiom sub : forall {A}, (A ~~> Σ) -> (A ~~> Σ) -> Prop.

  (* Ignore this for now. *) 
 Definition nsub : forall {A}, (A ~~> Σ) -> (A ~~> Σ) -> Prop :=
    fun A u v => exists (x : unit ~~> A), u ∘ x == true /\ v ∘ x == false.

  (* Maybe make this definitional. 
 Theorem nnsub : forall {A} (u v : A ~~> Σ), (sub u v) <-> ~ (nsub u v). *)

  Axiom sub_reflexive : forall {A} (f : A ~~> Σ), sub f f.

  Axiom sub_transitive : forall {A} (f g h : A ~~> Σ), sub f g -> sub g h -> sub f h.

  Axiom sub_Proper : forall {A}, Proper (eq ==> eq ==> Logic.iff) (sub (A:=A)).

  Axiom sub_ext : forall {A A'} (f : A ~~> A') (u v : A' ~~> Σ), sub u v -> sub (u ∘ f) (v ∘ f).
  (** I.e. taking inverse images of subsets is monotone **)       


  Definition sleq : forall {A B}, (A ~~> B) -> (A ~~> B) -> Prop :=
    fun A B f g => forall (V : B ~~> Σ), sub (V ∘ f) (V ∘ g).

  Lemma sleq_Proper : forall {A B}, Proper (eq ==> eq ==> Logic.iff) (sleq (A:=A)(B:=B)).
  Proof.
    intros A B.
    unfold Proper, respectful.
    intros f f' ff' g g' gg'.
    unfold sleq.
    split; intros H V; specialize (H V).
    - rewrite <- ff', <- gg'.
      assumption.
    - rewrite -> ff', -> gg'.
      assumption.
  Qed.   
    

(* Definition slt : forall {A B}, (A ~~> B) -> (A ~~> B) -> Prop :=
    fun A B f g => (sleq f g) /\ exists (V : B ~~> Σ), nsub (V ∘ g) (V ∘ f). *)  
  
  (* Lemma lt_so_leq : forall {A B} (f f' : A ~~> B), (slt f f') -> (sleq f f').
  Proof.
    intros A B f f' H.
    destruct H as [fleqf' H].
    assumption.
  Qed. *)
      
  Lemma compose_sleq : forall {A B C}, Proper (sleq ==> sleq ==> sleq) (compose (A:=A) (B:=B) (C:=C)).
  Proof. intros A B C. unfold Proper, respectful. intros g g' gg' f f' ff'.
         unfold sleq. intros V.
         specialize (gg' V). specialize (ff' (V ∘ g')).
         pose proof (sub_ext f _ _ gg').
         rewrite !compose_assoc.
         repeat (eapply sub_transitive; eassumption).         
  Qed.

  Axiom pair_sleq : forall {A B C}, Proper (sleq ==> sleq ==> sleq) (pair (A:=A) (B:=B) (Γ:=C)).
  (** This is theoretically provable, given some other assumptions. Sketch: 
     If V = Va x Vb is a product of basic opens, then the conclusion is true; now for an 
     arbitrary V, write V as a union of Va x Vb. But everything is monotone, so you can reduce to the
     previous case. **)

  Axiom sum_sleq : forall {Γ A0 A1 B} (f g : Γ * (A0 + A1) ~~> B),
    (sleq (f ∘ (id ⊗ inl)) (g ∘ (id ⊗ inl))) -> (sleq (f ∘ (id ⊗ inr)) (g ∘ (id ⊗ inr))) ->
    (sleq f g).

  Axiom sleq_eq : forall {Γ A} (f g : Γ ~~> A), (sleq f g) -> (sleq g f) -> (f == g).
  
  Section Prob.

    Lemma sleq_reflexive : forall {Γ A} (mu : Γ ~~> A), sleq mu mu.
    Proof.
      intros Γ A mu.
      unfold sleq. intros v. apply sub_reflexive.
    Qed.


    Lemma sleq_transitive : forall {Γ A} (mu nu ou : Γ ~~> A), sleq mu nu -> sleq nu ou -> sleq mu ou.
    Proof.
      intros Γ A mu nu ou mn no.
      unfold sleq. intros V. 
      specialize (mn V). specialize (no V).
      apply (sub_transitive _ _ _ mn no).
    Qed.

    Lemma sleq_ext : forall {Γ Γ' A} (f g : Γ' ~~> A) (h : Γ ~~> Γ'),
        (sleq f g) -> (sleq (f ∘ h) (g ∘ h)).
    Proof.
      intros Γ Γ' A f g h fg.
      unfold sleq.
      intros V.
      specialize (fg V).
      eapply sub_Proper; try apply compose_assoc.
      apply sub_ext. assumption.
    Qed.

    Require Import Spec.Real.
    Import Real.
    
    (* Theorem Bind_lt_monotone : forall {Γ A B} (mu : Γ ~~> Meas A) (f g : Γ * A ~~> Meas B),
    (sleq f g) -> (exists U : Γ * A ~~> Σ,
                        (LRnnlt _ (LRnnzero _ ∘ tt) (MeasEval ∘ ⟨mu, (open_abstract U)⟩)) /\
                        (forall u : Γ ~~> A, (U ∘ ⟨id, u⟩ == true ∘ tt) ->
                                     slt (f ∘ ⟨id, u⟩) (g ∘ ⟨id, u⟩))) ->
    (slt (Bind mu f) (Bind mu g)). *)

    Section Bottom.

      Definition isBot {A : U} : (forall Γ, Γ ~~> A) -> Prop :=
        fun a => forall Γ (a' : Γ ~~> A), sleq (a Γ) a'.

      Definition hasBot : U -> Type :=
        fun A => sig (isBot (A:=A)).

      Definition bot {A Γ} (h : hasBot A) : Γ ~~> A :=
        ((proj1_sig h) Γ).

      Definition ishas : forall {A} {x : forall Γ, Γ ~~> A}, isBot x -> hasBot A.
      Proof. intros A x H.
             exists x. assumption.
      Defined.


    End Bottom.
      

      
    Section Fix.
      
      Fixpoint iter {A} (n : nat) : (A -> A) -> A -> A :=
        fun F =>
          match n with
          | O => fun x => x
          | (S m) => fun x => F (iter m F x)
          end.

      Axiom sfix : forall {Γ A : U} (F : (Γ ~~> A) -> (Γ ~~> A))
          (h : hasBot A),
          (Proper (sleq ==> sleq) F) ->
          Γ ~~> A.
      
      Axiom sfix_fix : forall {Γ A} (F : (Γ ~~> A) -> (Γ ~~> A))
                         (h : hasBot A)
                         (p : Proper (sleq ==> sleq) F),
          (F (sfix F h p)) == sfix F h p.
      
      Axiom sfix_min : forall {Γ A} (F : (Γ ~~> A) -> (Γ ~~> A))
                         (h : hasBot A)
                         (p : Proper (sleq ==> sleq) F)
                         (mu : Γ ~~> A),
          (F mu == mu) -> sleq (sfix F h p) mu.

      Lemma sleq_Proper_eq_Proper : forall {A B C D} (H : A ~~> B -> C ~~> D),
          Proper (sleq ==> sleq) H -> Proper (eq ==> eq) H.
      Proof. intros A B C D H HP.
             unfold Proper, respectful.
             intros x y xy.
             apply sleq_eq.
             - apply HP. eapply sleq_Proper. exact xy. reflexivity.
               apply sleq_reflexive.
             - apply HP. eapply sleq_Proper. reflexivity. exact xy.
               apply sleq_reflexive.
      Qed.


      Lemma sfix_map : forall {A B C D : U} (F : (A ~~> B) -> (A ~~> B)) (G : C ~~> D -> C ~~> D) (H : A ~~> B -> C ~~> D)
                         (FP : Proper (sleq ==> sleq) F) (GP : Proper (sleq ==> sleq) G)
                         (hB : hasBot B)(hD : hasBot D),
          (forall f, H (F f) == G (H f)) -> Proper (sleq ==> sleq) H -> (H (bot hB) == bot hD) ->
          H (sfix F hB FP) == sfix G hD GP.
      Proof.
        intros A B C D F G H FP GP hB hD HF_GH HP hH.
        apply sleq_eq.
        - admit. (* This really ought to be provable. I should work it out if it isn't. *)
        - apply sfix_min.
          rewrite <- HF_GH. pose proof (sleq_Proper_eq_Proper H HP) as E.
          rewrite sfix_fix.
          reflexivity.
      Admitted.
      
    End Fix.
  End Prob.
End Specialization.