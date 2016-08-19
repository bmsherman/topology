Require Import Spec.Category Spec.Sierpinski Spec.Sum.
Import Morphisms Category Sierp Sum.

Local Open Scope obj.
Local Open Scope morph.

Section Suprema.

  Arguments exist {A} {P} x _.
  
  Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmp : CMC_Props U}
          {Σ : U} {Σos : @ΣOps U ccat cmc Σ} {Σps : ΣProps}
          {sts : SumTys} {sos : SumOps (U:=U)}{sps : SumProps}.

  Section Specialization.
    
    Axiom sub : forall {A}, (A ~~> Σ) -> (A ~~> Σ) -> Prop.
    
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

    Axiom false_sleq_anything : forall x, sleq false x.
    
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
    
    (* Theorem Bind_lt_monotone : forall {Γ A B} (mu : Γ ~~> Meas A) (f g : Γ * A ~~> Meas B),
    (sleq f g) -> (exists U : Γ * A ~~> Σ,
                        (LRnnlt _ (LRnnzero _ ∘ tt) (MeasEval ∘ ⟨mu, (open_abstract U)⟩)) /\
                        (forall u : Γ ~~> A, (U ∘ ⟨id, u⟩ == true ∘ tt) ->
                                     slt (f ∘ ⟨id, u⟩) (g ∘ ⟨id, u⟩))) ->
    (slt (Bind mu f) (Bind mu g)). *)
    
    Section Bottom.
      
      Definition isBot {A B : U} : (A ~~> B) -> Prop :=
        fun b => forall (b' : A ~~> B), sleq b b'.
      
      Definition hasBot : U -> U -> Type :=
        fun A B => sig (@isBot A B).

      Definition bot {A B} (h : hasBot A B) : A ~~> B :=
        proj1_sig h.

      Definition ishas : forall {A B} {x : A ~~> B}, isBot x -> hasBot A B.
      Proof. intros A B x H.
             exists x. assumption. 
      Defined.
            
    End Bottom.

  End Specialization.
    
  Section Nat.

    Definition nat_family : U -> U -> Type :=
      fun A B => {f : nat -> A ~~> B | forall n : nat, sleq (f n) (f (S n))}.

    Axiom sup_nat_family : forall {A B : U} (f1 : nat_family A B), A ~~> B.

    Axiom sup_nat_family_prop : forall {A B : U} (f1 : nat_family A B),
        let f := proj1_sig f1 in
        forall y : A ~~> B, sleq (sup_nat_family f1) y <-> forall n : nat, sleq (f n) y.

    Lemma sup_geq_members : forall {A B : U} (f1 : nat_family A B) (g : A ~~> B),
        (exists n : nat, sleq g (proj1_sig f1 n)) -> sleq g (sup_nat_family f1).
    Proof. intros A B f1 g N. destruct N.
           pose (sup_nat_family_prop f1) as H0.
           specialize (H0 (sup_nat_family f1)).
           destruct H0; clear H1.
           specialize (H0 (sleq_reflexive _)).
           eapply sleq_transitive.
           apply H. apply H0.
    Qed.

        
    Lemma po_yoneda : forall {A B} (x y : A ~~> B),
        (forall z, sleq x z <-> sleq y z) -> x == y.
    Proof. intros.
           apply sleq_eq.
           apply H. apply sleq_reflexive.
           apply H. apply sleq_reflexive.
    Qed.

    Lemma sup_sleq_sup : forall {A B : U} (f1 f2 : nat_family A B),
        (forall n, exists m, sleq (proj1_sig f1 n) (proj1_sig f2 m)) ->
        sleq (sup_nat_family f1) (sup_nat_family f2).
    Proof.
      intros A B f1 f2 h1.
      rewrite !sup_nat_family_prop.
      intros n. specialize (h1 n). destruct h1 as [m h1].
        eapply sleq_transitive. 
        apply h1. apply sup_geq_members. exists m. apply sleq_reflexive.
    Qed.

    Lemma sup_exacteq_sup : forall {A B : U} (f1 f2 : nat_family A B),
        (forall n, (proj1_sig f1 n) == (proj1_sig f2 n)) -> (sup_nat_family f1) == (sup_nat_family f2).
    Proof. intros.
           apply sleq_eq; apply sup_sleq_sup; intros n; exists n;
             specialize (H n); eapply sleq_Proper; try apply H; try reflexivity; apply sleq_reflexive.
    Qed.
    
  End Nat.

    Section Cont.

    Definition Cont {A B C D : U} (F : A ~~> B -> C ~~> D) : (Proper (sleq ==> sleq) F) -> Prop.
    Proof. intros FP.
           refine (
               forall f : nat_family A B, F (sup_nat_family f) == _).
           refine (sup_nat_family _).
           unfold nat_family. exists (fun n : nat => F ((proj1_sig f) n)).
           intros n. apply FP. apply (proj2_sig f).
    Defined.

    Theorem everything_cont : forall {A B} (F : A ~~> B -> A ~~> B)
                                (FP : Proper (sleq ==> sleq) F),
        Cont F FP.
    Proof. intros A B F FP.
           unfold Cont. intros f.
           apply (sleq_eq).
           - (* Well, this doesn't look provable to me... *)
    Abort.

    Existing Instance sleq_Proper.

    Lemma sum_elim_sleq :  forall {Γ A B C} (f : Γ * A ~~> C),
        Proper (sleq ==> sleq) (sum_elim (B:=B) f).
    Proof. intros Γ A B C f.
           unfold Proper, respectful.
           intros. apply sum_sleq.
           - eapply sleq_Proper. eapply sum_elim_inl. eapply sum_elim_inl.
             apply sleq_reflexive.
           - eapply sleq_Proper. eapply sum_elim_inr. eapply sum_elim_inr.
             assumption.
    Qed.

    Axiom precompose_Cont : forall {A B C : U} (f : A ~~> B),
        Cont (fun g : B ~~> C => g ∘ f)
             (fun (x y : B ~~> C) (H : sleq x y) => compose_sleq x y H f f (sleq_reflexive f)).

    Axiom postcompose_Cont : forall {A B C : U} (f : B ~~> A),
        Cont (fun g : C ~~> B => f ∘ g)
             (fun (x y : C ~~> B) (H : sleq x y) => compose_sleq f f (sleq_reflexive f) x y H).

    Axiom pairR_Cont : forall {A B C : U} (f : A ~~> B),
        Cont (fun g : A ~~> C => ⟨ f, g ⟩) (pair_sleq f f (sleq_reflexive f)).

    Axiom pairL_Cont : forall {A B C : U} (g : A ~~> C), (*maybe follows from the above *)
        Cont (fun f : A ~~> B => ⟨ f, g ⟩) (fun a b c => pair_sleq a b c g g (sleq_reflexive g)).
      
      
    Lemma sum_elim_Cont : forall {Γ A B C} (f : Γ * A ~~> C),
        Cont (sum_elim (B:=B) f) (sum_elim_sleq f).
    Proof. intros Γ A B C f.
           unfold Cont. intros f0.
           destruct f0.
           apply sum_determines.
           - rewrite precompose_Cont. 
             rewrite sum_elim_inl.
             apply po_yoneda. intros z.
             rewrite sup_nat_family_prop. simpl.
             assert ( (forall n : nat, sleq (sum_elim f (x n) ∘ id ⊗ inl) z) <-> (forall n : nat, sleq f z)).
             { split. intros. specialize (H n). eapply (sleq_Proper). symmetry.
               apply (sum_elim_inl (B:=B)). reflexivity. apply H. intros. specialize (H n).
               eapply (sleq_Proper). apply (sum_elim_inl (B:=B)). reflexivity. apply H. }
             rewrite H. intuition; auto. apply H1. exact 0. (* kind of disappointed in coq here *)
           - rewrite precompose_Cont.
             rewrite sum_elim_inr.
             apply sleq_eq; apply sup_sleq_sup; intros n; exists n; simpl; eapply sleq_Proper.
             reflexivity. eapply sum_elim_inr. apply sleq_reflexive.
             eapply sum_elim_inr. reflexivity. apply sleq_reflexive.
    Qed.

  End Cont.


  
    
End Suprema.