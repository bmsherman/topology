Require Import Spec.Category Spec.Sup Spec.Sierpinski Spec.Sum.

Import CMorphisms Category Sup Sierp Sum.
Local Open Scope obj.
Local Open Scope morph.
      
Section Fix.
  
  Arguments exist {A} {P} x _.
  
  Context {U : Type} {ccat : CCat U} {cmc : CMC U}
          {Σ : U}         
          `{sps : SumProps(U:=U)(ccat:=ccat)(cmc:=cmc)}.  

  
  Fixpoint iter {A} (n : nat) : (A -> A) -> A -> A :=
    fun F =>
      match n with
      | O => fun x => x
      | (S m) => fun x => F (iter m F x)
          end.
  
  Definition sfix : forall {Γ A : U} (F : (Γ ~~> A) -> (Γ ~~> A))
                      (h : hasBot(Σ:=Σ) Γ A),
      (Proper (sleq (Σ:=Σ) ==> sleq (Σ:=Σ)) F) ->
      Γ ~~> A.
  Proof. intros Γ A F h FP.
         apply (sup_nat_family (Σ:=Σ)).
         unfold nat_family.
         exists (fun n : nat => iter n F (bot h)).
         induction n.
         - destruct h. simpl. unfold isBot in i. apply i.
         - simpl. apply FP. apply IHn.
  Defined.

  Existing Instance sleq_Proper.
  
  Theorem sfix_fix : forall {Γ A} (F : (Γ ~~> A) -> (Γ ~~> A))
                     (h : hasBot Γ A)
                     (p : Proper (sleq ==> sleq) F)
                     (c : Cont F p),
      (F (sfix F h p)) == sfix F h p.
  Proof.
    intros Γ A F h p c.    
    unfold sfix. rewrite c.
    apply (sleq_eq(Σ:=Σ)); apply sup_sleq_sup.
    - simpl. intros n. exists (S n).
      simpl. apply sleq_reflexive.
    - simpl. intros n. exists n.
      induction n.
      + destruct h. simpl. apply i.
      + simpl. apply p. apply IHn.
  Qed.

  
  Theorem sfix_min : forall {Γ A} (F : (Γ ~~> A) -> (Γ ~~> A))
                       (h : hasBot Γ A)
                       (p : Proper (sleq ==> sleq) F)
                       (mu : Γ ~~> A),
      (F mu == mu) -> sleq (Σ:=Σ) (sfix F h p) mu.
  Proof. intros Γ A F h p mu mu_fix.
         unfold sfix; apply sup_nat_family_prop; simpl.
         induction n.
         - destruct h; simpl. apply i.
         - simpl. rewrite <- mu_fix.
           apply p. apply IHn.
  Defined.    
  
  Lemma sleq_Proper_eq_Proper : forall {A B C D} {H : A ~~> B -> C ~~> D},
      Proper (sleq(Σ:=Σ) ==> sleq(Σ:=Σ)) H -> Proper (eq ==> eq) H.
  Proof. intros A B C D H HP.
         unfold Proper, respectful.
         intros x y xy.
         apply (sleq_eq (Σ:=Σ)).
         - apply HP. eapply sleq_Proper. exact xy. reflexivity.
           apply sleq_reflexive.
         - apply HP. eapply sleq_Proper. reflexivity. exact xy.
           apply sleq_reflexive.
  Qed.


  Lemma sfix_map : forall {A B C D : U} (F : (A ~~> B) -> (A ~~> B)) (G : C ~~> D -> C ~~> D) (H : A ~~> B -> C ~~> D)
                         (FP : Proper (sleq ==> sleq) F) (GP : Proper (sleq ==> sleq) G)
                         (h0 : hasBot A B)(h1 : hasBot C D)
                         (HP : Proper (sleq(Σ:=Σ) ==> sleq(Σ:=Σ)) H),
      (forall f, H (F f) == G (H f)) -> (H (bot h0) == bot h1) ->
      (Cont H HP) -> 
      H (sfix F h0 FP) == sfix G h1 GP.
      Proof.
        intros A B C D F G H FP GP h0 h1 HP HF_GH Hbot HC.
        unfold sfix at 1.
        rewrite HC. apply sup_exacteq_sup. simpl.
        induction n.
        - simpl. apply Hbot.
        - simpl. rewrite HF_GH.
          apply (sleq_Proper_eq_Proper GP). (* Interesting that GP and not FP is used in the proof; *)
          apply IHn.                        (* however, both are needed for the statement.          *)
      Qed.

      
End Fix.