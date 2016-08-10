Require Import Spec.Prob Spec.Category Spec.Sup Spec.SMonad Spec.Real Numbers.Qnn Fix.
Require Import Language.ContPL.

Import Prob Category Sup SMonad Real Qnn Fix.
Import ContPL.
Import Morphisms.

Local Open Scope obj.
Local Open Scope morph.

Section Sums.

  Context `{mos : MeasOps}.
  Context {los : LRnnOps (Σ:=Σ) LRnn}.
  Context {lps : LRnnProps LRnn}.
  
  Arguments Qnn_to_LRnn {U} {ccat} {cmc} {Σ} {LRnn} {_} _.
  
  
  Fixpoint parSum {Γ A} (n : nat) (f : nat -> Γ ~~> Meas A) : Γ ~~> Meas A :=
    match n with
    | O => zero
    | (S m) => Meas_add ∘ ⟨f m, parSum m f⟩
    end.

  Fixpoint parSum' {Γ} (n : nat) (f : nat -> Γ ~~> LRnn) : Γ ~~> LRnn :=
    match n with
    | O => LRnnzero _ ∘ tt
    | (S m) => LRnnplus _ ∘ ⟨f m, parSum' m f⟩
    end.

  Existing Instance sleq_Proper.

  Definition sum_family {Γ A : U} (f : nat -> Γ ~~> Meas A) : nat_family (Σ:=Σ) Γ (Meas A).
  Proof. unfold nat_family. exists (fun n => parSum n f).
         intros n. simpl.
         rewrite <- compose_id_left at 1.
         rewrite <- add_zero_left.
         rewrite <- compose_assoc, -> pair_f.
         apply compose_sleq; try apply sleq_reflexive.
         apply pair_sleq.
         rewrite zero_ext. apply zero_min.
         rewrite compose_id_left. apply sleq_reflexive.
  Defined.

  Definition sum_family' {Γ : U} (f : nat -> Γ ~~> LRnn) : nat_family (Σ:=Σ) Γ LRnn.
  Proof. unfold nat_family. exists (fun n => parSum' n f).
         intros n. simpl.
         rewrite <- compose_id_left at 1.
         pose (SRadd_0_l (Lrnnsemiring _ LRnn) id) as e.
         unfold ap2, ap0 in e. rewrite <- e. clear e.
         rewrite <- compose_assoc, -> pair_f.
         apply compose_sleq; try apply sleq_reflexive.
         apply pair_sleq.
         rewrite <- compose_assoc. rewrite -> (unit_uniq (tt ∘ _) tt).
         apply LRnnzerobot. apply lps.
         rewrite compose_id_left. apply sleq_reflexive.
  Defined.
  
  Definition sum {Γ A : U} (f : nat -> Γ ~~> Meas A) :=
    sup_nat_family (sum_family f).

  Definition sum' {Γ : U} (f : nat -> Γ ~~> LRnn) :=
    sup_nat_family (sum_family' f).

  Existing Instance MeasMonad.
  
  Definition coe : Qnn -> unit ~~> Meas unit :=
    fun q => Meas_scale ∘ ⟨Qnn_to_LRnn q, Ret tt⟩.

  Definition F : (unit ~~> Meas unit) -> (unit ~~> Meas unit). (* 1 + x/2 *)
    intros r.
    eapply compose. apply Meas_add.
    apply pair. exact (coe 1%Qnn).
    eapply compose. apply Meas_scale.
    apply pair. apply (Qnn_to_LRnn Qnnonehalf).
    apply r.
  Defined.

  Lemma F_Proper : Proper (sleq (Σ:=Σ) ==> sleq(Σ:=Σ)) F.
  Proof. unfold Proper, respectful.
         intros x y H. unfold F.
         apply compose_sleq; try apply sleq_reflexive.
         apply pair_sleq; try apply sleq_reflexive.
         apply compose_sleq; try apply sleq_reflexive.
         apply pair_sleq; try apply sleq_reflexive.
         assumption.
  Qed.

  Lemma F_Cont : Cont F F_Proper.
  Proof. unfold Cont.
         intros.
         unfold F at 1.
         rewrite pairR_Cont.
         rewrite postcompose_Cont.
         rewrite pairR_Cont.
         rewrite postcompose_Cont.
         apply sup_exacteq_sup.
         reflexivity. (* This could totally be automated. *)
  Qed.

  (* So F has a fixed point. *)

  Definition Two1 : unit ~~> Meas unit :=
    sfix F (ishas zero_min) F_Proper.

  (* On the other hand... *)

  Fixpoint expn (n : nat) : unit ~~> Meas unit := (* 2 to the minus n *)
    match n with
    | O => coe (1%Qnn)
    | (S m) => Meas_scale ∘ ⟨Qnn_to_LRnn Qnnonehalf, (expn m)⟩
    end.

  Definition Two2 : unit ~~> Meas unit :=
    sum expn.

  (* And of course *)
  Definition Two0 : unit ~~> Meas unit :=
    coe ((1+1)%Qnn).

  Notation "A + B" := (Meas_add ∘ ⟨A, B⟩).
  Notation "A ⨰ B" := (Meas_scale ∘ ⟨A, B⟩) (at level 40).

  Lemma relation12 : (forall n : nat, F (parSum n expn) == parSum (S n) expn).
  Proof.
          induction n.
      - simpl. unfold F. rewrite scale_zero. reflexivity.
      - unfold F. simpl. unfold F in IHn. simpl in IHn.
        (* we know 1 + (1/2) * pn == en + pn. 
           we want 1 + (1/2) * (en + pn) == (1/2) * en + (en + pn). *)
        rewrite scale_add at 1. 
        setoid_rewrite add_commute at 2.
        rewrite <- add_assoc. rewrite IHn.
        setoid_rewrite add_commute at 3. reflexivity.
  Qed.
  
  Lemma t1let2 : sleq (Σ:=Σ) Two1 Two2.
  Proof.
    apply sfix_min.
    unfold Two2. unfold sum.
    rewrite F_Cont.
    apply (sleq_eq (Σ:=Σ)).
    - apply sup_sleq_sup. simpl.
      intros n; exists (S n). rewrite relation12. apply sleq_reflexive.
    - apply sup_sleq_sup. simpl. 
      intros n; destruct n.
      + simpl. exists 0. apply zero_min.
      + exists n. rewrite relation12. apply sleq_reflexive.
  Qed.

  Lemma t2let1 : sleq (Σ:=Σ) Two2 Two1.
  Proof.
    unfold Two2, sum. apply sup_nat_family_prop.
    intros n. simpl.
    induction n.
    - simpl. apply zero_min.
    - rewrite <- relation12. unfold Two1. rewrite <- sfix_fix.
      apply F_Proper. apply IHn. apply F_Cont.
  Qed.

  Lemma t1let0 : sleq (Σ:=Σ) Two1 Two0.
  Proof. apply sfix_min.
         unfold F, Two0, coe.
         setoid_rewrite <- mult_scale.
         setoid_rewrite <- add_scale.
         apply compose_Proper; try reflexivity.
         apply pair_Proper; try reflexivity.
         (* I don't feel like learning how to add and multiply numbers, so I'll admit this for now. *)
         admit.
  Admitted.
         
        
End Sums.
