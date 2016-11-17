(** Propositional truncation of spaces. *)

Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.Bundled
  FormTopC.Cont
  Coq.Classes.CMorphisms.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Existing Instances Bundled.IGT_Pos Bundled.local
  Bundled.IGTFT Bundled.IGT_PreO.

Local Open Scope FT.

Section Truncate.

Variable A : IGT.

Inductive le {s t : A} : Type :=
  | Orig : s <=[A] t -> le
  | IPos : FormTop.gPos t -> le.

Arguments le : clear implicits.

Local Instance POSle : PreO.t le.
Proof.
econstructor.
- intros. apply Orig. reflexivity.
- intros. destruct X. destruct X0.
  apply Orig. etransitivity; eassumption.
  apply IPos. assumption. destruct X0. apply IPos. 
  eapply (FormTop.gmono_le); eassumption.
  apply IPos. eassumption.
Qed.

Definition A'PO : FormTop.PreOrder :=
  {| PO_car := A
  ;  FormTop.le := le
  |}.

Definition A'UL : PreISpace.t :=
  {| PreISpace.S := A'PO
   ; PreISpace.C := PreISpace.C A
  |}.

Definition A' := Localized A'UL.

Lemma Cov_Refine : forall a U,
    a <|[A] U
   -> a <|[A'] U.
Proof.
intros. induction X.
- apply FormTop.grefl. assumption.
- eapply FormTop.gle_left. constructor. eassumption.
  eassumption.
- 
Abort.

Local Instance Pos : FormTop.gtPos A'.
Proof.
unshelve econstructor.
- exact (FormTop.gPos (A := A)).
- intros. destruct X. eapply FormTop.gmono_le; eassumption.
  assumption. 
- intros. destruct i. simpl.
  destruct l.
  + destruct (localized A a c l ix).
    pose proof (FormTop.gmono_ax (A := A)
     a x) as H. simpl.
    specialize (H X). destruct H. destruct i.
    specialize (s a0 c0).
    destruct s. exists a0. split. 
    exists x0. destruct p. split. assumption.
    destruct d. split; apply Orig; assumption.
    assumption.
  + pose proof (FormTop.gmono_ax (A := A)
      c ix g). destruct X0.  destruct i. 
    exists a0. split. exists a0. split. assumption.
    split. apply IPos. assumption. reflexivity.
    assumption.
- intros.
  pose proof (FormTop.gpositive (A := A)
    a U).
Abort.

End Truncate.