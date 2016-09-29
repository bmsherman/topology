(** Propositional truncation of spaces. *)

Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.Cont
  Coq.Classes.CMorphisms.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Section Truncate.

Context {S} {leS : crelation S} 
  {POS : PreO.t leS}
  {IxS : S -> Type}
  {CS : forall a, IxS a -> Subset S}
  {locS : FormTop.localized leS CS}
  {OvertS : FormTop.gtPos leS CS}.

Let CovS := FormTop.GCov leS CS.

Inductive le {s t : S} : Type :=
  | Orig : leS s t -> le
  | IPos : FormTop.gPos t -> le.

Arguments le : clear implicits.

Local Instance POSle : PreO.t le.
Proof.
econstructor.
- intros. apply Orig. reflexivity.
- intros. destruct X. destruct X0.
  apply Orig. etransitivity; eassumption.
  apply IPos. assumption. destruct X0. apply IPos. 
  eapply (FormTop.gmono_le (gtPos := OvertS)); eassumption.
  apply IPos. eassumption.
Qed.

Definition C := FormTop.CL le CS.

Lemma Cov_Refine : forall a U,
    FormTop.GCov leS CS a U
   -> FormTop.GCov le C a U.
Proof.
intros. induction X.
- apply FormTop.grefl. assumption.
- eapply FormTop.gle_left. constructor. eassumption.
  eassumption.
- 
Abort.

Local Instance Overt : FormTop.gtPos le C.
Proof.
unshelve econstructor.
- exact (FormTop.gPos (gtPos := OvertS)).
- intros. destruct X. eapply FormTop.gmono_le; eassumption.
  assumption. 
- intros. destruct i. simpl.
  destruct l.
  + destruct (locS a c l ix).
    pose proof (FormTop.gmono_ax (gtPos := OvertS)
     a x) as H. simpl.
    specialize (H X). destruct H. destruct i.
    specialize (s a0 c0).
    destruct s. exists a0. split. 
    exists x0. destruct p. split. assumption.
    destruct d. split; apply Orig; assumption.
    assumption.
  + pose proof (FormTop.gmono_ax (gtPos := OvertS)
      c ix g). destruct X0.  destruct i. 
    exists a0. split. exists a0. split. assumption.
    split. apply IPos. assumption. reflexivity.
    assumption.
- intros.
  pose proof (FormTop.gpositive (gtPos := OvertS)
    a U).
  eapply FormTop.trans.
Abort.

End Truncate.