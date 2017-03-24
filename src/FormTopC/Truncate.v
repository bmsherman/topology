(** Propositional truncation of spaces. *)

Require Import
  Coq.Classes.CMorphisms

  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  FormTopC.FormTop
  FormTopC.FormalSpace
  FormTopC.Cont.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Local Open Scope FT.

Section Truncate.

Variable A : IGt.

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

Definition A'PO : PreOrder :=
  {| PO_car := A
  ;  PreOrder.le := le
  |}.

Definition A' : PreISpace.t :=
  {| PreISpace.S := A'PO
   ; PreISpace.C := PreISpace.C A
  |}.

Lemma Cov_Refine : forall a U,
    a <|[A] U
   -> a <|[toPSL A'] U.
Proof.
intros. induction X.
- apply FormTop.glrefl. assumption.
- eapply FormTop.glle_left. constructor. eassumption.
  eassumption.
- 
Abort.

Local Instance Pos : FormTop.gtPos A'.
Proof.
unshelve econstructor.
- exact (FormTop.gPos (A := A)).
- intros. destruct X. eapply FormTop.gmono_le; eassumption.
  assumption. 
- intros.
Abort.

End Truncate.