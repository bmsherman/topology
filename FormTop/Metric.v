
Add Rec LoadPath "/Users/Sherman/Documents/Projects/corn/" as CoRN.
Require Import CoRN.reals.fast.CRtrans.

Module Metric.
Section Metric.
Hypothesis MS : MetricSpace.

Definition M : Type := msp_is_setoid MS.

Definition Ball : Type := (M * Qpos)%type.

Definition le_ball (Bx By : Ball) : Prop :=
  let (x, delta) := Bx in let (y, epsilon) := By in
  forall z, ball delta x z -> ball epsilon y z.

Require Import Frame.

Instance PreO : PreO.t le_ball.
Proof.
constructor; intros.
- destruct x. unfold le_ball. trivial.
- destruct x, y, z. unfold le_ball in *.
  intros. apply H0. apply H. assumption.
Qed.

Definition lt_ball (Bx By : Ball) : Prop :=
  le_ball Bx By /\ ~ le_ball By Bx.

Definition Ix (_ : Ball) : Type := option Qpos.

Definition C (b : Ball) (i : Ix b) : (Ball -> Prop) := 
  match i with
  | None         => fun b' => lt_ball b' b
  | Some epsilon => fun b' => snd b' = epsilon
  end.

Require Import FormTop.FormTop.

Definition IxL := @FormTop.IxL _ le_ball Ix.
Definition CL := @FormTop.CL _ le_ball Ix C.

Theorem loc : @FormTop.localized _ le_ball IxL CL.
Proof.
apply FormTop.Llocalized.
Qed.

End Metric.
End Metric.
