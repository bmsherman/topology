Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.Cont
  CMorphisms.

Record t : Type :=
  { S :> PreSpace.t
  ; PO : PreO.t (le S)
  ; isFT : FormTop.t S
  ; pos : FormTop.tPos S
  }.

Local Open Scope FT.


Require FormTopC.Bundled.

Existing Instances Bundled.IGT_PreO Bundled.IGTFT.

Definition fromIGT (A : Bundled.IGT) : t :=
  {| S := Bundled.S A
   ; pos := FormTop.GCov_Pos (H := Bundled.pos A) |}.

Local Instance FT (A : t) : FormTop.t A := isFT A.
Local Instance PreO (X : t) : PreO.t (le X) := PO X.

Section Properness.
Require Import CMorphisms.
Context {A : t}.

Definition refl a U : In U a -> a <|[A] U.
Proof.
auto using FormTop.refl.
Qed.

Definition le_left (a b : S A) (U : Open A)
  : a <=[A] b -> b <|[A] U -> a <|[A] U.
Proof.
intros; eapply FormTop.le_left; eassumption.
Qed.

Definition trans {a U} :
  a <|[A] U -> forall V, U <<|[A] V -> a <|[A] V.
Proof.
intros. eapply FormTop.trans; eassumption.
Qed.

Local Open Scope Subset.

Definition le_right {a U V} :
  a <|[A] U -> a <|[A] V ->
  a <|[A] ⇓ U ∩ ⇓ V.
Proof.
auto using FormTop.le_right.
Qed.

Definition monotone (U V : Subset (S A))
  : U ⊆ V -> forall a : S A, a <|[A] U -> a <|[A] V.
Proof.
apply FormTop.monotone.
Qed.

Instance Cov_Proper :
  Proper (le A --> Included ==> arrow) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper.
Qed.

(** This is just a flipped version of what's above. It
    shouldn't be needed. *)

Instance Cov_Proper3  :
  Proper (le A ==> Included --> flip arrow) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper3.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) (PreSpace.Cov A).
Proof.
apply FormTop.Cov_Proper2.
Qed.

End Properness.

Ltac trans H := apply (trans H); let T := type of H in 
  match constr:(T) with
  | _ _ ?a _ => clear a H; intros a H
  end.

Ltac etrans := match goal with
     | [ H : ?Cov ?X ?a _  |- ?Cov ?X ?a _ ] => try (trans H)
     end.

Ltac join H1 H2 := let H := fresh H1 in
  pose proof (le_right H1 H2) as H; clear H1 H2.

Ltac ejoin := repeat match goal with
  | [ H1 : ?Cov ?A ?a _, H2 : ?Cov ?A ?a _  |- ?Cov ?A ?a _ ] => join H1 H2
  end.