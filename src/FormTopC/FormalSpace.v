Require Import
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.FormTop
  FormTopC.Cont
  CMorphisms.

Record t : Type :=
  { S : Type
  ; le : crelation S
  ; PO : PreO.t le
  ; Cov : S -> Subset S -> Type
  ; isFT : FormTop.t le Cov
  ; pos : FormTop.tPos Cov
  }.

Require FormTopC.Bundled.

Existing Instances Bundled.IGT_PreO Bundled.IGTFT.

Definition fromIGT (A : Bundled.IGT) : t :=
  {| S := Bundled.S A
   ; le := Bundled.le A
   ; Cov := Bundled.Cov A
   ; pos := FormTop.GCov_Pos (H := Bundled.pos A) |}.

Notation "a <|[ X ] U" := (Cov X a U) (at level 63, format "a  <|[ X ]  U").
Notation "a <=[ X ] b" := (le X a b) (at level 40, format "a  <=[ X ]  b").

Local Instance FT (A : t) : FormTop.t (le A) (Cov A)
  := isFT A.

Local Instance PreO (X : t) : PreO.t (le X) := PO X.

Definition Contmap (A B : t) := Cont.map (S A) (S B).
Definition Contprf (A B : t) := Cont.t (le A) (le B) (Cov A) (Cov B).


Section Properness.
Require Import CMorphisms.
Context {A : t}.

Definition le_left (a b : S A) (U : Subset (S A))
  : a <=[A] b -> b <|[A] U -> a <|[A] U.
Proof.
intros; eapply FormTop.le_left; eassumption.
Qed.

Local Open Scope Subset.

Definition monotone (U V : Subset (S A))
  : U ⊆ V -> forall a : S A, a <|[A] U -> a <|[A] V.
Proof.
apply FormTop.monotone.
Qed.

Instance Cov_Proper :
  Proper (le A --> Included ==> arrow) (Cov A).
Proof.
apply FormTop.Cov_Proper.
Qed.

(** This is just a flipped version of what's above. It
    shouldn't be needed. *)

Instance Cov_Proper3  :
  Proper (le A ==> Included --> flip arrow) (Cov A).
Proof.
apply FormTop.Cov_Proper3.
Qed.

Instance Cov_Proper2 : Proper (eq ==> Same_set ==> iffT) (Cov A).
Proof.
apply FormTop.Cov_Proper2.
Qed.

End Properness.
