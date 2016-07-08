Require Import Spec.Category.

Import Category.

Local Open Scope obj.
Local Open Scope morph.

Module Real.

Section Defn.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.

Section Ring.

Context {R : U}.
Variable zero one : unit ~~> R.
Variable plus mult : R * R ~~> R.

Require Import Coq.setoid_ring.Ring_theory.

Definition SemiRing : Prop :=
  forall Γ, @semi_ring_theory (Γ ~~> R) (ap0 zero) (ap0 one)
     (ap2 plus) (ap2 mult) eq.

Variable sub : R * R ~~> R.
Variable opp : R ~~> R.

Definition Ring : Prop :=
  forall Γ, @ring_theory (Γ ~~> R) (ap0 zero) (ap0 one)
     (ap2 plus) (ap2 mult) (ap2 sub) (ap1 opp) eq.

End Ring.

Require Import Numbers.Qnn Spec.Discrete Spec.Sierpinski QArith.
Local Close Scope Q.
Import Discrete.
Import Sierp.

Variable D : Type -> U. Variable pow : Type -> U -> U.
Context {dops : DiscreteOps D pow}.
Context `{sigops : ΣOps (U := U) (ccat := ccat) (cmc := cmc)}.

(** Real numbers *)
Variable R : U.
Class ROps : Type :=
  { Q_to_R : Q -> unit ~~> R
  ; Rplus : R * R ~~> R
  ; Rmult : R * R ~~> R
  ; Ropp : R ~~> R
  ; Rlt : R * R ~~> Σ
  ; Rmin : R * R ~~> R
  ; Rmax : R * R ~~> R
  }.

Context `{ROps}. 

Definition Rsub : R * R ~~> R := Rplus ∘ (id ⊗ Ropp).
Definition Rzero : unit ~~> R := Q_to_R 0%Q.
Definition Rone : unit ~~> R := Q_to_R 1%Q.

Class RProps : Prop :=
  { Rring : Ring Rzero Rone Rplus Rmult Rsub Ropp
  }.

(** Non-located real numbers *)
Variable RNL : U.
(** I probably need to replace "D Q", the discrete space
    over the rationals, with something that enforces the
    setoid structure of Q. *)
Class RNLOps : Type :=
  { R_to_RNL : R ~~> RNL
  ; RNLplus : RNL * RNL ~~> RNL
  ; RNLmult : RNL * RNL ~~> RNL
  ; RNLopp : RNL ~~> RNL
  ; RNLmin : RNL * RNL ~~> RNL
  ; RNLmax : RNL * RNL ~~> RNL
  ; RNLind : Σ ~~> RNL
  }.

Context `{RNLOps}.
Definition RNLsub : RNL * RNL ~~> RNL := RNLplus ∘ (id ⊗ RNLopp).
Definition RNLzero : unit ~~> RNL := R_to_RNL ∘ Rzero.
Definition RNLone : unit ~~> RNL := R_to_RNL ∘ Rone.

Class RNLProps : Prop :=
  { RNLring : Ring RNLzero RNLone RNLplus RNLmult RNLsub RNLopp
  }.

(** Non-negative lower reals *)
Variable LRnn : U.

Class LRnnOps : Type :=
  { LRnnplus : LRnn * LRnn ~~> LRnn
  ; LRnnmult : LRnn * LRnn ~~> LRnn
  ; Qnn_to_LRnn : Qnn -> unit ~~> LRnn
  ; LRnninf : unit ~~> LRnn
  ; LRnnmin : LRnn * LRnn ~~> LRnn
  ; LRnnmax : LRnn * LRnn ~~> LRnn
  ; LRnnind : Σ ~~> LRnn
  }.

Context `{LRnnOps}.
Definition LRnnzero : unit ~~> LRnn := Qnn_to_LRnn 0%Qnn.
Definition LRnnone : unit ~~> LRnn := Qnn_to_LRnn 1%Qnn.

Class LRnnProps : Prop :=
  { Lrnnsemiring : SemiRing LRnnzero LRnnone LRnnplus LRnnmult
  }.

(** Lower reals *)

Variable LR : U.
Class LROps : Type :=
  { LRnn_inj : LRnn ~~> LR
  ; RNL_inj : RNL ~~> LR
  ; LRplus : LR * LR ~~> LR
  ; LRmin : LR * LR ~~> LR
  ; LRmax : LR * LR ~~> LR
  }.

End Defn.

End Real.