Require Import Spec.Category Spec.Sup Spec.Sierpinski.

Import Category Sup Sierp.

Local Open Scope obj.
Local Open Scope morph.

Module Real.

Section Defn.

Context {U : Type} {ccat : CCat U} {cmc : CMC U} {Σ:U}{Σos:ΣOps (Σ:=Σ)}.

Axiom SemiRing : forall R (zero one : unit ~~> R)
  (plus mult : R * R ~~> R), Type. 
Axiom Ring : forall R (zero one : unit ~~> R)
  (plus mult sub : R * R ~~> R)
  (opp : R ~~> R), Type. 

Require Import Numbers.Qnn Spec.Discrete Spec.Sierpinski QArith.
Local Close Scope Q.
Import Discrete.
Import Sierp.

Variable D : Type -> U.
Context {dops : DiscreteOps D}.
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

Class RProps : Type :=
  { Rring : Ring _ Rzero Rone Rplus Rmult Rsub Ropp
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

Class RNLProps : Type :=
  { RNLring : Ring _ RNLzero RNLone RNLplus RNLmult RNLsub RNLopp
  }.

(** Non-negative lower reals *)
Variable LRnn : U.

Require Import CMorphisms.

Class LRnnOps : Type :=
  { LRnnplus : LRnn * LRnn ~~> LRnn
  ; LRnnmult : LRnn * LRnn ~~> LRnn
  ; Qnn_to_LRnn : Qnn -> unit ~~> LRnn
  ; LRnninf : unit ~~> LRnn
  ; LRnnmin : LRnn * LRnn ~~> LRnn
  ; LRnnmax : LRnn * LRnn ~~> LRnn
  ; LRnnind : Σ ~~> LRnn
  ; LRnnlt : forall {Γ}, Γ ~~> LRnn -> Γ ~~> LRnn -> Type
  ; LRnnlt_Proper : forall {Γ}, Proper (eq (A:=Γ) ==> eq ==> iffT) LRnnlt
  }.

Context `{LRnnOps}.
Definition LRnnzero : unit ~~> LRnn := Qnn_to_LRnn 0%Qnn.
Definition LRnnone : unit ~~> LRnn := Qnn_to_LRnn 1%Qnn.
Definition LRnnonehalf : unit ~~> LRnn := Qnn_to_LRnn Qnnonehalf.

Class LRnnProps : Type :=
  { Lrnnsemiring : SemiRing _ LRnnzero LRnnone LRnnplus LRnnmult
  ; LRnnzerobot : forall {Γ}, isBot (Σ:=Σ) (LRnnzero ∘ (tt(Γ:=Γ)))
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