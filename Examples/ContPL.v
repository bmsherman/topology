Require Import Prob.ContPL.
Require Import Spec.Category Spec.Real Spec.Sierpinski Spec.Prob Spec.Sum.

Section LangExample.

Import Category.
Import Prob.
Import Real.
Import Sum.
Import Sierp.


Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope obj.
Local Open Scope morph.

Context {U : Type}.
Context `{mops : MeasOps U}.
Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) U 
   (LRnn := LRnn)}.
Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (R := R)
  (Σ := Σ)}.
Context {sumops : SumOps}.
Context `{sigmaops : ΣOps (U := U) (ccat := ccat) (cmc := cmc)
  (Σ := Σ)}.


Definition sum_match {Γ A B C}
  (e : Γ ~~> A + B)
  (l : Γ * A ~~> C) (r : Γ * B ~~> C) : Γ ~~> C :=
  sum_elim l r ∘ (id ⊗ e) ∘ diagonal.

Notation "'If' cond 'Then' thenExp 'Else' elseExp" :=
  (sum_match (cond)%morph (LAM _ => thenExp ∘ fst)%morph (LAM _ => elseExp ∘ fst)%morph) (at level 160) : morph_scope.

Definition bool := unit + unit.
Definition btrue : unit ~~> bool := inl ∘ tt.
Definition bfalse : unit ~~> bool := inr ∘ tt.
Definition band : bool * bool ~~> bool :=
  sum_elim (inl ∘ tt) fst.

Infix "&&" := (ap2 band).

Infix "+" := (ap2 (Rplus R)) : morph_scope.
Infix "*" := (ap2 (Rmult R)) : morph_scope.
Notation "0" := (ap0 (Rzero R)) : morph_scope.
Notation "1" := (ap0 (Rone R)) : morph_scope.

Fixpoint constR {Γ} (n : nat) : Γ ~~> R := match n with
  | 0%nat => 0
  | S n' => (1 + constR n')%morph
  end.

Definition exampleFun : [bool; R; R] ~> R :=
  makeFun [bool; R; R] (fun Γ b x y => 
   let z := (x * x)%morph in 
   If b && b
     Then z + constR 3
     Else x + (x * y) + z).

Definition example2 : [R] ~> R :=
  makeFun [R] (fun Γ x => let f := Call exampleFun (ap0 btrue) x in
      f (constR 5) + f x)%morph.

Definition squareAndAdd : R ~~> R := makeFun1 (fun _ x => x * x + x)%morph.

Local Instance smd : SMonad U Prob := ProbMonad.

Definition exampleProgram {Γ} : Γ ~~> Prob R :=
  x <- ap0 normal;
  b <- ap0 coinflip;
  If b
    Then Ret (!x)
    Else
      y <- ap0 normal;
      Ret (!x + !y).

Require Import Spec.Stream.
Import Stream.

Context `{StreamOps (U := U) (ccat := ccat) (Stream := Stream)}.

Infix "-" := (ap2 (Rsub R)) : morph_scope.

Definition ornstein : [R; R] ~> Prob (Stream R) :=
  makeFun [R; R] (fun _ θ σ => let σ2 := σ * σ in
     pstream (MeasOps := mops) (Ret 0) (LAM x =>
        (z <- ap0 normal 
        ; Ret ( (1 - !θ) * !x + !σ2 * !z))))%morph.

Definition peval {A} : (Prob A * Open A ~~> LRnn)%obj :=
  MeasEval ∘ ((SubProb_to_Meas ∘ Prob_to_SubProb) ⊗ id).

Context `{OpenOps (U := U) (ccat := ccat) (Σ := Σ) (Open := Open)}.

Infix "<" := (ap2 (Rlt R)).
Infix "/\" := (ap2 and).

(** This seems to cause a Coq bug in v8.5...
Definition ornstein_prob : [R; R] ~> LRnn :=
  makeFun [R; R] (fun _ θ σ =>
  ap2 peval (Call ornstein θ σ)
     (open_abstract (LAM x => ap1 hd x < 0  /\  1 < ap1 hd (ap1 tl x))))%morph.
*)


End LangExample.