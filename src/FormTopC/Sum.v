Require Import Prob.StdLib FormTopC.FormTop Algebra.FrameC Algebra.SetsC 
  FormTopC.Cont.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Class HasBot {S : Type} {le : S -> S -> Type}
  {Cov : S -> Subset S -> Type}
  : Type :=
  { bot : S
  ; bot_le : forall {s : S}, le bot s
  ; bot_cov : forall (U : Subset S), Cov bot U
  }.

Arguments HasBot {S} le Cov : clear implicits.

(** Sum (coproduct) spaces

The space `A + B` has:

We require that both `A` and `B` have elements called `false` such 
that `false <| {}` (not always necessary in my definition of a 
formal topology!).

Basic opens `(a, b)` which means that either the point is in the 
left side in `a` or it is in the right side in `b`.

(a, b) <= (a', b')     iff  a<= a' and b <= b'

(a, b) <| { (a, false), (false, b) }
(a, false) <| { (u, false) | u in U}   (for each covering `a <| U` in A)
(false, b) <| { (false, v) | v in V}   (for each covering `b <| V` in B)

Pos(a, b)     iff    Pos(a) or Pos(b)

Note that the first rule (together with the preorder info) 
give us the equivalence
{(a, b)} = {(a, false), (b, false)}
which is key.
*)
Section Sum.

Context {S} {leS : S -> S -> Type}
  {IS : S -> Type} {CS : forall s, IS s -> Subset S}.
Context {T} {leT : T -> T -> Type}
  {IT : T -> Type} {CT : forall t, IT t -> Subset T}.

Context {SHasBot : HasBot leS (FormTop.GCov leS CS)}
        {THasBot : HasBot leT (FormTop.GCov leT CT)}.

Require Import FormTopC.Product.

Inductive IxUL : S * T -> Type := 
  | SplitIx : forall s t, IxUL (s, t)
  | LeftIx : forall {s}, IS s -> IxUL (s, bot)
  | RightIx : forall {t}, IT t -> IxUL (bot, t).

Arguments IxUL : clear implicits.

Inductive CUL : forall {p : S * T}, IxUL p -> Subset (S * T) :=
  | CSplitL : forall {s t}, In (CUL (SplitIx s t)) (s, bot)
  | CSplitR : forall {s t}, In (CUL (SplitIx s t)) (bot, t)
  | CLeft : forall {s} (ix : IS s) (s' : S), In (CS s ix) s' -> In (CUL (LeftIx ix)) (s', bot)
  | CRight : forall {t} (ix : IT t) (t' : T), In (CT t ix) t' -> In (CUL (RightIx ix)) (bot, t').

Arguments CUL : clear implicits.

Context {POS : PreO.t leS}. 
Context {POT : PreO.t leT}.

Definition le := prod_op leS leT.

Local Instance PO : PreO.t le := PreO.product POS POT.

Ltac inv H := inversion H; clear H; subst.


(** This isn't localized. I should just
    take its localization. *)
Local Instance loc : 
    FormTop.localized leS CS
  -> FormTop.localized leT CT
  -> FormTop.localized le CUL.
Proof.
intros H H0. unfold FormTop.localized.
intros a c H1 i. destruct H1 as (H1 & H2).
destruct a as [sa ta].
simpl in *.
destruct i.
- exists (SplitIx sa ta). intros.
  inv X. 
  + exists (s, bot). split. econstructor.
    split; split; simpl;
      (assumption || reflexivity || apply bot_le).
  + exists (bot, t). split. econstructor.
    split; split; simpl;
      (assumption || reflexivity || apply bot_le).
- unfold FormTop.localized in H.
  simpl in *.
  specialize (H sa s H1 i).
  destruct H as (i' & H).
Abort.

Definition Ix := FormTop.IxL le (Ix := IxUL).
Definition C := FormTop.CL le CUL.

Definition Cov := FormTop.GCov le C.

Existing Instance FormTop.Llocalized.

Local Instance isCov : FormTop.t (prod_op leS leT) Cov.
Proof.
apply FormTop.GCov_formtop.
Qed.

Let CovS := FormTop.GCov leS CS.
Let CovT := FormTop.GCov leT CT.

Section Overt.

Context {PosS : Subset S} {OvertS : FormTop.gtPos leS CS}.
Context {PosT : Subset T} {OvertT : FormTop.gtPos leT CT}.

Inductive PosSum : Subset (S * T) :=
  | LeftPos : forall {s t}, FormTop.gPos s -> PosSum (s, t)
  | RightPos : forall {s t}, FormTop.gPos t -> PosSum (s, t).

Local Open Scope Subset.


Lemma Overt : FormTop.gtPos (prod_op leS leT) C.
Proof.
unshelve econstructor.
- exact PosSum.
- intros. destruct b, X0, X. simpl in *.
  + left. eapply OvertS; eassumption.
  + right. eapply OvertT; eassumption.
- intros. destruct i.
  destruct x. simpl. admit.
- intros.
  apply (FormTop.trans (U := eq a ∩ PosSum)).
Admitted.

Existing Instance FormTop.GCov_formtop.

End Overt.

Inductive inl : Cont.map S (S * T) :=
  | MkInl : forall a b t, leS a b -> inl (b, t) a.

Lemma inl_cont : IGCont.t leS CovS le C inl.
Proof.
unshelve econstructor; intros.
- apply FormTop.grefl. exists (a, bot). unfold In.
  constructor. constructor. reflexivity.
- induction X. inv X0.
  apply FormTop.grefl. exists (a, bot).
  split; split; simpl; (reflexivity || assumption
    || solve[apply bot_le]).
  econstructor; reflexivity.
- induction X0. econstructor. etransitivity; eassumption.
- induction X. destruct X0, c. simpl in *.
   econstructor. etransitivity; eassumption.
- induction j. destruct x. simpl.
  induction X. induction i.
Abort.

End Sum.

(*
Section SumMaps.

Context {S} {leS : S -> S -> Type}
  {IS : S -> Type} {CS : forall s, IS s -> Subset S}.
Context {T} {leT : T -> T -> Type}
  {IT : T -> Type} {CT : forall t, IT t -> Subset T}.

Let CovS := FormTop.GCov leS CS.

Context {SHasBot : HasBot leS (FormTop.GCov leS CS)}
        {THasBot : HasBot leT (FormTop.GCov leT CT)}.
*)