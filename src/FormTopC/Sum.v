Require Import 
  Prob.StdLib 
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC 
  FormTopC.Cont
  FormTopC.Bundled.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Class HasBot {A : IGT}
  : Type :=
  { bot : S A
  ; bot_le : forall {s : S A}, le A bot s
  ; bot_cov : forall (U : Subset (S A)), Cov A bot U
  }.

Arguments HasBot : clear implicits.

Definition posIGT {A : IGT} (x : S A) := FormTop.gPos (gtPos := pos A) x.

Lemma bot_Pos (A : IGT) `(HasBot A) :
  posIGT bot -> False.
Proof. 
intros contra.
pose (FormTop.GCov_Pos (H :=pos A)).
pose proof (FormTop.mono bot (fun _ => False)).
cut (Inhabited ((fun _ : S A => False) ∩ FormTop.Pos)%Subset).
intros. destruct X0. destruct i. auto.
apply X. simpl. assumption.
apply bot_cov.
Qed.

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

Context {A B : IGT}.

Context {AHasBot : HasBot A}
        {BHasBot : HasBot B}.

Definition S' := (S A * S B)%type.

Inductive IxUL : S' -> Type := 
  | SplitIx : forall s t, IxUL (s, t)
  | LeftIx : forall {s}, Ix A s -> IxUL (s, bot)
  | RightIx : forall {t}, Ix B t -> IxUL (bot, t).

Arguments IxUL : clear implicits.

Inductive CUL : forall {p : S'}, IxUL p -> Subset S' :=
  | CSplitL : forall {s t}, In (CUL (SplitIx s t)) (s, bot)
  | CSplitR : forall {s t}, In (CUL (SplitIx s t)) (bot, t)
  | CLeft : forall {s} (ix : Ix A s) (s' : S A), In (C A s ix) s' -> In (CUL (LeftIx ix)) (s', bot)
  | CRight : forall {t} (ix : Ix B t) (t' : S B), In (C B t ix) t' -> In (CUL (RightIx ix)) (bot, t').

Arguments CUL : clear implicits.

Definition le' := prod_op (le A) (le B).

Existing Instances Bundled.IGT_Pos Bundled.IGT_PreO
  Bundled.IGTFT Bundled.local.

Local Instance PO : PreO.t le' := PreO.product _ _.

Ltac inv H := inversion H; clear H; subst.

(** This isn't localized. I should just
    take its localization. *)
Local Instance loc : FormTop.localized le' CUL.
Proof.
unfold FormTop.localized.
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
Abort.

Definition Ix' := FormTop.IxL le' IxUL.
Definition C' := FormTop.CL le' CUL.

Definition Cov := FormTop.GCov le' C'.

Existing Instance FormTop.Llocalized.

Local Instance isCov : FormTop.t le' Cov.
Proof.
apply FormTop.GCov_formtop.
Qed.

Inductive PosSum : Subset S' :=
  | LeftPos : forall {s t}, FormTop.gPos s -> PosSum (s, t)
  | RightPos : forall {s t}, FormTop.gPos t -> PosSum (s, t).

Local Open Scope Subset.

Local Instance Pos : FormTop.gtPos le' C'.
Proof.
unshelve econstructor.
- exact PosSum.
- intros. destruct b, X0, X. simpl in *.
  + left. eapply (pos A); eassumption.
  + right. eapply (pos B); eassumption.
- intros. destruct i.
  destruct l as [l l0]. destruct ix; simpl in l, l0.
  + destruct X; simpl in l, l0.
    * simpl. exists (s0, bot). unfold In. split.
    exists (s, bot). split. econstructor.
    split. split; simpl. reflexivity. apply bot_le.
    split; simpl. assumption. apply bot_le.
    econstructor 1. assumption.
    * simpl. exists (bot, t0). unfold In. split.
    exists (bot, t). split. econstructor.
    split. split; simpl. apply bot_le. reflexivity. 
    split; simpl. apply bot_le. assumption.
    econstructor 2. assumption.
  + destruct a as [sa ta]; simpl in l, l0.
    pose proof (FormTop.gmono_ax (gtPos := pos A) s i).
    inv X. 
    * destruct X0. eapply FormTop.gmono_le; eassumption.
      destruct i0. exists (a, ta). split. 2: econstructor 1; auto.
      exists (a, bot). split. econstructor.  assumption.
      split. admit. admit.
    * exfalso. eapply (bot_Pos B). eapply FormTop.gmono_le.
      eassumption. assumption.
  + admit.
- intros.
  apply (FormTop.trans (U := eq a ∩ PosSum)).
Admitted.

Existing Instance FormTop.GCov_formtop.

Definition Sum : IGT :=
  {| S := S'
  ; le := le'
  ; Ix := Ix'
  ; C := C' |}.

Inductive inl : Contmap A Sum :=
  | MkInl : forall a b t, le A a b -> inl (b, t) a.

Lemma inl_cont : IGContprf A Sum inl.
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
- induction j. destruct c. simpl.
  induction X.
Abort.

End Sum.