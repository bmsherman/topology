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

Basic opens `inl a` for `a` a basic open in `A`, meaning that it
is in the left side (`A`), as well as basic opens `inr b` for
`b` a basic open in `B`.

inl a <= inl a'      if a <= a'
inr b <= inr b'      if b <= b'
Otherwise, x <= y is false.

inl a <| { inl u | u in U } (for each covering `a <| U` in A)
inr b <| { inr v | v in V } (for each covering `b <| V` in B)

Pos(inl a)    iff   Pos(a)
Pos(inr b)    iff   Pos(b)

*)
Section Sum.

Context {A B : IGT}.

Definition S' := (S A + S B)%type.

Inductive Ix' : S' -> Type := 
  | LeftIx : forall {s}, PreISpace.Ix A s -> Ix' (inl s)
  | RightIx : forall {t}, PreISpace.Ix B t -> Ix' (inr t).

Arguments Ix' : clear implicits.

Inductive C' : forall {p : S'}, Ix' p -> Subset S' :=
  | CLeft : forall {s} (ix : PreISpace.Ix A s) (s' : S A), 
      In (PreISpace.C A s ix) s' -> In (C' (LeftIx ix)) (inl s')
  | CRight : forall {t} (ix : PreISpace.Ix B t) (t' : S B), 
      In (PreISpace.C B t ix) t' -> In (C' (RightIx ix)) (inr t').

Arguments C' : clear implicits.

Inductive le' : S' -> S' -> Type := 
  | le'_L : forall (x y : A), x <=[A] y -> le' (inl x) (inl y)
  | le'_R : forall (x y : B), x <=[B] y -> le' (inr x) (inr y).

Existing Instances Bundled.IGT_Pos Bundled.IGT_PreO
  Bundled.IGTFT Bundled.local.

Ltac inv H := inversion H; clear H; subst.

Local Instance PO : PreO.t le'.
Proof.
econstructor; intros.
- destruct x; econstructor; reflexivity.
- destruct X; inv X0; econstructor; etransitivity; eassumption.
Qed.

Definition SumPreOrder : PreOrder := 
  {| PO_car := S'
   ; le := le'
  |}.

Definition SumPS : PreISpace.t :=
  {| PreISpace.S := SumPreOrder
   ; PreISpace.Ix := Ix'
   ; PreISpace.C := C'
  |}.

Local Instance loc : FormTop.localized SumPS.
Proof.
unfold FormTop.localized.
intros a c H1 i. destruct i.
- inv H1. destruct (localized A x s X i) as (i' & Hi').
  exists (LeftIx i'). simpl. intros. inv X0.
  assert (ix = i') by admit.
  subst. specialize (Hi' s' X1).
  destruct Hi' as (u & Pu1 & Pu2).
  exists (inl u). split. econstructor. assumption.
  destruct Pu2 as (dl & dr). split; econstructor; eassumption.
- inv H1. destruct (localized B x t X i) as (i' & Hi').
  exists (RightIx i'). simpl. intros. inv X0.
  assert (ix = i') by admit.
  subst. specialize (Hi' t' X1).
  destruct Hi' as (u & Pu1 & Pu2).
  exists (inr u). split. econstructor. assumption.
  destruct Pu2 as (dl & dr). split; econstructor; eassumption.
Admitted.

Existing Instance FormTop.Llocalized.

Local Instance isCov : FormTop.t SumPS.
Proof.
apply FormTop.GCov_formtop.
Qed.

Inductive PosSum : Subset S' :=
  | LeftPos : forall {s}, FormTop.gPos s -> PosSum (inl s)
  | RightPos : forall {t}, FormTop.gPos t -> PosSum (inr t).

Local Open Scope Subset.


Lemma cov1 : forall p U, GCov A p (fun l : A => U (inl l))
  ->  GCov SumPS (inl p) U.
Proof.
intros. remember (fun l : A => U (inl l)) as V.
induction X; subst.
- econstructor. eassumption.
- eapply gle_left. econstructor; eassumption. 
  apply IHX. reflexivity.
- apply ginfinity with (LeftIx i).
  intros. destruct u. apply X. inv X0. 
  assert (ix = i) by admit. subst. assumption.
  reflexivity. inv X0.
Admitted.

Lemma cov1' : forall p U, GCov SumPS (inl p) U 
  -> GCov A p (fun l : A => U (inl l)).
Proof.
intros. remember (inl p) as a.
induction X; subst.
- econstructor. eassumption.
Admitted.

Lemma cov2 : forall p U, GCov B p (fun l : B => U (inr l))
  ->  GCov SumPS (inr p) U.
Proof.
intros. remember (fun l : B => U (inr l)) as V.
induction X; subst.
- econstructor. eassumption.
- eapply gle_left. econstructor; eassumption. 
  apply IHX. reflexivity.
- apply ginfinity with (RightIx i).
  intros. destruct u. inv X0. inv X0. apply X. 
  assert (ix = i) by admit. subst. assumption.
  reflexivity. 
Admitted.

Lemma cov2' : forall p U, GCov SumPS (inr p) U 
  -> GCov B p (fun l : B => U (inr l)).
Proof.
intros. remember (inr p) as a.
induction X; subst.
- econstructor. eassumption.
Admitted.

Local Instance Pos : FormTop.gtPos SumPS.
Proof.
unshelve econstructor.
- exact PosSum.
- intros. destruct X; inv X0; econstructor; 
    eapply gmono_le; eassumption.
- intros. destruct i.
  + inv X. destruct (gmono_ax s i X0).
    destruct i0. econstructor.
    split; econstructor; eassumption.
  + inv X. destruct (gmono_ax t i X0).
    destruct i0. econstructor.
    split; econstructor; eassumption.
- intros. destruct a.
  + apply cov1. apply gpositive.
    intros. apply cov1'. apply X.  constructor. assumption. 
  + apply cov2. apply gpositive.
    intros. apply cov2'. apply X. constructor. assumption.
Admitted.

Existing Instance FormTop.GCov_formtop.

Definition Sum : IGT :=
  {| S := SumPS
  ; Bundled.PO := PO |}.

Inductive Inl : Cont.map A Sum :=
  | MkInl : forall a b, le A a b -> Inl (inl b) a.

Lemma inl_cont : IGCont.t A Sum Inl.
Proof.
unshelve econstructor; intros.
- apply FormTop.grefl. exists (inl a). unfold In.
  constructor. constructor. reflexivity.
- induction X. inv X0.
  apply FormTop.grefl. exists (inl a).
  split; constructor; assumption. constructor. reflexivity.
- induction X0. econstructor. etransitivity; eassumption.
- induction X. inv X0. econstructor. 
  etransitivity; eassumption.
- induction j. 
  + inv X. apply FormTop.le_left with s. 
    assumption. eapply ginfinity with i.
    intros. apply grefl. econstructor. econstructor. eassumption.
    econstructor. reflexivity.
  + inv X.
Qed.

End Sum.