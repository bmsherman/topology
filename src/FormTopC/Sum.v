Require Import 
  Prob.StdLib
  Types.UIP
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC 
  Algebra.PreOrder
  FormTopC.Cont
  FormTopC.FormalSpace.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Local Open Scope FT.

Class HasBot {A : IGt}
  : Type :=
  { bot : S A
  ; bot_le : forall {s : S A}, le A bot s
  ; bot_cov : forall (U : Subset (S A)), bot <|[A] U
  }.

Arguments HasBot : clear implicits.

Definition posIGT {A : IGt} (x : S A) := FormTop.gPos (gtPos := IGpos A) x.

Lemma bot_Pos (A : IGt) `(HasBot A) :
  posIGT bot -> False.
Proof. 
intros contra.
pose (FormTop.GCov_Pos (H :=IGpos A)).
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

Context {Ix : Type}.
Context {Ix_UIP : EqdepFacts.UIP_ Ix}.
Context {A : Ix -> IGt}.

Definition S' := SomeOpen A.

Definition SomeOpen := MkSomeOpen (X := A).

Inductive Ix' : S' -> Type := 
  | MkIx : forall {ix : Ix} {s : A ix}, PreISpace.Ix (A ix) s -> 
       Ix' (SomeOpen ix s).

Arguments Ix' : clear implicits.

Inductive InDisjunct {ix : Ix} {U : Open (A ix)} : Subset S' :=
  | MkInDisjunct : forall s : A ix, In U s -> In InDisjunct (SomeOpen ix s).

Arguments InDisjunct {ix} U.

Definition C' (p : S') (ix : Ix' p) : Subset S' := match ix with
  | MkIx ix s ax => InDisjunct (PreISpace.C (A ix) s ax)
  end.

Definition le' : S' -> S' -> Type := SomeOpen_le (X := A).

Definition SumPreOrder : PreOrder := 
  {| PO_car := S'
   ; le := le'
  |}.

Local Instance PO : PreO.t (le SumPreOrder). 
Proof.
unshelve eapply Sum_PO; eassumption.
Qed.


Definition SumPS : PreISpace.t :=
  {| PreISpace.S := SumPreOrder
   ; PreISpace.Ix := Ix'
   ; PreISpace.C := C'
  |}.

Local Instance loc 
  (locA : forall ix, localized (A ix)) : FormTop.localized SumPS.
Proof.
unfold FormTop.localized.
intros a c H1 i. destruct i.
UIP_inv H1. 
destruct (locA ix aix0 s X i) as (i' & Hi').
exists (MkIx i').
intros u X0. simpl in X0. UIP_inv X0.
specialize (Hi' s0 X1). destruct Hi'. le_downH d.
split. le_down. 
simpl. constructor. assumption.
destruct d0. eexists. econstructor. eassumption.
econstructor. eassumption.
Qed.

Inductive PosSum : Subset S' :=
  | MkPos : forall (ix : Ix) {s : A ix}, FormTop.gPos s -> PosSum (SomeOpen ix s).

Local Open Scope Subset.

Lemma cov1 : forall ix p U,  p <|[A ix] (fun l : A ix => U (SomeOpen ix l))
  -> SomeOpen ix p <|[toPSL SumPS] U.
Proof.
intros. remember (fun l : A ix => U (SomeOpen ix l)) as V.
induction X; subst.
- econstructor. eassumption.
- eapply glle_left. econstructor; eassumption. 
  apply IHX. reflexivity.
- apply gle_infinity with (SomeOpen ix b) (MkIx i).
  constructor. assumption.
  intros u Pu. destruct u. 
  destruct Pu. le_downH d.
  UIP_inv d. apply X. 2: reflexivity.
  split. le_down. assumption.
  destruct d0. destruct a0.
  simpl in l0. UIP_inv l0. UIP_inv i0.
  eexists; eassumption.
Qed.

Lemma cov1' : forall ix p U, SomeOpen ix p <|[toPSL SumPS] U
  -> p <|[A ix] (fun l : A ix => U (SomeOpen ix l)).
Proof.
intros. remember (SomeOpen ix p) as a.
generalize dependent ix.
induction X; intros; subst.
- econstructor. eassumption.
- UIP_inv l. eapply FormTop.glle_left. 
  eassumption. apply IHX.
  reflexivity.
- UIP_inv l.
  remember ({| SOIx := ix; SOOpen := bix |}) as u.
  induction i. 
  UIP_inv Hequ.
  eapply FormTop.gle_infinity with bix i.
  assumption. intros. 
  eapply X. 2:reflexivity.
  destruct X1 as (d & d0).
  split. le_down. constructor. le_downH d.
  assumption.
  destruct d0 as [u' Pu' lu'].
  exists (SomeOpen ix u').
  unfold In. simpl.
  econstructor. assumption.
  econstructor. assumption.
Qed.

Local Instance Pos : FormTop.gtPos SumPS.
Proof.
unshelve econstructor.
- exact PosSum.
- intros. induction X. UIP_inv X0.
    constructor. eapply gmono_le; eassumption.
- intros. destruct i.
  + UIP_inv X0. UIP_inv X.
    destruct (gmono_ax (A := A ix) s i s0 X0 X1).
    destruct i0. destruct d. le_downH d.
    exists (SomeOpen ix a). split. split. 
    le_down. constructor. assumption.
    destruct d0.
    eexists. econstructor. eassumption.
    constructor. assumption.
    econstructor. assumption.
- intros. destruct a.
  + apply cov1. apply gpositive.
    intros. apply cov1'. apply X. constructor. assumption. 
Qed.

Definition Sum : IGt :=
  {| IGS := SumPS
  ; IGPO := PO |}.

Inductive Inj (ix : Ix) : Cont.map (A ix) Sum :=
  | MkInj : forall a b, a <=[A ix] b -> Inj ix (SomeOpen ix b) a.

Lemma Inj_cont (ix : Ix) : IGCont.t (A ix) Sum (Inj ix).
Proof.
unshelve econstructor; intros.
- apply FormTop.refl. exists (SomeOpen ix a). unfold In.
  constructor. constructor. reflexivity.
- induction X. inv X0.
  apply FormTop.refl. exists (SomeOpen ix a).
  split; le_down; constructor; assumption. constructor. reflexivity.
- induction X0. econstructor. etransitivity; eassumption.
- induction X. UIP_inv X0. econstructor. 
  etransitivity; eassumption.
- induction j. 
  UIP_inv X0. UIP_inv X. 
  apply FormTop.gle_infinity with s i.
  etransitivity; eassumption.
  intros. apply FormTop.glrefl.
  destruct X. le_downH d. destruct d0.
  exists (SomeOpen ix0 u). split. le_down.
  constructor. transitivity a; assumption.
  exists (SomeOpen ix0 a0). constructor. assumption.
  constructor. assumption.
  constructor. reflexivity.
Qed.

End Sum.