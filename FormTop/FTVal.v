Require Import LPReal Frame.
Local Open Scope LPR.

Module FinVal.

Generalizable All Variables.
Section Defn.
Context {S : Type} {leS : S -> S -> Prop}.

Record T (mu : S -> LPReal) :=
  { monotone : forall a b, leS a b -> mu a <= mu b
  ; modular : forall a b minab maxab,
      @PreO.min _ leS a b minab
    -> @PreO.max _ leS a b maxab
    -> mu a + mu b = mu minab + mu maxab
  }.

End Defn.
End FinVal.

Module JoinVal. 
Section Defn.

Context {S} {ops : Lattice.Ops S}.
Variable bot : S.
Hypothesis bok_ok : @PreO.bottom _ Lattice.le bot.

Definition extend (mu : S -> LPReal) (U : S -> Prop) : LPReal :=
  LPRsup (fun s : { t | U t } => mu (projT1 s)).

Hypothesis Cov : S -> (S -> Prop) -> Prop.

Record T (mu : S -> LPReal) :=
  { monotone : forall a U, Cov a U -> mu a <= extend mu U
  ; modular : forall (a b : S), mu a + mu b = 
     mu (Lattice.min a b) + mu (Lattice.max a b)
  }.

Inductive JoinClose (U : S -> Prop) : S -> Prop :=
  | In : forall a, U a -> JoinClose U a
  | Join : forall a b, JoinClose U a -> JoinClose U b
    -> JoinClose U (Lattice.max a b).

Require Import FormTop.FormTop.

Hypothesis Latt : Lattice.t S ops.

Instance JLS' : JoinLat.Ops S := Lattice.toJoinLatOps ops.

Instance JLS : JoinLat.t S JLS' := Lattice.toJoinLat Latt.

Instance MLS' : MeetLat.Ops S := Lattice.toMeetLatOps ops.

Instance MLS : MeetLat.t S MLS' := Lattice.toMeetLat Latt.

Hypothesis FTS : JoinTop.t bot Cov.

(* Lemma 1 in Roadmap *)
Lemma JoinCloseCov : forall (U V : S -> Prop), 
  (forall a, U a -> Cov a V) 
  -> forall a, JoinClose U a -> Cov a V.
Proof.
intros. induction H0. 
- apply H. assumption.
- apply (@JoinTop.join_left _ _ _ _ FTS); assumption.
Qed.

(* Lemma 2 in Roadmap *)
Lemma JoinCloseSubset : forall (U V : S -> Prop),
  (forall a, U a -> V a)
  -> forall a, JoinClose U a -> JoinClose V a.
Proof.
intros. induction H0.
- apply In. apply H. assumption.
- apply Join; assumption.
Qed.

(* Lemma 3 in Roadmap *)
Lemma JoinCloseMeetDistr : forall (U V : S -> Prop),
  forall a b, JoinClose U a -> JoinClose V b
  -> JoinClose (fun s => exists a' b', U a' /\ V b' /\ @FormTop.down _ MeetLat.le a' b' s) (MeetLat.min a b).
Proof.
intros. generalize dependent b. induction H; intros.
- induction H0. 
  + apply In. exists a. exists a0. split. assumption.
    split. assumption.
    split. apply MeetLat.min_l. apply MeetLat.min_r.
  + admit.
- admit.
Admitted.

Variable mu : S -> LPReal.
Hypothesis Tmu : T mu.

(* Lemma 5 of Roadmap *)
Lemma subsetMonotone : forall (U V : S -> Prop),
  (forall a, U a -> Cov a V)
  -> extend mu U <= extend mu V.
Proof.
intros. unfold extend at 1. apply LPRsup_le.
intros a. destruct a as (t & Ut). simpl.
apply (monotone _ Tmu). apply H. assumption.
Qed.

Lemma singleton : forall a, mu a = extend mu (Lattice.eq a).
Proof.
intros. apply LPRle_antisym.
apply (monotone _ Tmu). apply FormTop.refl. admit.
unfold extend. apply LPRsup_le.
intros a0. destruct a0 as (t & eqat). simpl.
admit.
Admitted.

Lemma monotone_le : forall a b, JoinLat.le a b
  -> mu a <= mu b.
Proof.
intros. rewrite !singleton.
apply subsetMonotone.
intros.
Admitted.

End Defn.

End JoinVal.