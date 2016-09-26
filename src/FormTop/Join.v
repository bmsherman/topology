Require Import FormTop.FormTop 
  Algebra.Frame 
  Algebra.Sets 
  Coq.Program.Basics.
Module JoinTop.

Section JoinTop.
(** We assume we have some type [S] equipped
    with a partial order. *)
Context {S} {ops : JoinLat.Ops S} {JL : JoinLat.t S ops}.

Variable bot : S.
Variable Cov : S -> (Ensemble S) -> Prop.


Class t : Prop :=
  { FT :> FormTop.t JoinLat.le Cov
  ; bot_ok : @PreO.bottom _ JoinLat.le bot
  ; bot_Cov : forall U, Cov bot U
  ; join_left : forall a b U, Cov a U -> Cov b U -> Cov (JoinLat.max a b) U
  }.

Hypothesis FTS : t.
(** Check properties we expect to hold *)

Definition singleton (s s' : S) : Prop := s = s'.

Lemma join_right : forall a b c, Cov a (singleton b)
  -> Cov a (singleton (JoinLat.max b c)).
Proof.
intros. eapply FormTop.trans. apply H. clear H. clear a.
intros a sba. unfold singleton in sba. subst.
apply FormTop.le_left with (JoinLat.max a c).
apply JoinLat.max_ok.
apply FormTop.refl. unfold In in *. subst. reflexivity.
Qed.

End JoinTop.


(** Given a formal topology, we can always produce a join-closed formal
    topology by taking "free join" elements (i.e., the free monoid, a list)
    and interpreting the cover relation accordingly.
*)
Require Import Coq.Lists.List.
Section Joinify.
Context {S} {le : S -> Ensemble S} {PO : PreO.t le}.

Definition leL (xs ys : list S) : Prop := forall x,
  List.In x xs -> exists y, le x y /\ List.In y ys.

Definition eqL (xs ys : list S) : Prop := leL xs ys /\ leL ys xs.

Definition joinL (xs ys : list S) : list S := xs ++ ys.

Definition ops' : JoinLat.Ops (list S) :=
  {| JoinLat.le := leL
  ;  JoinLat.eq := eqL
  ;  JoinLat.max := joinL
  |}.

Instance ops : JoinLat.Ops (list S) := ops'.

Require Import Morphisms.

Instance joinPreO : @PreO.t (list S) JoinLat.le.
Proof.
constructor; intros.
- simpl. unfold leL. intros. exists x0.
  split. apply PreO.le_refl. assumption.
- simpl in *. unfold leL in *. intros. 
  destruct (H x0 H1). destruct H2. 
  destruct (H0 x1 H3). destruct H4. 
  exists x2. split. eapply PreO.le_trans; eassumption.
  assumption.
Qed.

Instance joinPO : @PO.t (list S) JoinLat.le JoinLat.eq.
Proof.
constructor.
- apply joinPreO.
- repeat intro. simpl in *.
  destruct H, H0. split;
  replace leL with JoinLat.le in * by reflexivity;
  eauto using (PreO.le_trans).
- intros. split; assumption.
Qed. 

Lemma joinLE : forall (xs ys xs' ys' : list S), leL xs xs' -> leL ys ys'
  -> leL (xs ++ ys) (xs' ++ ys').
Proof.
unfold leL in *.
intros.
apply in_app_iff in H1.
destruct H1 as [In1 | In2].
- destruct (H x In1). exists x0. rewrite in_app_iff. destruct H1. auto.
- destruct (H0 x In2). exists x0. rewrite in_app_iff. destruct H1. auto.
Qed.


Theorem JL : JoinLat.t (list S) ops.
Proof.
constructor.
- apply joinPO.
- repeat intro. simpl in *. unfold joinL.
  unfold eqL in *. destruct H, H0.
  auto using joinLE.
- intros. simpl. unfold joinL. constructor; unfold leL; intros.
  + exists x. split. apply PreO.le_refl. apply in_app_iff. auto.
  + exists x. split. apply PreO.le_refl. apply in_app_iff. auto.
  + apply in_app_iff in H1. destruct H1; [apply H | apply H0]; assumption.
Qed.

Variable Cov : S -> (Ensemble S) -> Prop.

Definition LCov (a : list S) (U : Ensemble (list S)) : Prop :=
  forall s : S, In s a -> Cov s (fun s' => exists xs, In s' xs /\ U xs).

Instance joinify : FormTop.t le Cov -> t nil LCov.
Proof.
intros FTS.
constructor.
- constructor.
  + unfold LCov. intros. apply FormTop.refl.
    exists a. split; assumption.
  + unfold LCov. intros. eapply FormTop.trans.
    eapply H. assumption. simpl.
    clear s H1. intros.
    destruct H1 as (xs & Inxs & Uxs).
    eapply H0. eassumption. assumption.
  + simpl. unfold LCov. intros. unfold leL in *.
    specialize (H s H1). destruct H as (y & sy & Inyb).
    apply FormTop.le_left with y. assumption.
    apply H0. assumption.
  + unfold LCov. intros.
    pose proof (fun (s' : S) (insa : In s' a) =>
      FormTop.le_right s' _ _ (H s' insa) (H0 s' insa)).
    eapply FormTop.monotone. 2: apply (H2 s H1). simpl.
    unfold Included, Ensembles.In; intros.
    destruct H3. destruct H3, H4. unfold flip, Ensembles.In in *.
    destruct H3 as (xs & Inxs & Uxs).
    destruct H4 as (ys & Inys & Vys).
    exists (cons x nil). split. unfold In. left. reflexivity.
    constructor; (econstructor; [eassumption|]);
    unfold flip, leL; intros x' inx; simpl in inx; destruct inx; subst;
    match goal with
    | [ H: In ?x ?xs  |- exists y, _ /\ In y ?xs ] => exists x; tauto
    end.
- unfold PreO.bottom. simpl. unfold leL. intros.
  apply in_nil in H. contradiction.
- unfold LCov. intros. apply in_nil in H. contradiction.
- unfold LCov. simpl. unfold joinL. intros.
  apply in_app_iff in H1. destruct H1.
  + apply H; assumption.
  + apply H0; assumption.
Qed.

End Joinify.

End JoinTop.
