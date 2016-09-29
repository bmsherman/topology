Require Import
  FormTopC.FormTop 
  Algebra.SetsC
  Algebra.OrderC.

Module JoinTop.

Section JoinTop.
(** We assume we have some type [S] equipped
    with a partial order. *)
Context {S} {ops : JoinLat.Ops S} {JL : JoinLat.t S ops}.

Variable bot : S.
Variable Cov : S -> (Subset S) -> Type.


Class t : Type :=
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
intros. eapply FormTop.trans. apply X. clear X. clear a.
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
Require Import Coq.Lists.List Types.List.
Section Joinify.
Context {S} {le : S -> Subset S} {PO : PreO.t le}.

Definition leL (xs ys : list S) := forall x,
  member x xs -> { y : S & (le x y * member y ys)%type }.

Definition eqL (xs ys : list S) : Type := leL xs ys * leL ys xs.

Definition joinL (xs ys : list S) : list S := xs ++ ys.

Definition ops' : JoinLat.Ops (list S) :=
  {| JoinLat.le := leL
  ;  JoinLat.eq := eqL
  ;  JoinLat.max := joinL
  |}.

Instance ops : JoinLat.Ops (list S) := ops'.


Require Import CMorphisms.

Instance joinPreO : @PreO.t (list S) leL.
Proof.
constructor; intros.
- simpl. unfold leL. intros. exists x0.
  split. apply PreO.le_refl. assumption.
- simpl in *. unfold leL in *. intros. 
  destruct (X x0 X1). destruct p. 
  destruct (X0 x1 m). destruct p. 
  exists x2. split. eapply PreO.le_trans; eassumption.
  assumption.
Qed.

Instance joinPO : @PO.t (list S) leL JoinLat.eq.
Proof.
constructor.
- apply joinPreO.
- repeat intro.
  destruct X, X0. split; intros.
  transitivity x. assumption. transitivity x0; eassumption.
  transitivity y; try assumption. transitivity y0; eassumption.
- intros. split; assumption.
Qed. 

Lemma joinLE (xs ys xs' ys' : list S) : leL xs xs' -> leL ys ys'
  -> leL (xs ++ ys) (xs' ++ ys').
Proof.
unfold leL in *.
intros H H0 x H1.
apply member_app in H1.
destruct H1 as [In1 | In2].
- destruct (H x In1). exists x0. destruct p. 
  split. assumption. apply member_app. left. assumption. 
- destruct (H0 x In2). exists x0. destruct p. 
  split. assumption. apply member_app. right. assumption.
Qed.


Theorem JL : JoinLat.t (list S) ops.
Proof.
constructor.
- apply joinPO.
- repeat intro. simpl in *. unfold joinL.
  unfold eqL in *. destruct X, X0.
  auto using joinLE.
- intros. simpl. unfold joinL. constructor; unfold leL; intros.
  + exists x. split. apply PreO.le_refl. apply member_app. auto.
  + exists x. split. apply PreO.le_refl. apply member_app. auto.
  + apply member_app in X1. destruct X1; [apply X | apply X0]; assumption.
Qed.

Variable Cov : S -> (Subset S) -> Prop.

Definition LCov (a : list S) (U : Subset (list S)) :=
  forall s : S, member s a -> Cov s (fun s' => { xs : list S & (member s' xs * U xs)%type }).

Instance joinify : FormTop.t le Cov -> t nil LCov.
Proof.
intros FTS.
constructor.
- constructor.
  + unfold LCov. intros. apply FormTop.refl.
    exists a. split; assumption.
  + unfold LCov. intros. eapply FormTop.trans.
    eapply H. assumption. simpl.
    clear s X. intros.
    destruct X as (xs & Inxs & Uxs).
    eapply H0. eassumption. assumption.
  + simpl. unfold LCov. intros. unfold leL in *.
    specialize (X s X0). destruct X as (y & sy & Inyb).
    apply FormTop.le_left with y. assumption.
    apply H. assumption.
  + unfold LCov. intros.
    pose proof (fun (s' : S) (insa : member s' a) =>
      @FormTop.le_right _ _ _ _ s' _ _ (H s' insa) (H0 s' insa)).
    eapply FormTop.monotone. 2: apply (H1 s X). simpl.
    unfold Included, pointwise_rel, arrow; intros.
    destruct X0. destruct d, d0. unfold flip, SetsC.In in *.
    destruct i as (xs & Inxs & Uxs).
    destruct i0 as (ys & Inys & Vys).
    exists (cons a0 nil). split. left.
    constructor; (econstructor; [eassumption|]);
    unfold flip, leL; intros x' inx; simpl in inx; inv inx; subst;
    match goal with
    | [ H: member ?z ?xs  |- { y : _ & (_ * member y ?xs)%type } ] => exists z; split; auto
    end.
    inv X0. inv X0.
- unfold PreO.bottom. simpl. unfold leL. intros.
  inv X. 
- unfold LCov. intros. inv X.
- unfold LCov. simpl. unfold joinL. intros.
  apply member_app in X. destruct X.
  + apply H; assumption.
  + apply H0; assumption.
Qed.

End Joinify.

End JoinTop.
