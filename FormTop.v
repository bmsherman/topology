Require Import Frame.

Module FormTop.

(** Inductively generated formal topologies *)

Section Defn.

Context {S : Type}.
Context {PO : PO.t S}.

Let le := PO.le PO.

Definition down (a b c : S) : Prop :=
  le c a /\ le c b.

Record t { Cov : S -> (S -> Prop) -> Prop } :=
  { refl : forall (a : S) (U : S -> Prop), U a -> Cov a U
  ; trans : forall (a : S) (U V : S -> Prop), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; le_left : forall (a b : S) (U : S -> Prop)
     , PO.le PO a b -> Cov b U -> Cov a U
  ; le_right : forall (a : S) (U V : S -> Prop)
    , Cov a U -> Cov a V
    -> Cov a (fun c => exists u v, U u /\ V v /\ down u v c)
  }.

Arguments t : clear implicits.

Variable Cov : S -> (S -> Prop) -> Prop.

Lemma monotone : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a -> V a)
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. eapply trans. eassumption. eassumption.
intros. apply H0 in H2. eapply refl. eassumption.
assumption.
Qed.

Lemma subset_equiv : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, Cov a U <-> Cov a V.
Proof.
intros. split; apply monotone; firstorder.
Qed.

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (S -> Prop).

Definition stable (Cov : S -> (S -> Prop) -> Prop) :=
  forall a b U V, Cov a U -> Cov b V
  -> forall c, le c a -> le c b ->
    Cov c (fun s => exists u v, U u /\ V v /\ down u v s).

Definition localized := forall (a c : S),
  le a c -> forall (i : I c),
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ down a u s).

Inductive GCov : S -> (S -> Prop) -> Prop :=
  | grefl : forall (a : S) (U : S -> Prop), U a -> GCov a U
  | gle_left : forall (a b : S) (U : S -> Prop)
     , le a b -> GCov b U -> GCov a U
  | ginfinity : forall (a : S) (i : I a) (U : S -> Prop),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Hypothesis loc : localized. 

Lemma gmonotone : forall (a : S) (U V : S -> Prop),
  (forall u, U u -> V u) -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gle_left. eassumption. apply IHGCov.
  assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gsubset_equiv : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; firstorder.
Qed.

Lemma le_infinity : forall (a c : S), le a c ->
  forall (i : I c) (U : S -> Prop), 
  (forall u v, C c i v -> down a v u -> GCov u U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros. destruct (loc a c H i).
apply (ginfinity _ x).
intros.
specialize (H1 u H2).
destruct H1. destruct H1.
eapply H0. 2:eassumption. assumption.
Qed.


Lemma GCov_stable : stable GCov.
Proof.
unfold localized in loc.
unfold stable. intros. generalize dependent c.
induction H.
- induction H0; intros.
  + apply grefl. exists a. exists a0. unfold down. intuition.
  + apply IHGCov. apply H2. 
    eapply PO.le_trans; eassumption.
  + pose proof (loc c a0 H3 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ j).

    intros. specialize (loc' u H4).
    destruct loc'. destruct H5. destruct H6.
    eapply H1. eassumption.
    eapply PO.le_trans. apply H6. assumption.
    assumption.
- intros. 
  apply IHGCov. eapply PO.le_trans. apply H2. apply H. 
  apply H3.
- intros. pose proof (loc c a H2 i) as loc1.
  destruct loc1 as [j loc'].
  apply (ginfinity _ j).

  intros. specialize (loc' u H4).
  destruct loc'. destruct H5. destruct H6.
  eapply H1. eassumption. assumption.
  eapply PO.le_trans. apply H6. assumption.
Qed.

Theorem GCov_formtop : t GCov.
Proof.
unfold localized in loc.
constructor.
- apply grefl.
- intros. induction H.
  + apply H0. assumption.
  + eapply gle_left. apply H. apply IHGCov.
    apply H0.
  + apply (ginfinity _ i). intros. apply H1; assumption.
- apply gle_left.
- intros.
  pose proof GCov_stable as stab.
  unfold stable in stab.
  eapply GCov_stable. eassumption. eassumption.
  apply PO.le_refl. apply PO.le_refl.
Qed.
  

End Defn.

End FormTop.