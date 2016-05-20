Require Import FormTop.FormTop Frame Algebra.Sets 
  Coq.Program.Basics.

Local Open Scope Ensemble.

(** Formal topologies presented with a minimum operation
    rather than just a partial order. Most of the material
    is pretty similar to the module above.

    One good reference for this presentation is

    [2]
    Formal topology and domains.
    Giovanni Sambin.
    2000.
    http://www.math.unipd.it/~sambin/txt/ftd.pdf
 *)
Module FormTopM.

Generalizable All Variables.

Section Defn.
Context {S} {dotS : S -> S -> S}.

Definition ops : MeetLat.Ops S :=
  {| MeetLat.le := fun x y => dotS x y = x
   ; MeetLat.eq := eq
   ; MeetLat.min := dotS
  |}.

Instance ops' : MeetLat.Ops S := ops.

Definition le := MeetLat.le.
Definition dot := MeetLat.min.

Context {ML : MeetLat.t S ops}.

Definition dotset (U V : Ensemble S) : Ensemble S :=
  union U (fun u => union V (fun v c => MeetLat.eq c (dot u v))).

Class t { Cov : S -> (Ensemble S) -> Prop } :=
  { refl : forall (a : S) (U : Ensemble S), U a -> Cov a U
  ; trans : forall (a : S) (U V : Ensemble S), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; dot_left : forall (a b : S) (U : Ensemble S)
     , Cov a U -> Cov (dot a b) U
  ; dot_right : forall (a : S) (U V : Ensemble S)
    , Cov a U -> Cov a V
    -> Cov a (dotset U V)
  }.

Arguments t : clear implicits.

Lemma monotone {Cov} : t Cov
  -> forall (U V : Ensemble S)
  , U ⊆ V
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. unfold Included, In in H0. eauto using trans, refl.
Qed.

Lemma subset_equiv {Cov} : t Cov
  -> forall (U V : Ensemble S)
  , (forall a : S, U a <-> V a)
  -> forall a, Cov a U <-> Cov a V.
Proof.
intros. split; apply monotone; firstorder.
Qed.

Definition asFormTop `(tCov : t Cov) : FormTop.t le Cov.
Proof.
constructor; intros.
- apply refl. assumption.
- eapply trans. eassumption. assumption.
- assert (MeetLat.min a b = a). apply (PO.le_antisym (le := MeetLat.le)). 
  + apply (@PreO.min_l _ _ _ b).
    apply MeetLat.min_ok.
  + apply (@PreO.min_greatest _ _ a b).
    apply MeetLat.min_ok. apply PreO.le_refl. assumption.
  + rewrite <- H1. rewrite MeetLat.min_comm. 
    apply dot_left. assumption. 
- pose (UV := dotset U V).
  apply monotone with UV. assumption.
  unfold UV. unfold Included, In; intros.
  destruct H1. destruct H2.
  constructor; [constructor 1 with a0 | constructor 1 with a1];
    try eassumption.
  unfold flip. rewrite H3. apply MeetLat.min_l.
  unfold flip. rewrite H3. apply MeetLat.min_r.
  unfold UV. apply dot_right; assumption.
Qed.

(** Inductively generated formal topologies for this formulation. *)

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (Ensemble S).

Definition stable (Cov : S -> (Ensemble S) -> Prop) :=
  forall a b U V, Cov a U -> Cov b V
  -> Cov (dot a b) (dotset U V).

Definition localized := forall (b c : S),
  forall (i : I c), let a := dot b c in
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ MeetLat.le s (dot a u)).

Inductive GCov : S -> (Ensemble S) -> Prop :=
  | grefl : forall (a : S) (U : Ensemble S), U a -> GCov a U
  | gdot_left : forall (a b : S) (U : Ensemble S)
     , GCov a U -> GCov (dot a b) U
  | ginfinity : forall (a : S) (i : I a) (U : Ensemble S),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Hypothesis loc : localized.

Lemma localized_asFormTop : FormTop.localized MeetLat.le C.
Proof.
unfold FormTop.localized, localized in *.
intros.
specialize (loc a c i).
unfold dot, MeetLat.min in *. simpl in *.
rewrite H in loc.
destruct loc.
exists x. intros. specialize (H0 s H1).
destruct H0. exists x0. destruct H0. split. assumption.
unfold FormTop.down.
unfold dot in x. simpl in x.
change dotS with (MeetLat.min) in *.
change (@eq S) with (MeetLat.eq) in *.
split.
apply PO.le_antisym. apply MeetLat.min_l. apply MeetLat.min_ok.
apply PreO.le_refl. rewrite <- H2. rewrite MeetLat.min_comm.
rewrite <- MeetLat.min_assoc. apply MeetLat.min_l.
apply PO.le_antisym. apply MeetLat.min_l. apply MeetLat.min_ok.
apply PreO.le_refl. rewrite <- H2. rewrite MeetLat.min_assoc.
apply MeetLat.min_r.
Qed.

Lemma gmonotone : forall (a : S) (U V : Ensemble S),
  (forall u, U u -> V u) -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gdot_left. apply IHGCov. assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gsubset_equiv : forall (U V : Ensemble S)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
Qed.

Lemma dot_infinity : forall (b c : S), let a := dot b c in
  forall (i : I c) (U : Ensemble S), 
  (forall v, C c i v -> GCov (dot a v) U)
  -> GCov a U.
Proof.
unfold localized in loc.
intros. destruct (loc b c i).
apply (ginfinity _ x).
intros.
specialize (H0 u H1).
destruct H0. destruct H0.
simpl in H2. 
replace dotS with MeetLat.min in H2 by reflexivity.
rewrite <- H2.
rewrite MeetLat.min_comm.
apply gdot_left. 
apply H. assumption.
Qed.


Lemma GCov_stable : stable GCov.
Proof.
unfold localized in loc.
unfold stable. intros.
induction H.
- induction H0; intros.
  + apply grefl. unfold dotset. 
    constructor 1 with a. assumption. 
    constructor 1 with a0. assumption. reflexivity.
  + unfold dot. rewrite MeetLat.min_assoc. 
    apply gdot_left. apply IHGCov.
  + pose proof (loc a a0 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ j).

    intros. specialize (loc' u H2).
    destruct loc'. destruct H3.
    simpl in H4.
    replace dotS with dot in H4 by reflexivity.
    rewrite <- H4. unfold dot.
    rewrite MeetLat.min_comm.
    apply gdot_left.
    rewrite <- MeetLat.min_assoc.
    rewrite (MeetLat.min_comm a0 x).
    rewrite MeetLat.min_assoc.
    apply gdot_left. 
    apply H1. assumption.
- intros. unfold dot. rewrite <- MeetLat.min_assoc.
  rewrite (MeetLat.min_comm b0 b).
  rewrite MeetLat.min_assoc. apply gdot_left.
  apply IHGCov.
- intros. pose proof (loc b a i) as loc1.
  destruct loc1 as [j loc'].
  unfold dot. rewrite MeetLat.min_comm.
  apply (ginfinity _ j).

  intros. specialize (loc' u H2).
  destruct loc'. destruct H3. simpl in H4.

 replace dotS with dot in H4 by reflexivity.
    rewrite <- H4. unfold dot.
    rewrite MeetLat.min_comm.
    apply gdot_left.
    rewrite <- MeetLat.min_assoc.
    rewrite (MeetLat.min_comm a x).
    rewrite MeetLat.min_assoc.
    apply gdot_left.
    rewrite MeetLat.min_comm.
    apply H1. assumption.  
Qed.

Theorem GCov_formtop : t GCov.
Proof.
unfold localized in loc.
constructor.
- apply grefl.
- intros. induction H.
  + apply H0. assumption.
  + eapply gdot_left. apply IHGCov. apply H0.
  + apply (ginfinity _ i). intros. apply H1; assumption.
- apply gdot_left.
- intros.
  pose proof GCov_stable as stab.
  unfold stable in stab.
  pose proof GCov_stable.
  replace a with (dot a a).
  eapply H1. eassumption. eassumption.
  pose proof (MeetLat.min_idempotent a) as ida.
  simpl in ida. apply ida.
Qed.

End Defn.

End FormTopM.
