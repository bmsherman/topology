Require Import Frame.
Set Asymmetric Patterns.

Module FormTop.

(** Inductively generated formal topologies *)

Generalizable All Variables.

Section Defn.

Context {S} {le eq} {PO : PO.t S le eq}.

Definition down (a b c : S) : Prop :=
  le c a /\ le c b.

Record t { Cov : S -> (S -> Prop) -> Prop } :=
  { refl : forall (a : S) (U : S -> Prop), U a -> Cov a U
  ; trans : forall (a : S) (U V : S -> Prop), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; le_left : forall (a b : S) (U : S -> Prop)
     , le a b -> Cov b U -> Cov a U
  ; le_right : forall (a : S) (U V : S -> Prop)
    , Cov a U -> Cov a V
    -> Cov a (fun c => exists u v, U u /\ V v /\ down u v c)
  }.

Arguments t : clear implicits.

Record tPos { Cov : S -> (S -> Prop) -> Prop } {Pos : S -> Prop} :=
  { cov :> t Cov
  ; mono : forall a U, Pos a -> Cov a U -> exists b, U b /\ Pos b
  ; positive : forall a U, (Pos a -> Cov a U) -> Cov a U
  }.

Arguments tPos : clear implicits.

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

Lemma gsubset_equiv : forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
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
    eapply PreO.le_trans; eassumption.
  + pose proof (loc c a0 H3 i) as loc1.
    destruct loc1 as [j loc'].
    apply (ginfinity _ j).

    intros. specialize (loc' u H4).
    destruct loc'. destruct H5. destruct H6.
    eapply H1. eassumption.
    eapply PreO.le_trans. apply H6. assumption.
    assumption.
- intros. 
  apply IHGCov. eapply PreO.le_trans. apply H2. apply H. 
  apply H3.
- intros. pose proof (loc c a H2 i) as loc1.
  destruct loc1 as [j loc'].
  apply (ginfinity _ j).

  intros. specialize (loc' u H4).
  destruct loc'. destruct H5. destruct H6.
  eapply H1. eassumption. assumption.
  eapply PreO.le_trans. apply H6. assumption.
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
  apply PreO.le_refl. apply PreO.le_refl.
Qed.


End Defn.

End FormTop.

Arguments FormTop.t {_} _ _.

Module FormTopM.

Generalizable All Variables.

Section Defn.

Context {S} {dotS : S -> S -> S}.

Instance ops : MeetLat.Ops S :=
  {| MeetLat.le := fun x y => dotS x y = x
   ; MeetLat.eq := eq
   ; MeetLat.min := dotS
  |}.

Definition le := MeetLat.le.
Definition dot := MeetLat.min.

Context {ML : @MeetLat.t S ops}.

Require Import SetoidClass Morphisms.

Class t { Cov : S -> (S -> Prop) -> Prop } :=
  { refl : forall (a : S) (U : S -> Prop), U a -> Cov a U
  ; trans : forall (a : S) (U V : S -> Prop), 
       Cov a U 
     -> (forall (a' : S), U a' -> Cov a' V)
     -> Cov a V
  ; dot_left : forall (a b : S) (U : S -> Prop)
     , Cov a U -> Cov (dot a b) U
  ; dot_right : forall (a : S) (U V : S -> Prop)
    , Cov a U -> Cov a V
    -> Cov a (fun c => exists u v, U u /\ V v /\ MeetLat.eq c (dot u v))
  }.

Arguments t : clear implicits.

Lemma monotone {Cov} : t Cov
  -> forall (U V : S -> Prop)
  , (forall a : S, U a -> V a)
  -> forall a, Cov a U -> Cov a V.
Proof.
intros. eapply trans. eassumption.
intros. apply H0 in H2. eapply refl. eassumption.
Qed.

Lemma subset_equiv {Cov} : t Cov
  -> forall (U V : S -> Prop)
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
- pose (UV := (fun c => exists u v, U u /\ V v /\ MeetLat.eq c (MeetLat.min u v))).
  apply monotone with UV. assumption.
  unfold UV. intros.
  destruct H1 as [u [v [Uv [Vv downP]]]].
  exists u. exists v. split. assumption. split. assumption.
  unfold FormTop.down. repeat rewrite downP.
  split. apply MeetLat.min_ok. apply MeetLat.min_ok. 
  unfold UV. apply dot_right; assumption.
Qed.

Variable I : S -> Type.
Variable C : forall (s : S), I s -> (S -> Prop).

Definition stable (Cov : S -> (S -> Prop) -> Prop) :=
  forall a b U V, Cov a U -> Cov b V
  -> Cov (dot a b) (fun s => exists u v, U u /\ V v /\ MeetLat.eq s (dot u v)).

Definition localized := forall (b c : S),
  forall (i : I c), let a := dot b c in
  exists (j : I a),
  (forall s, C a j s -> exists u, C c i u /\ MeetLat.le s (dot a u)).

Inductive GCov : S -> (S -> Prop) -> Prop :=
  | grefl : forall (a : S) (U : S -> Prop), U a -> GCov a U
  | gdot_left : forall (a b : S) (U : S -> Prop)
     , GCov a U -> GCov (dot a b) U
  | ginfinity : forall (a : S) (i : I a) (U : S -> Prop),
     (forall u, C a i u -> GCov u U) -> GCov a U.

Hypothesis loc : localized. 

Lemma gmonotone : forall (a : S) (U V : S -> Prop),
  (forall u, U u -> V u) -> GCov a U -> GCov a V.
Proof.
intros. induction H0.
- apply grefl. apply H. assumption.
- eapply gdot_left. apply IHGCov. assumption.
- eapply ginfinity. intros. apply H1. apply H2.
  apply H.
Qed.

Lemma gsubset_equiv : forall (U V : S -> Prop)
  , (forall a : S, U a <-> V a)
  -> forall a, GCov a U <-> GCov a V.
Proof.
intros. split; apply gmonotone; intro; apply H; assumption.
Qed.

Lemma dot_infinity : forall (b c : S), let a := dot b c in
  forall (i : I c) (U : S -> Prop), 
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
  + apply grefl. exists a. exists a0. intuition.
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

End FormTopM.

Module Concrete. 
Section Concrete.

Variable X S : Type.
Variable In : X -> S -> Prop.

Instance SPO : PO.t S _ _ := PO.map (fun s x => In x s) (PO.subset X).

Record t : Type :=
  { here : forall x, { s | In x s }
  ; local : forall (a b : S) x, In x a -> In x b 
          -> { c | In x c /\ @FormTop.down S (map_op (fun s x => In x s) L.le) a b c }
  }.

Definition Ix (a : S) : Type := sig (fun (g : forall (x : X), In x a -> S) 
  => forall (x : X) (prf : In x a), In x (g x prf)).

Definition C (a : S) (i : Ix a) : S -> Prop := match i with
  | exist g _ => fun s => exists (x : X) (prf : In x a), s = g x prf
  end.

Theorem loc : t -> @FormTop.localized S (map_op (fun s x => In x s) L.le) Ix C.
Proof.
intros conc. destruct conc.
unfold FormTop.localized. simpl.
intros. unfold Ix in *. destruct i as [g Pg].
assert (forall x prf, In x (g x (H x prf))) as Pg'.
intros. apply Pg.
pose (fun x xina => local0 a (g x (H x xina)) x xina
  (Pg' x xina)) as g'.
assert (forall x prf, In x (proj1_sig (g' x prf))) as Pg''.
intros. destruct (g' x prf).
simpl. destruct a0. assumption.
exists (exist _ (fun x prf => proj1_sig (g' x prf)) Pg''). 

unfold C. intros.
destruct H0 as [x [prf img]].
exists (g x (H x prf)). split. exists x. exists (H x prf).
reflexivity.
destruct (g' x prf). simpl in *. destruct a0. subst.
assumption. 
Qed.

End Concrete.
End Concrete.

Module Cantor.

Variable A : Type.

Definition S := list A.

Definition Ix (s : S) := True.

Require Import List.

Definition C (s : S) (_ : True) (s' : S) : Prop := exists b,
  s' = s ++ (b :: nil).

Definition LE {A} (xs ys : list A) : Prop := exists zs,
  xs = ys ++ zs.

Lemma LE_PO {A : Type} : PO.t (list A) LE eq.
Proof.
constructor; intros.
- constructor; unfold LE; intros.
  + exists nil. rewrite app_nil_r. reflexivity.
  + destruct H. destruct H0.
    exists (x1 ++ x0). rewrite H. rewrite H0.
    rewrite app_assoc. reflexivity.
- unfold Morphisms.Proper, Morphisms.respectful. 
  unfold LE in *. intros. subst. reflexivity. 
- unfold LE in *.  destruct H. destruct H0.
  rewrite H0 in H. rewrite <- app_assoc in H.
  rewrite <- app_nil_r in H at 1.
  apply app_inv_head in H.
  symmetry in H. apply app_eq_nil in H.
  destruct H.  subst. rewrite app_nil_r.
  reflexivity.
Defined.

Definition Cov := @FormTop.GCov S LE Ix C.

Theorem loc : @FormTop.localized S LE Ix C.
Proof.
unfold FormTop.localized.
intros.  unfold Ix in *. destruct i. exists I.
intros. unfold C in *. destruct H0.
simpl in H.
unfold LE in H. destruct H.
destruct x0.
- subst.
  exists (c ++ x :: nil). split. exists x. reflexivity.
  unfold FormTop.down. split; simpl; unfold LE.
  exists (x :: nil). reflexivity.
  exists nil. repeat rewrite app_nil_r. reflexivity.
- exists (c ++ a0 :: nil). split. exists a0. reflexivity.
  unfold FormTop.down. split; simpl; unfold LE.
  exists (x :: nil). assumption. exists (x0 ++ x :: nil).
  rewrite <- app_assoc. simpl.
  rewrite H0. rewrite H. rewrite <- app_assoc. reflexivity.
Qed.

End Cantor.

Module Product.

Generalizable All Variables.
Section Product.

Variable S T : Type.
Context `{POS : PO.t S leS eqS}. 
Context `{POT : PO.t T leT eqT}.
Variable IS : S -> Type.
Variable IT : T -> Type.
Variable CS : forall s, IS s -> (S -> Prop).
Variable CT : forall t, IT t -> (T -> Prop).

Definition Ix (p : S * T) : Type := match p with
  (s, t) => (IS s * T + S * IT t)%type end.

Definition C (p : S * T) : Ix p -> S * T -> Prop
  := match p as p' return Ix p' -> S * T -> Prop with (a, b) =>
  fun pI open => let (z, w) := open in match pI with
    | inl (sI, t) => CS a sI z /\ w = b
    | inr (s, tI) => z = a /\ CT b tI w
    end
  end.

Definition PO := PO.product POS POT.

Theorem loc : 
    @FormTop.localized S leS IS CS
  -> @FormTop.localized T leT IT CT
  -> @FormTop.localized (S * T) (prod_op leS leT) Ix C.
Proof.
intros. unfold FormTop.localized in *.
intros. destruct a as [sa ta], c as [sc tc]. 
destruct H1.
simpl in H1, H2, i.
destruct i as [[sI t]|[s tI]].
- specialize (H sa sc H1 sI).
  destruct H. unfold Ix in *.
  exists (inl (x, t)).
  intros. destruct s as [su tu].
  simpl in H3. destruct H3.
  specialize (H _ H3).
  destruct H as [u [CSu downu]].
  simpl. exists (u, tc). split. split. assumption. reflexivity.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. assumption. apply PreO.le_refl.
  simpl. split. assumption. assumption.
- specialize (H0 ta tc H2 tI).
  destruct H0. unfold Ix in *.
  exists (inr (s, x)).
  intros. destruct s0 as [su tu].
  simpl in H3. destruct H3.
  specialize (H0 _ H4).
  destruct H0 as [u [CTu downu]].
  simpl. exists (sc, u). split. split. reflexivity. assumption.
  subst. destruct downu.
  unfold FormTop.down. split.
  simpl. split. apply PreO.le_refl. assumption.
  simpl. split. assumption. assumption.
Qed.

Definition Cov := @FormTop.GCov (S * T) (prod_op leS leT) Ix C.
  
End Product.
End Product.

(*WIP : Still need to update
Module Cont.
Section Cont.

Record t {S} {CovS : S -> (S -> Prop) -> Prop} 
  {T} {POT : PO.t T}
  {CovT : T -> (T -> Prop) -> Prop}
 {F : S -> T -> Prop} : Prop :=
  { here : forall s, exists t, F s t
  ; local : forall a b c, F a b -> F a c
    -> exists bc, F a bc /\ FormTop.down POT b c bc
  ; cov : forall a b V, F a b -> CovT b V
    -> CovS a (fun s => exists t, V t /\ F s t)
  }.

Arguments t {S} CovS {T} POT CovT F.

Lemma le_left {S} {POS : PO.t S} {CovS : S -> (S -> Prop) -> Prop}
  {T} {POT : PO.t T} {CovT : T -> (T -> Prop) -> Prop}
  : FormTop.t POS CovS
  -> FormTop.t POT CovT
  -> forall (F : S -> T -> Prop), t CovS POT CovT F
  -> forall a b u, PO.le POS a b -> F b u -> F a u.
Proof.
intros.
assert (CovT u (fun u' => u = u')).
eapply FormTop.refl. eassumption. reflexivity.
pose proof (cov H1 _ _ _ H3 H4).
simpl in H5.
assert (CovS b (fun a' => F a' u)).
eapply FormTop.monotone. eassumption. 2:apply H5.
intros a'. simpl. intros. destruct H6.
destruct H6. induction H6. assumption.
assert (CovS a (fun a' => F a' u)).
eapply (FormTop.le_left _ H). eassumption. assumption.
Abort.

Definition id {S} (POS : PO.t S)
  (s t : S) := PO.le POS s t.

Theorem t_id {S} {POS : PO.t S} {CovS : S -> (S -> Prop) -> Prop} 
  : FormTop.t POS CovS -> t CovS POS CovS (id POS).
Proof.
intros. constructor; intros.
- exists s. unfold id. apply PO.le_refl.
- unfold id in *. exists a. split. apply PO.le_refl.
  split; assumption.
- unfold id in *. eapply FormTop.le_left. eassumption. 
  eassumption. eapply (FormTop.monotone POS CovS H). 2: eassumption. 
  intros. exists a0. split. assumption. apply PO.le_refl. 
Qed.

(*
Everything in s maps to u
iff there is some subset T such that
  everything in s maps to T and
  everything in T maps to u
*)

Variable S T : Type.

Variable CovS : S -> (S -> Prop) -> Prop.
Variable POS : PO.t S.
Variable CovS_ok : FormTop.t POS CovS.

Variable CovT : T -> (T -> Prop) -> Prop.
Variable POT : PO.t T.
Variable CovT_ok : FormTop.t POT CovT.

Variable U : Type.
Variable CovU : U -> (U -> Prop) -> Prop.
Variable POU : PO.t U.
Variable CovU_ok : FormTop.t POU CovU.

Definition compose (F : S -> T -> Prop)
  (G : T -> U -> Prop) (s : S) (u : U) : Prop :=
    exists t, F s t /\ G t u.


Theorem t_compose : forall (F : S -> T -> Prop) (G : T -> U -> Prop),
    t CovS POT CovT F
  -> t CovT POU CovU G
  -> t CovS POU CovU (compose F G).
Proof.
intros. constructor.
- intros. pose proof (here H s). destruct H1.
  pose proof (here H0 x). destruct H2.
  exists x0. unfold compose. exists x. split; assumption.
- unfold compose. intros.
  destruct H1 as [tb [Fatb Gtbb]].
  destruct H2 as [tc [Fatc Gtcc]].
  pose proof (local H _ _ _ Fatb Fatc).
  destruct H1 as [tt' [Fatt' downtt']].
  pose proof (here H0 tt').
  destruct H1. 

  exists x. split. 
  exists tt'. split; assumption. 
  admit.
- intros. unfold compose in H1. 
  destruct H1 as [t [Fat Gtb]].
Abort.
  

End Cont.
End Cont.
*)