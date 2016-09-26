Require Import 
  FormTop.FormTop 
  Algebra.Frame 
  Algebra.Sets
  FormTop.Cont.

(** Product spaces for inductively generated formal topologies.
    See Section 4.3 of [1]. *)
Module Product.

Generalizable All Variables.
Section Product.

Variable S T : Type.
Context `{POS : PreO.t S leS}. 
Context `{POT : PreO.t T leT}.
Variable IS : S -> Type.
Variable IT : T -> Type.
Variable CS : forall s, IS s -> (Ensemble S).
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

Definition PO := PreO.product POS POT.

Theorem loc : 
    FormTop.localized leS CS
  -> FormTop.localized leT CT
  -> FormTop.localized (prod_op leS leT) C.
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
  simpl. red. eauto. 
Qed.

Definition Cov := FormTop.GCov (prod_op leS leT) C.

Hypothesis locS : FormTop.localized leS CS.
Hypothesis locT : FormTop.localized leT CT.

Theorem isCov : FormTop.t (prod_op leS leT) Cov.
Proof.
apply (@FormTop.GCov_formtop (S * T) (prod_op leS leT)
  PO Ix C (loc locS locT)).
Qed.

Let CovS := FormTop.GCov leS CS.
Let CovT := FormTop.GCov leT CT.

Lemma factors : forall a b U V, CovS a U -> CovT b V -> 
  Cov (a, b) (fun p => let (a', b') := p in U a' /\ V b').
Proof.
intros. induction H.
- induction H0.
  + apply FormTop.grefl. split; assumption.
  + eapply FormTop.gle_left. 2:apply IHGCov.
    split; simpl. apply PreO.le_refl. assumption.
  + apply FormTop.ginfinity with (inr (IS a * T) (a, i)).
    intros. simpl in H2. destruct u. destruct H2. 
    subst. apply H1. assumption.
- apply FormTop.gle_left with (b0, b). split; simpl.
  assumption. apply PreO.le_refl.
  apply IHGCov.
- apply FormTop.ginfinity with (inl (S * IT b) (i, b)).
  intros. simpl in H2. destruct u. destruct H2. 
  subst. apply H1. assumption.
Qed.

(** The other space has to be nonempty *)
Lemma unfactors1 : forall a b U, Cov (a, b) U
  -> (forall (t : T) (i : IT t), Inhabited (CT t i))
  -> CovS a (fun s => exists b', U (s, b')).
Proof.
intros. remember (a, b) as ab.
replace (a) with (fst ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. exists t. assumption.
- destruct a, b, H. simpl in *. 
  apply FormTop.gle_left with s0. assumption.
  assumption.
- destruct a. destruct i.
  + destruct p. apply FormTop.ginfinity with i.
    intros. apply (H1 (u, t)). simpl. simpl in H1.
    intuition.
  + destruct p. simpl in *.
    specialize (H0 t i). destruct H0.
    apply (H1 (s, x)). split. reflexivity. assumption.
Qed.

Lemma unfactors2 : forall a b U, Cov (a, b) U
  -> (forall (s : S) (i : IS s), Inhabited (CS s i))
  -> CovT b (fun t' => exists a', U (a', t')).
Proof.
intros. remember (a, b) as ab.
replace b with (snd ab) by (rewrite Heqab; auto).
clear a b Heqab. induction H.
- apply FormTop.grefl. destruct a. exists s. assumption.
- destruct a, b, H. simpl in *. 
  apply FormTop.gle_left with t0. assumption.
  assumption.
- destruct a. destruct i.
  + destruct p. simpl in *.
    specialize (H0 s i). destruct H0.
    apply (H1 (x, t)). split. assumption. reflexivity.
  + destruct p. apply FormTop.ginfinity with i.
    intros. apply (H1 (s, u)). simpl. simpl in H1.
    intuition.
Qed.

End Product.
End Product.

Module ProductMaps.
  Generalizable All Variables.
Section Products. 
Context {S} `{POS : PreO.t S leS}.
Context {IS} {CS : forall (s : S), IS s -> (Ensemble S)}.
Variable locS : FormTop.localized leS CS.
Let CovS := FormTop.GCov leS CS.

Definition diagonal (out : S * S) (p : S) : Prop :=
  let (out1, out2) := out in leS p out1 /\ leS p out2.

Lemma t_diagonal : Cont.t leS (prod_op leS leS)
  CovS (@Product.Cov _ _ leS leS IS IS CS CS) diagonal.
Proof.
pose proof (FormTop.GCov_formtop _ CS) as FTS.
constructor; intros; unfold diagonal, CovS in *.
- apply FormTop.refl. exists (a, a). split.
  split; reflexivity. 
- destruct b. destruct H0.
  split; eauto using PreO.le_trans. 
- destruct b, c. destruct H, H0.
  apply FormTop.refl. exists (a, a).
  split. split; unfold prod_op; simpl; eauto.
  split; eauto. split; reflexivity.
- generalize dependent a. induction H0; intros.
  + apply FormTop.refl. exists a. assumption. assumption. 
  + apply IHGCov. destruct a, b, H. simpl in *. 
    destruct H1. split; eauto using PreO.le_trans.
  + destruct a. simpl in *. destruct H1. destruct i.
    * destruct p. unfold FormTop.localized in locS. 
      specialize (locS a0 s H1 i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (H3 _ H4).
      destruct H3. destruct H3. 
      apply H0 with (x0, s0).
      auto. destruct H5. eauto using PreO.le_trans.
    * destruct p. unfold FormTop.localized in locS. 
      specialize (locS a0 s0 H2 i).
      destruct locS.
      apply FormTop.ginfinity with x.
      intros.
      specialize (H3 _ H4).
      destruct H3. destruct H3. 
      apply H0 with (s, x0).
      auto. destruct H5. eauto using PreO.le_trans.
Qed.
  

Context {T} `{POT : PreO.t T leT}.
Context {IT} {CT : forall (t : T), IT t -> (T -> Prop)}.
Variable locT : FormTop.localized leT CT.
Let CovT := FormTop.GCov leT CT.

Definition proj_L (out : S) (p : S * T) : Prop :=
  let (s1, t1) := p in leS s1 out.

Lemma t_proj_L : Cont.t (prod_op leS leT) leS 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovS proj_L.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_L in *.
- apply FormTop.refl. destruct a. exists s. unfold In.
  constructor. reflexivity.
- destruct c, a.  destruct H. simpl in H, H1. 
  eapply PreO.le_trans; eassumption.
- destruct a. apply FormTop.refl. 
  exists s. split; assumption. reflexivity. 
- destruct a. generalize dependent s. induction H0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (b, t).
    split; simpl. eapply PreO.le_trans; eassumption. 
    apply PreO.le_refl.
    apply IHGCov. apply PreO.le_refl.
  + unfold FormTop.localized in locS. 
    specialize (locS _ _ H1 i).
    destruct locS.
    apply FormTop.ginfinity with (inl (x, t)). 
    intros. simpl in *. destruct u. destruct H3.
    subst.
    specialize (H2 _ H3). destruct H2 as (u & Caiu & downu).
    eapply H0. eassumption.
    destruct downu. assumption.
Qed.

Definition proj_R (out : T) (p : S * T) : Prop :=
  let (s1, t1) := p in leT t1 out.

Lemma t_proj_R : Cont.t (prod_op leS leT) leT 
  (@Product.Cov _ _ leS leT IS IT CS CT) CovT proj_R.
Proof.
pose proof (Product.isCov _ _ _ _ _ _ locS locT) as FTST.
constructor; intros; unfold proj_R in *.
- apply FormTop.refl. destruct a. exists t. unfold In.
  constructor. reflexivity.
- destruct c, a.  destruct H. simpl in H, H1. 
  eauto using PreO.le_trans.
- destruct a. apply FormTop.refl. 
  exists t. split; eauto. reflexivity. 
- destruct a. generalize dependent t. induction H0; intros.
  + apply FormTop.refl. exists a; assumption.
  + apply FormTop.le_left with (s, b).
    (** We would like
        eauto using (PreO.le_refl, PreO.le_trans)
        to work here, but it is dumb! *)
    split; simpl. apply PreO.le_refl. 
    eapply PreO.le_trans; eassumption. 
    apply IHGCov. apply PreO.le_refl.
  + unfold FormTop.localized in locT. 
    specialize (locT _ _ H1 i).
    destruct locT.
    apply FormTop.ginfinity with (inr (s, x)). 
    intros. simpl in *. destruct u. destruct H3.
    subst.
    specialize (H2 _ H4). destruct H2 as (u & Caiu & downu).
    eapply H0. eassumption.
    destruct downu. assumption.
Qed.

Context {A} `{POA : PreO.t A leA}.
Context {IA} {CA : forall (t : A), IA t -> (A -> Prop)}.
Variable locA : FormTop.localized leA CA.
Let CovA := FormTop.GCov leA CA.

Context {B} `{POB : PreO.t B leB}.
Context {IB} {CB : forall (t : B), IB t -> (B -> Prop)}.
Variable locB : FormTop.localized leB CB.
Let CovB := FormTop.GCov leB CB.

Definition parallel (F : Cont.map S A) (G : Cont.map T B)
  (out : A * B) (p : S * T)  : Prop :=
  let (s, t) := p in let (a, b) := out in
   F a s /\ G b t.

Existing Instance Product.PO.

Instance product_cov :
  FormTop.t (prod_op leS leT) (@Product.Cov S T leS leT IS IT CS CT).
Proof.
apply FormTop.GCov_formtop.
apply Product.loc; assumption.
Qed.

Theorem t_parallel (F : Cont.map S A) (G : Cont.map T B)
  : Cont.t leS leA CovS CovA F
  -> Cont.t leT leB CovT CovB G
  -> Cont.t (prod_op leS leT) (prod_op leA leB)
      (@Product.Cov _ _ leS leT IS IT CS CT)
      (@Product.Cov _ _ leA leB IA IB CA CB)
      (parallel F G).
Proof.
intros ContF ContG.
constructor; intros; unfold parallel in *.
- eapply FormTop.gmonotone with
  (fun s : S * T => let (s', t') := s in
  union (fun _ => True) F s' /\ union (fun _ => True) G t').
  unfold Included, In; intros.
  destruct a, x. 
  destruct H. destruct H, H0.
  constructor 1 with (a, a0). 
  constructor. econstructor; eassumption.
  destruct a. apply Product.factors; try assumption.
  apply (Cont.here ContF). apply (Cont.here ContG).
- destruct c, b, a. destruct H; simpl in *.
  destruct H0. split.
  eapply (Cont.le_left ContF); eassumption.
  eapply (Cont.le_left ContG); eassumption.
- destruct a, b, c.
  destruct H, H0.
  pose proof (Cont.local ContF H H0).
  pose proof (Cont.local ContG H1 H2).
  eapply FormTop.monotone. Focus 2.
  eapply Product.factors; eassumption.
  unfold Included, In; intros.
  destruct x. destruct H5. destruct H5, H6.
  destruct H5, H6.
  exists (a1, a2). unfold FormTop.down, In, prod_op; auto.
  split; assumption.
- destruct a, b. destruct H. 
  pose proof (fun VA => Cont.cov ContF VA H).
  pose proof (fun VB => Cont.cov ContG VB H1).
  (* I think I can do it if the spaces A and B are both
     nonempty (as topological spaces). But if not, I
     learn nothing from the fact that (a, b) <| V.

     Actually, I'm not sure. I don't think the following
     strategy works.
  *)
  eapply FormTop.gmonotone. 
  Focus 2. eapply Product.factors; try eassumption.
  eapply H2. eapply Product.unfactors1; try eassumption.
  admit. eapply H3. eapply Product.unfactors2. 
  eassumption. admit.
  unfold Included, In; intros.
  destruct x. destruct H4. destruct H4, H5.
  destruct H4, H5. econstructor.
  
Admitted.

End Products.
End ProductMaps.