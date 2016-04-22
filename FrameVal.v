Require Import Frame.

Generalizable All Variables.

Module F := Frame.

Require Import LPReal.
Local Open Scope LPR.

(** Supremum over directed sets (i.e., join-semilattices)
    commutes with addition *)
Lemma LPRsup_sum_jlat : forall A `(I : JoinLat.t A),
  forall (f g : A -> LPReal) ,
    (forall n m : A, JoinLat.le n m -> f n <= f m) ->
    (forall n m : A, JoinLat.le n m -> g n <= g m) ->
    LPRsup (fun x : A => f x + g x) = LPRsup f + LPRsup g.
Proof.
intros. eapply LPRsup_sum_lattice.
intros. eapply PreO.max_l. apply JoinLat.max_ok.
intros. eapply PreO.max_r. apply JoinLat.max_ok.
assumption. assumption.
Qed. 


Delimit Scope Val_scope with Val.
(** This module defines valuations. Valuations like measures, rather than
    being defined on sigma-algebras of subsets, they are defined on
    locales (= frames).
*)
Module Val.

Require Import Equalities Coq.Structures.Orders GenericMinMax.

(** This describes the property of when a valuation is
    _continuous_. This condition is analagous to countable additivity
    in measure theory. Essentially, if I have a sequence of subsets
    which is getting bigger and bigger, then the measure of the union
    of the subsets is the supremum of the measures of each of the
    subsets in the sequence. *)
Definition ContinuousV {A OA} (X : F.t A OA) (mu : (A -> LPReal))
  := forall I `{JL : JoinLat.t I} (f : I -> A)
       (fmono : forall (m n : I), JoinLat.le m n -> L.le (f m) (f n))
       , mu (F.sup f) = LPRsup (fun n => mu (f n)).

  Record t {A OA} {X : F.t A OA} :=
  { val :> A -> LPReal
  ; strict : val F.bottom = 0
  ; monotonic : forall (U V : A), L.le U V -> val U <= val V
  ; modular : forall (U V : A),
      val U + val V = val (L.max U V) + val (L.min U V)
  ; continuous : ContinuousV X val
  }.

  Arguments t {A} {OA} X.

  (** If two elements of the frame are equal, they are assigned the
      same measure. *)
  Lemma val_iff : forall `{X : F.t A} (mu : t X) (U V : A),
    L.eq U V -> mu U = mu V.
  Proof. 
   intros. apply LPRle_antisym; apply monotonic; 
   rewrite H; apply PreO.le_refl.
  Qed.

  (** We say one valuation [mu] is less than or equal to another valuation
      [nu] if, for every open [P], the measure [mu] assigns to [P] is
      less than or equal to the measure [nu] assigns to [P] *)
  Definition le `{X : F.t A} (mu nu : t X) := forall P, mu P <= nu P.

  Infix "<=" := le : Val_scope.

  Lemma le_refl `{X : F.t A} (mu : t X) : (mu <= mu)%Val.
  Proof. unfold le. intros. apply monotonic. apply PreO.le_refl. Qed.

  Definition eq `{X : F.t A} (mu nu : t X) := forall P, mu P = nu P.
  Infix "==" := eq : Val_scope.

  (** Lower reals have a partial order. *)
  Definition POLPR : PO.t LPReal LPRle Logic.eq.
  Proof. constructor; intros.
  - constructor; intros. reflexivity. eapply LPRle_trans; eassumption.
  - unfold Proper, respectful. intros. subst. reflexivity.
  - eapply LPRle_antisym; eassumption.
  Qed.

  (** Our definition of "<=" on valuations induces a partial order structure. *)
  Instance PO `{X : F.t A} : PO.t (t X) le eq 
    := PO.map val (PO.pointwise (fun _ : A => POLPR)).

  Lemma le_trans `{X : F.t A} (x y z : t X) : (x <= y -> y <= z -> x <= z)%Val.
  Proof.
    apply PreO.le_trans.
  Qed.

Require Import FunctionalExtensionality ProofIrrelevance.
Lemma eq_compat : forall `{X : F.t A} (mu nu : t X), (mu == nu)%Val -> mu = nu. 
Proof.
intros.
unfold eq in *.
destruct mu, nu. simpl in *.
assert (val0 = val1).
apply functional_extensionality. assumption.
induction H0.
pose proof (proof_irrelevance _ strict0 strict1).
induction H0.
pose proof (proof_irrelevance _ monotonic0 monotonic1).
induction H0.
pose proof (proof_irrelevance _ modular0 modular1).
induction H0.
pose proof (proof_irrelevance _ continuous0 continuous1).
induction H0.
reflexivity.
Qed.

(** The valuation which assigns zero measure to every open. This is the
    bottom element of the partial order we defined on valuations. *)
Definition zero `{X : F.t A} : t X.
Proof. refine (
  {| val := fun _ => 0 |}
); intros.
- reflexivity.
- reflexivity.
- reflexivity.
- unfold ContinuousV. intros. simpl. symmetry.
  apply LPRle_antisym.
  + unfold LPRle. simpl. intros. destruct H. assumption.
  + apply LPRzero_min.
Defined.

  Instance val_proper `{X : F.t A} : Proper (Logic.eq ==> L.eq ==> Logic.eq) (@val _ _ X).
  Proof.
   unfold Proper, respectful. intros. rewrite H. apply val_iff.
   assumption.
  Qed.

Notation "'0'" := zero : Val_scope.

Require Import Ring.

Lemma qredistribute : forall andLq andRq orLq orRq,
    andLq + andRq + (orLq + orRq)
 = (andLq + orLq) + (andRq + orRq).
Proof. intros. ring. Qed.

(** We can add two valuations by adding the measure they assign to each open. *)
Definition add `{X : F.t A} (mu nu : t X) : t X.
Proof. refine (
  {| val := fun P => mu P + nu P |}
); intros.
- rewrite strict. rewrite strict. ring.
- apply LPRplus_le_compat; apply monotonic; assumption.
- rewrite qredistribute. 
  rewrite (qredistribute (mu (L.max _ _))).
  apply LPRplus_eq_compat; apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite (LPRsup_sum_jlat I).
  apply LPRplus_eq_compat;
   eapply continuous; assumption.
   assumption.
  intros. apply monotonic. apply fmono. assumption.
  intros. apply monotonic. apply fmono. assumption.
Defined.

(** Scale a valuation by a constant *)
Definition scale `{X : F.t A} (c : LPReal) (mu : t X) : t X.
Proof. refine (
  {| val := fun P => c * mu P |}
); intros.
- rewrite strict. ring.
- apply LPRmult_le_compat. reflexivity.
  apply monotonic; assumption.
- replace (c * mu U + c * mu V) with (c * (mu U + mu V)) by ring.
  replace (c * mu _ + c * mu _) 
  with (c * (mu (L.max U V) + mu (L.min U V))) by ring.
  apply LPRmult_eq_compat. reflexivity.
  apply modular.
- intros. unfold ContinuousV in *. intros. simpl.
  rewrite continuous by eassumption.
  apply LPRsup_scales.
Defined.

Infix "+" := add : Val_scope.
Infix "*" := scale : Val_scope.

Lemma zero_min `{X : F.t A} : forall (mu : t X), (0 <= mu)%Val.
Proof. intros. unfold le. intros. simpl. apply LPRzero_min. Qed.

(** We can map a continuous map over a valuation. *)
Definition map {A OA B OB} {X : F.t A OA} {Y : F.t B OB} (f : F.cmap OA OB)
  (mu : t X) : t Y.
Proof.
refine (
  {| val := fun x => mu (F.finv f x) |}
).
Proof. 
- pose proof (F.f_bottom (F.cont f)).
  rewrite H. apply strict.
- intros. apply monotonic.
   apply (L.f_PO (F.f_L (F.cont f))).
   apply H.
- intros. unfold L.min, L.max. 
  rewrite (L.f_min (F.f_L (F.cont f))).
  rewrite (L.f_max (F.f_L (F.cont f))).
  apply modular.
- unfold ContinuousV. intros.
  rewrite (F.f_sup (F.cont f)).
  eapply continuous. eassumption. intros. 
  apply (L.f_PO (F.f_L (F.cont f))). apply fmono. assumption.
Defined.

(** If we view [F.prop] as locale corresponding to the 1-point set, then
    [unit_prop] is the unique probability distribution we can define for the 1-point 
    set; it puts all its mass (i.e., a measure of 1) on that single point. *)
Definition unit_prop : t F.prop.
Proof.
refine (
  {| val := fun P => LPRindicator P |}
); simpl; intros.
- apply LPRind_false. unfold not. intros. destruct H.
  contradiction.
- unfold L.le in H. simpl in H. apply LPRind_imp. assumption.
- unfold L.max, L.min. simpl. rewrite (SRadd_comm LPRsrt (LPRindicator (U \/ V))). 
  apply LPRind_modular.
- unfold ContinuousV. intros.
  apply LPRind_exists. 
Defined.

(** We can now define a Dirac delta distribution, which is a probability distribution
    which puts all its mass on a single point. Since a point is just a continuous map from
    the one-point set, a Dirac delta just maps this continuous function over the
    probability distribution [unit_prop] for the one-point set. *)
Definition unit {A OA} {X : F.t A OA} (x : F.point OA)
  : t X := map x unit_prop.

Lemma unit_prob {A OA} {X : F.t A OA} (x : F.point OA) : unit x (F.top) = 1.
Proof.
simpl. apply LPRind_true.
rewrite (F.f_top (F.cont x)). simpl. exists True. constructor.
Qed.

Definition pointwise {A B : Type} (cmp : B -> B -> Prop)
  (f g : A -> B) : Prop := forall (a : A), cmp (f a) (g a).

Definition supValuation {A OA} {X : F.t A OA}
  I `{JL : JoinLat.t I} (f : I -> t X)
    (fmono : forall (m n : I), JoinLat.le m n -> (f m <= f n)%Val)
 : t X.
Proof.
refine (
  {| val := fun P => LPRsup (fun i => f i P) |}).
- apply LPRle_antisym. apply LPRsup_le.
  intros. rewrite strict. reflexivity. apply LPRzero_min.
- intros. apply LPRsup_le. intros.
  apply LPRsup_ge2. exists a. apply monotonic. assumption.
- intros. unfold le in fmono.
  repeat  erewrite <- LPRsup_sum_jlat by auto.
  apply LPRsup_eq_pointwise. intros. apply modular.
- unfold ContinuousV. intros. apply LPRle_antisym. 
  apply LPRsup_le. intros. rewrite continuous.
  apply LPRsup_le. intros. apply LPRsup_ge2. exists a0.
  apply LPRsup_ge2. exists a. reflexivity. assumption. assumption.
  apply LPRsup_le. intros. apply LPRsup_le. intros.
  apply LPRsup_ge2. exists a0. apply monotonic.
  apply F.sup_ok.
Defined.

(** The nth iteration of the fixpoint of a functional on
    measures *)
Fixpoint fixn {A OA} {X : F.t A OA} 
  (f : t X -> t X) (n : nat)
  : t X
  := match n with
  | 0 => 0%Val
  | S n' => f (fixn f n')
  end.

(** If our valuation functional is monotonic, then the
    fixpoint is nondecreasing. *)
Lemma fixnmono {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : forall (n : nat), (fixn f n <= fixn f (S n))%Val.
Proof. intros. induction n.
simpl. unfold le; intros. simpl. apply LPRzero_min.
simpl. apply fmono. assumption.
Qed.

Lemma fixnmono2 {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : forall (m n : nat), (JoinLat.le m n)%nat -> (fixn f m <= fixn f n)%Val.
Proof. intros. induction H. apply le_refl. 
eapply le_trans. eassumption. apply fixnmono. assumption.
Qed.

(** If we have a valuation functional which is monotonic, we can take
    its fixpoint! *)
Definition fixValuation {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  : t X
  := supValuation nat (fun n => (fixn f n)) 
     (fixnmono2 f fmono).

Lemma fixValuation_subProb {A OA} {X : F.t A OA}
  (f : t X -> t X)
  (fmono : forall u v, (u <= v -> f u <= f v)%Val)
  (fbounded : forall v, val v F.top <= 1 -> val (f v) F.top <= 1)
  : (fixValuation f fmono) F.top <= 1.
Proof. unfold fixValuation.  simpl. apply LPRsup_le.
intros n. induction n. simpl. apply LPRzero_min.
simpl. apply fbounded. assumption.
Qed.

Theorem fixValuation_fixed_u {A OA} {X : F.t A OA} 
  (f : t X -> t X)
  (fmono : forall u v : t X, (u <= v)%Val -> (f u <= f v)%Val)
  : (fixValuation f fmono <= f (fixValuation f fmono))%Val.
Proof.
unfold le. intros P. apply LPRsup_le. intros n. destruct n; simpl.
- apply LPRzero_min.
- apply fmono. unfold le; intros. simpl.
  apply LPRsup_ge2. exists n. reflexivity.
Qed.

(** Definition of when a functional is continuous. *)
Definition Continuous {A OA} {X : F.t A OA} (f : t X -> t X) 
  := forall I `(JL : JoinLat.t I) (nonempty : I) (g : I -> t X)
       (gmono : forall m n : I, JoinLat.le m n -> (g m <= g n)%Val)
       (P : A),
      (f (supValuation I g gmono)) P
    = LPRsup (fun x : I => f (g x) P).

(** If a functional is continuous, then we indeed reach a fixpoint
    when we apply [fixValuation]. *)
Theorem fixValuation_fixed {A OA} {X : F.t A OA} (f : t X -> t X)
  (fmono : forall u v : t X, (u <= v)%Val -> (f u <= f v)%Val)
  : Continuous f
  -> f (fixValuation f fmono) = fixValuation f fmono.
Proof.
intros.
apply eq_compat. unfold eq. intros. apply LPRle_antisym.
-  unfold Continuous in H.
  unfold fixValuation at 1. rewrite H.
  apply LPRsup_le. intros n.
  simpl. apply LPRsup_ge2. exists (S n). reflexivity. exact 0%nat.
- apply fixValuation_fixed_u.
Qed.

(** * Reasoning about measures *)

(** A set of techniques for reasoning about measures. *)

(** Binary version of the union bound. *)
Lemma union_bound2 {A OA} {X : F.t A OA} {mu : t X}
  (P Q : A)
  : mu (L.min P Q) <= mu P + mu Q.
Proof.
rewrite modular. eapply LPRle_trans.
Focus 2. eapply LPRplus_le_compat.
apply LPRzero_min. reflexivity.
rewrite (SRadd_0_l LPRsrt). 
reflexivity.
Qed.

(** Finite version of the union bound. *)
Lemma union_bound {A OA} {X : F.t A OA} {mu : t X}
  (xs : list A)
  : mu (List.fold_right L.min F.bottom xs) <=
    List.fold_right LPRplus 0 (List.map (val mu) xs).
Proof.
induction xs; simpl.
- rewrite strict. reflexivity.
- rewrite <- IHxs. apply union_bound2. 
Qed.

(** Finite distributions *)
Require Import Qnn.
Section FinDist.
Context {A} {OA} {X : F.t A OA}.

Fixpoint uniform_helper (p : LPReal) (xs : list (F.point OA)) := match xs with
  | nil => 0%Val
  | (x :: xs')%list => (p * unit x + uniform_helper p xs')%Val
end.

Lemma uniform_helper_weight {p : LPReal} {xs : list (F.point OA)}
  : uniform_helper p xs F.top = LPRQnn (Qnnnat (length xs)) * p.
Proof.
induction xs. 
- simpl. ring. 
- simpl. pose proof (unit_prob a) as UP. simpl in UP.
  rewrite UP. rewrite IHxs. rewrite <- LPRQnn_plus.
  ring.
Qed.

(** A uniform distribution over a finite, non-empty list
    of elements. *)
Definition uniform {n : nat} (xs : Vector.t (F.point OA) (S n)) :=
  uniform_helper (LPRQnn (Qnnfrac (S n))) (Vector.to_list xs).

Lemma Vector_length {T} {n : nat} {xs : Vector.t T n}
  : length (Vector.to_list xs) = n.
Proof. induction xs.
- reflexivity.
- unfold Vector.to_list in *. simpl. rewrite IHxs. reflexivity.
Qed.

Lemma uniform_prob : forall {n : nat} {xs : Vector.t (F.point OA) (S n)}
  , (uniform xs) F.top = 1.
Proof.
intros. unfold uniform.
rewrite uniform_helper_weight. rewrite Vector_length.
rewrite LPRQnn_mult. rewrite Qnnnatfrac. reflexivity.
Qed.

End FinDist.

End Val.

Module ValNotation.
Coercion Val.val : Val.t >-> Funclass.  Delimit Scope Val_scope with Val.

Infix "<=" := Val.le : Val_scope.
Infix "==" := Val.eq : Val_scope.
Infix "+" := Val.add : Val_scope.
Infix "*" := Val.scale : Val_scope.
Notation "'0'" := Val.zero : Val_scope.

End ValNotation.