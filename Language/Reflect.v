
Inductive Ty : Type :=
  | TDiscrete : Set -> Ty
  | Tunit : Ty
  | Tpair : Ty -> Ty -> Ty.

Inductive Expr : Ty -> Type :=
| Ett : Expr Tunit
| Econst : forall {A : Set}, A -> Expr (TDiscrete A)
| Efst : forall {A B}, Expr (Tpair A B) -> Expr A
| Esnd : forall {A B}, Expr (Tpair A B) -> Expr B
| Epair : forall {A B}, Expr A -> Expr B -> Expr (Tpair A B).

Fixpoint dcoqT (t : Ty) : Type := match t with
| Tunit => unit
| TDiscrete A => A
| Tpair a b => prod (dcoqT a) (dcoqT b)
end.

Fixpoint dcoq {A} (e : Expr A) : dcoqT A := match e with
| Ett => tt
| Econst x => x
| Efst e' => fst (dcoq e')
| Esnd e' => snd (dcoq e')
| Epair a b => pair (dcoq a) (dcoq b)
end.

Fixpoint dcoq_eq {A : Ty} : dcoqT A -> dcoqT A -> Prop
  := match A with
| Tunit => fun _ _ => True
| TDiscrete _ => eq
| Tpair a b => fun e1 e2 => dcoq_eq (fst e1) (fst e2) /\ dcoq_eq (snd e1) (snd e2)
end.

Theorem dcoq_eq_eq {A : Ty} : forall (x y : dcoqT A),
  dcoq_eq x y -> x = y.
Proof.
intros. induction A.
- assumption.
- destruct x, y. reflexivity.
- destruct x, y, H. f_equal; auto.
Qed.

Section Cont.
Require Import Spec.Category Spec.Discrete.
Import Category.
Import Discrete.
Context {U : Type} {ccat : CCat U} {cmc : CMC U}
  {D : Type -> U} {power : Type -> U -> U} 
  {Dops : DiscreteOps D power}.

Local Open Scope obj.
Local Open Scope morph.

Fixpoint dcontT (t : Ty) : U := match t with
| TDiscrete A => D A
| Tunit => unit
| Tpair a b => (dcontT a * dcontT b)%obj
end.

Fixpoint dcont {A} (e : Expr A) : unit ~~> dcontT A 
  := match e with
  | Ett => tt
  | Econst x => discrete_pt _ _ x
  | Efst e' => fst ∘ dcont e'
  | Esnd e' => snd ∘ dcont e'
  | Epair a b => pair (dcont a) (dcont b)
  end.

Fixpoint d_discrete_ok {t} : Expr t -> Prop := match t with
| TDiscrete A => fun e => dcont e == discrete_pt _ _ (dcoq e )
| Tunit => fun _ => True
| Tpair a b => fun e => d_discrete_ok (Efst e)
   /\ d_discrete_ok (Esnd e)
end.

Context {cmcprops : CMC_Props U (ccat := ccat) (cmc := cmc)}.
Context {discrete_props : DiscreteProps D power}.

Lemma d_discrete_ok_respectful {t} : forall (e1 e2 : Expr t),
  dcoq e1 = dcoq e2 -> 
  dcont e1 == dcont e2 -> d_discrete_ok e1 -> d_discrete_ok e2.
Proof.
induction t; simpl; intros.
- rewrite <- H, <- H0. assumption.
- auto.
- destruct H1. split.
  + eapply IHt1. 3: eassumption. simpl.
    f_equal. assumption. simpl.
    apply compose_Proper. reflexivity. assumption.
  + eapply IHt2. 3: eassumption. simpl.
    f_equal. assumption. simpl.
    apply compose_Proper. reflexivity. assumption.
Qed.

Lemma d_discrete_ok_holds {t} (e : Expr t) : d_discrete_ok e.
Proof.
induction e; simpl.
- auto. 
- reflexivity. 
- simpl in IHe. destruct IHe. assumption.
- simpl in IHe. destruct IHe. assumption.
- split. apply (d_discrete_ok_respectful e1).
  simpl. reflexivity. simpl. rewrite pair_fst. reflexivity.
  assumption.
  apply (d_discrete_ok_respectful e2).
  simpl. reflexivity. simpl. rewrite pair_snd.
  reflexivity. assumption.
Qed.

Theorem full_abstract : forall (A : Ty) (e1 e2 : Expr A),
  dcoq_eq (dcoq e1) (dcoq e2) -> dcont e1 == dcont e2.
Proof.
intros. induction A.
- pose proof (d_discrete_ok_holds e1).
  unfold d_discrete_ok in H0. rewrite H0; clear H0.
  pose proof (d_discrete_ok_holds e2).
  unfold d_discrete_ok in H0. rewrite H0. 
  rewrite H. reflexivity.
- rewrite (unit_uniq (dcont e1)).
  rewrite (unit_uniq (dcont e2)). reflexivity.
- destruct H. 
  rewrite pair_uniq. rewrite (pair_uniq (dcont e2)). 
  apply pair_Proper.
  specialize (IHA1 (Efst e1) (Efst e2) H).
  simpl in IHA1. assumption.
  specialize (IHA2 (Esnd e1) (Esnd e2) H0).
  simpl in IHA2. assumption.
Qed.

Definition test : nat :=
 Datatypes.snd ( 3 , 4 ).

Definition test_Expr : Expr (TDiscrete nat) :=
  Esnd (Epair (Econst 3) (Econst 4)).

Theorem test_ok : dcoq (test_Expr) = test.
Proof.
reflexivity.
Qed.

Class IsProb {Prob : Type -> Type} :=
  { Ret : forall {A}, Prob A
  ; Map : forall {A B}, (A -> B) -> Prob A -> Prob B
  ; Strength : forall {A B}, A -> Prob B -> Prob (A * B)%type
  ; Join : forall {A}, Prob (Prob A) -> Prob A
  ; Map_Compose : forall {A B C} (f : A -> B) (g : B -> C) (mu : Prob A),
      Map (fun x => g (f x)) mu = Map g (Map f mu)
  }.

Arguments IsProb : clear implicits.

Section Samplers.

Context {Prob} {isProb : IsProb Prob}.

Definition Bind {A B} (x : Prob A) (f : A -> Prob B) : Prob B
  := Join (Map f x).

Definition indep {A B} (mu : Prob A) (nu : Prob B)
  := Bind mu (fun x => Strength x nu).

Record Sampler {A R} (mu_R : Prob R) (mu : Prob A) :=
  { sample : R -> R * A
  ; sample_ok : Map sample mu_R = indep mu_R mu
  }.

End Samplers.

End Cont.