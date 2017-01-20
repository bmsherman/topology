
Inductive Ty : Type :=
  | TDiscrete : Set -> Ty
  | Tunit : Ty
  | Tpair : Ty -> Ty -> Ty
  | Tfunc : Ty -> Ty -> Ty.

Require Import Coq.Lists.List. 
Import ListNotations.

Fixpoint prodTy (xs : list Ty) : Ty := match xs with
 | nil => Tunit
 | x :: xs' => Tpair (prodTy xs') x
 end.

Fixpoint dcoqT (t : Ty) : Type := match t with
| Tunit => unit
| TDiscrete A => A
| Tpair a b => prod (dcoqT a) (dcoqT b)
| Tfunc a b => dcoqT a -> dcoqT b
end.

Definition dcoqTG Γ A := dcoqT (prodTy Γ) -> dcoqT A.

Section Cont.
Require Import Spec.Category Spec.Discrete.
Import Category.
Import Discrete.
Require Import Spec.CCC.CCC Types.List.
Import CCC.
Context {U : Type} {ccat : CCat U} {cmc : CMC U}
  {ccc : CCCOps U}
  {D : Type -> U} {power : Type -> U -> U} 
  {Dops : DiscreteOps D}
  {cmcprops : CMC_Props U}
  {cccprops : CCCProps U}
  {discrete_props : DiscreteProps D}.

Local Open Scope obj.
Local Open Scope morph.

Fixpoint dcontT (t : Ty) : U := match t with
| TDiscrete A => D A
| Tunit => unit
| Tpair a b => dcontT a * dcontT b
| Tfunc a b => dcontT a ==> dcontT b
end.

Definition dcontTG Γ A := dcontT (prodTy Γ) ~~> dcontT A.

Fixpoint Rel {ty : Ty} : dcoqT ty -> unit ~~> dcontT ty -> Type := match ty with
| TDiscrete A => fun e1 e2 => e2 == discrete_pt e1
| Tunit => fun _ _ => True
| Tpair _ _ => fun e1 e2 => (Rel (Datatypes.fst e1) (fst ∘ e2)
    * Rel (Datatypes.snd e1) (snd ∘ e2))%type
| Tfunc _ _ => fun f1 f2 => forall x1 x2, Rel x1 x2 ->
    Rel (f1 x1) (eval ∘ ⟨ f2 , x2 ⟩) 
end.

Lemma Rel_uniq_cont {ty : Ty} : forall (eC : dcoqT ty)
  (e1 e2 : unit ~~> dcontT ty),
  Rel eC e1 -> Rel eC e2 -> e1 == e2.
Proof.
induction ty; simpl; intros.
- rewrite X, X0. reflexivity. 
- rewrite (unit_uniq e1), (unit_uniq e2).
  reflexivity.
- destruct X, X0. 
  rewrite (pair_uniq e1), (pair_uniq e2).
  apply pair_Proper. eapply IHty1; eassumption.
  eapply IHty2; eassumption.
- rewrite <- (abstract_eval e1), <- (abstract_eval e2).
  unfold parallel.
Abort.

Fixpoint dcoq_eq {A : Ty} : dcoqT A -> dcoqT A -> Type
  := match A as A' return dcoqT A' -> dcoqT A' -> Type with
| Tunit => fun _ _ => True
| TDiscrete _ => Logic.eq
| Tpair a b => fun e1 e2 => (dcoq_eq (Datatypes.fst e1) (Datatypes.fst e2)
    * dcoq_eq (Datatypes.snd e1) (Datatypes.snd e2))%type
| Tfunc a b => fun f1 f2 => forall x1 x2 : dcoqT a, dcoq_eq x1 x2 -> dcoq_eq (f1 x1) (f2 x2)
end.

Definition dcoqG_eq {Γ A} : dcoqTG Γ A -> dcoqTG Γ A -> Type :=
  fun f1 f2 => forall x1 x2, dcoq_eq x1 x2 -> dcoq_eq (f1 x1) (f2 x2).

Require Import CMorphisms.
Instance dcoq_eq_Equiv {A} : Equivalence (@dcoq_eq A).
Proof.
constructor; unfold Reflexive, Symmetric, Transitive.
- induction A; intros; simpl; auto.
  intros. 
Admitted.

Instance dcoqG_eq_Equiv {Γ A} : Equivalence (@dcoqG_eq Γ A).
Proof.
constructor; unfold Reflexive, Symmetric, Transitive, dcoqG_eq; intros.
- admit.
- symmetry. apply X. symmetry. assumption.
- etransitivity. apply X. eassumption. apply X0. reflexivity.
Admitted. 

Lemma Rel_respectful {ty} :
  Proper (dcoq_eq ==> eq ==> arrow) (@Rel ty).
Proof.
unfold Proper, respectful, arrow.
induction ty; simpl; intros.
- subst. intros. 
  rewrite <- X0. symmetry. assumption.
- auto.
- destruct X, X1. split.
  + eapply IHty1. eassumption.
    apply compose_Proper. reflexivity. eassumption. assumption.
  + eapply IHty2. eassumption.
    apply compose_Proper. reflexivity. eassumption. assumption.
- eapply IHty2. apply X. Focus 2. rewrite <- X0. reflexivity. reflexivity.
  apply X1. eassumption.
Qed.

Instance Rel_respectful' {ty}
  : Proper (dcoq_eq ==> eq ==> iffT) (@Rel ty).
Proof.
unfold Proper, respectful. intros.
split; apply Rel_respectful; repeat (assumption || symmetry).
Qed.

Definition subst_coq {Γ A B} (e : dcoqTG (A :: Γ) B)
  (x : dcoqTG Γ A) : dcoqTG Γ B
  := fun ctxt => e (ctxt, x ctxt).

Definition subst_cont {Γ A B} (e : dcontTG (A :: Γ) B)
  (x : dcontTG Γ A) : dcontTG Γ B
  := e ∘ ⟨ id , x ⟩.

Fixpoint RelG {Γ} {A : Ty} : dcoqTG Γ A -> dcontTG Γ A -> Type := 
  match Γ as Γ' return dcoqTG Γ' A -> dcontTG Γ' A -> Type with
| [] => fun e1 e2 => Rel (e1 Datatypes.tt) e2
| X :: Xs => fun f1 f2 => forall x1 x2, RelG x1 x2 ->
     RelG (subst_coq f1 x1) (subst_cont f2 x2)
end.

Lemma RelG_respectful {Γ A}
  : Proper (dcoqG_eq ==> eq ==> arrow) (@RelG Γ A).
Proof.
unfold Proper, respectful. 
induction Γ; unfold dcoqG_eq, arrow; simpl; intros.
- rewrite <- X, <- X0. eassumption. auto.
- unfold arrow in IHΓ. eapply IHΓ. 3: apply X1. 3: eassumption. 
  unfold dcoqG_eq. intros. 
  apply X. simpl. split. assumption.
  assert (dcoqG_eq x1 x1) as H4 by reflexivity.
  apply H4. assumption.
  unfold subst_cont. rewrite X0. reflexivity.
Qed.

Instance RelG_respectful' {Γ A}
  : Proper (dcoqG_eq ==> eq ==> iffT) (@RelG Γ A).
Proof.
unfold Proper, respectful. intros.
split; apply RelG_respectful; repeat (assumption || symmetry).
Qed.







Inductive Constant {Γ} {A : Ty} : Type := MkConst
  { Ccoq : dcoqTG Γ A
  ; Ccont : dcontTG Γ A
  ; Crel : RelG Ccoq Ccont }.

Arguments Constant : clear implicits.

Definition Constant_subst {Γ A B} (f : Constant (A :: Γ) B)
  (x : Constant Γ A) : Constant Γ B.
Proof.
destruct f, x; simpl in *.
unshelve econstructor.
- eapply subst_coq; eassumption. 
- eapply subst_cont; eassumption.
- apply Crel0. assumption. 
Defined.

Definition Constant_swap {Γ A B C} (x : Constant (A :: B :: Γ) C)
  : Constant (B :: A :: Γ) C.
Proof.
unshelve econstructor.
- unfold dcoqTG in *. simpl in *.
  intros. apply (Ccoq x). destruct X as ((g & a) & b).
  simpl. auto. 
- unfold dcontTG in *. simpl in *.
  refine (Ccont x ∘ _).
  apply (⟨ ⟨ fst ∘ fst , snd ⟩ , snd ∘ fst ⟩).
- apply undefined.
Defined.

Definition Constant_weak {Γ A B} (x : Constant Γ B)
  : Constant (A :: Γ) B.
Proof.
unshelve econstructor.
- unfold dcoqTG in *. simpl. intros.
  apply (Ccoq x). apply (Datatypes.fst X).
- unfold dcontTG in *. simpl. 
  apply (Ccont x ∘ fst).
- simpl. intros. unfold subst_coq, subst_cont.
  simpl. rewrite <- compose_assoc. rewrite pair_fst.
  rewrite compose_id_right. apply x.
Defined.

Inductive termDB {G : list Ty} : Ty -> Type :=
  | VarDB : forall {t}, member t G -> termDB t
  | ConstDB : forall {A : Ty}, Constant G A -> termDB A
  | AbsDB : forall {dom ran}, @termDB (dom :: G) ran -> termDB (Tfunc dom ran)
  | AppDB : forall {dom ran}, termDB (Tfunc dom ran) -> termDB dom -> termDB ran.

Arguments termDB : clear implicits.

Ltac inv H := inversion H; clear H; subst.

Fixpoint swapDB {Γ A B C} (e : termDB (A :: B :: Γ) C)
  : termDB (B :: A :: Γ) C
  := match e with
 | VarDB m => VarDB (swap_member m)
 | ConstDB c => ConstDB (Constant_swap c)
 | AbsDB f => undefined _
 | AppDB f x => AppDB (swapDB f) (swapDB x)
end.

Lemma termDB_rect1 :
forall P : forall (A : Ty) (G : list Ty) (t : Ty), termDB (A :: G) t -> Type,
(forall A (G : list Ty) (t : Ty) (m : member t (A :: G)), P A G t (VarDB m)) ->
(forall A' (G : list Ty) (A : Ty) (c : Constant (A' :: G) A), P A' G A (ConstDB c)) ->
(forall A (G : list Ty) (dom ran : Ty) (t : termDB (A :: dom :: G) ran),
 P A (dom :: G) ran t -> P dom G (Tfunc A ran) (AbsDB t)) ->
(forall A (G : list Ty) (dom ran : Ty) (t : termDB (A :: G) (Tfunc dom ran)),
 P A G (Tfunc dom ran) t -> forall t0 : termDB (A :: G) dom, P A G dom t0 -> P A G ran (AppDB t t0)) ->
forall A (G : list Ty) (t : Ty) (t0 : termDB (A :: G) t), P A G t t0.
Proof.
intros P X X0 X1 X2.
pose (fun G : list Ty => match G as GG return forall t : Ty, termDB GG t -> Type with
 | [] => fun t term => True
 | A :: G' => P A G'
 end) as P'.
assert (forall G t t0, P' G t t0).
intros. 
induction t0; destruct G; simpl; auto.
intros A G. specialize (X3 (A :: G)). assumption.
Defined.

Definition substDB1_xx :
  forall A Γ B, termDB (A :: Γ) B -> Constant Γ A -> termDB Γ B.
Proof.
apply (termDB_rect1 (fun A Γ B _ => Constant Γ A -> termDB Γ B));
  intros.
- generalize dependent X. generalize dependent G.
  generalize dependent A. generalize dependent t.
  apply (member_rect1 _ (fun t A G _ => Constant G A -> termDB G t)). 
  + intros. apply ConstDB. assumption.
  + intros. apply VarDB. assumption.
- apply ConstDB. eapply Constant_subst; eassumption.
- apply AbsDB. admit. 
- eapply AppDB. apply X. assumption. apply X0. assumption.
Admitted. 

Fixpoint substDB {Γ A B} (e : termDB (A :: Γ) B)
  : Constant Γ A -> termDB Γ B :=
 match e with
 | VarDB m => match m with
   | here => fun k => ConstDB k
   | there next => fun _ => VarDB next
   end
 | ConstDB c => fun k => ConstDB (Constant_subst c k)
 | AbsDB f => undefined _
 | AppDB f x => fun k => AppDB (substDB f k) (substDB x k)
end.


Lemma lookup {G : list Ty} {t : Ty} (m : member t G)
  (e : dcoqT (prodTy G)) : dcoqT t.
Proof.
induction m; simpl in *; intros.
- exact (Datatypes.snd e).
- exact (IHm (Datatypes.fst e)).
Defined.

Axiom undefined : forall A, A.

Set Asymmetric Patterns.

Fixpoint dcoq_DB {Γ : list Ty} {A : Ty} (e : termDB Γ A)
 : dcoqT (prodTy Γ) -> dcoqT A
  := match e with
| VarDB _ m => fun ctxt => lookup m ctxt
| ConstDB _ (MkConst c _ _) => fun ctxt => c ctxt
| AbsDB _ _ lam => fun ctxt x => dcoq_DB lam (ctxt , x)
| AppDB _ _ f x => fun ctxt => (dcoq_DB f ctxt) (dcoq_DB x ctxt)
end.

Lemma substDB_coq  {Γ A B} (e : termDB (A :: Γ) B) (C : Constant Γ A)
  : dcoqG_eq (subst_coq (dcoq_DB e) (Ccoq C))
             (dcoq_DB (substDB e C)).
Proof.
generalize dependent C.
generalize dependent B. generalize dependent Γ.
generalize dependent A. 
apply (termDB_rect1 (fun A Γ B e => 
  forall C, dcoqG_eq (subst_coq (dcoq_DB e) (Ccoq C)) (dcoq_DB (substDB e C)))); intros.
- unfold subst_coq. admit.
- simpl. destruct c, C. simpl.
  unfold subst_coq. reflexivity.
Admitted.

Definition dcoq_closed {A : Ty} (e : termDB [] A)
  : dcoqT A := dcoq_DB e Datatypes.tt.


Lemma lookup_cont (G : list Ty) (t : Ty) (m : member t G)
  : dcontT (prodTy G) ~~> dcontT t.
Proof.
induction m; intros.
- exact (snd).
- exact (IHm ∘ fst).
Defined.

Definition dcont_DB {Γ : list Ty} {A : Ty} (e : termDB Γ A)
  : dcontT (prodTy Γ) ~~> dcontT A.
Proof.
induction e.
- apply lookup_cont. assumption.
- induction c. assumption.
- simpl. apply abstract. apply IHe.
- refine (eval ∘ _). eapply pair; eassumption.
Defined.

Lemma substDB_cont  {Γ A B} (e : termDB (A :: Γ) B) (C : Constant Γ A)
  : subst_cont (dcont_DB e) (Ccont C) == 
             dcont_DB (substDB e C).
Proof.
Admitted.


Lemma pair_parallel_snd : forall {A B C} (f : A ~~> B)
  (x : A ~~> C), ⟨ f , x ⟩ == (f ⊗ id) ∘ ⟨ id , x ⟩.
Proof.
intros. rewrite parallel_pair. rewrite compose_id_right, compose_id_left.
reflexivity.
Qed.

Theorem fst_constant {Γ A B} : Constant Γ (Tfunc (Tpair A B) A).
Proof.
unshelve econstructor; simpl.
- unfold dcoqTG. simpl. intros. destruct X0. assumption.
- unfold dcontTG. simpl.
  apply abstract. apply (fst ∘ snd).
- induction Γ; simpl; intros.
  + destruct x1, X. simpl in *. rewrite pair_parallel_snd. 
    rewrite compose_assoc. rewrite eval_abstract.
    rewrite <- compose_assoc. rewrite pair_snd. assumption.
  + eapply RelG_respectful'. 3 :eassumption. reflexivity.
    unfold subst_cont.
    unfold dcontTG in *. 
    pose proof (abstract_ext (B := dcontT A) (fst (B := dcontT B) ∘ snd) ⟨ id, x2 ⟩).
    rewrite X0. apply abstract_Proper.
    rewrite <- compose_assoc. rewrite parallel_snd.
    rewrite compose_id_left. reflexivity.
Defined.

Lemma RelG_substDB {Γ A B} (e : termDB (A :: Γ) B)
  (C : Constant Γ A) :
  RelG (dcoq_DB e) (dcont_DB e) ->
  RelG (dcoq_DB (substDB e C)) (dcont_DB (substDB e C)).
Proof.
generalize dependent C.
Admitted.

  
Theorem compiler_correct : forall Γ A (e : termDB Γ A),
  RelG (dcoq_DB e) (dcont_DB e).
Proof.
intros. induction e.
- induction m.
  + simpl. intros. unfold subst_coq, subst_cont. simpl. 
    rewrite pair_snd. assumption. 
  + simpl in *. intros. eapply RelG_respectful'. 3: apply IHm.
    reflexivity. unfold subst_cont.
    rewrite <- compose_assoc. simpl. rewrite pair_fst.
    rewrite compose_id_right. reflexivity.
- induction c. assumption.
- simpl. induction G; simpl in *; intros.
  + eapply Rel_respectful'. simpl. 3: apply IHe. Unshelve.
    Focus 4. unfold dcoqTG. simpl. intros; assumption.
    unfold subst_coq. reflexivity.
    rewrite pair_parallel_snd. rewrite compose_assoc.
    rewrite eval_abstract. apply compose_Proper. reflexivity.
    Focus 3. unfold dcontTG. simpl. assumption. reflexivity.
    simpl. assumption.
  + eapply RelG_respectful'. 3: apply IHG. Unshelve. 
    Focus 4.
    eapply substDB. Focus 2. eapply Constant_weak.
    econstructor; eassumption. apply swapDB. assumption.
    admit. admit. admit.
- induction G; intros.
  + simpl. eapply IHe1. assumption.
  + repeat intro. pose (MkConst _ _ x1 x2 X) as C.
    change x1 with (Ccoq C). change x2 with (Ccont C).
    eapply RelG_respectful'.
    apply substDB_coq. apply substDB_cont.
    simpl. apply IHG; apply RelG_substDB; assumption.
Admitted.


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