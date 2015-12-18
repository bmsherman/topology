Require Iso.
Require Fin.

Fixpoint Fin (n : nat) : Set := match n with
  | 0 => False
  | S n' => (True + Fin n')%type
  end.

Theorem finIso (n : nat) : Iso.T (Fin.t n) (Fin n).
Proof.
induction n.
- eapply Iso.Build_T.
  intros a. inversion a.
  intros b. inversion b. 
- 
refine (
{| Iso.to := fun x => (match x in Fin.t n'
  return (S n = n') -> Fin (S n) with
   | Fin.F1 _ => fun _ => inl I
   | Fin.FS n' x' => fun pf => inr (Iso.to IHn (eq_rect n' Fin.t x' _ (eq_sym (eq_add_S _ _ pf))))
   end) eq_refl
 ; Iso.from := fun x => match x with
   | inl I => Fin.F1
   | inr x' => Fin.FS (Iso.from IHn x')
   end
|}).
intros a.
Require Import Program.
dependent destruction a; simpl.
reflexivity. rewrite Iso.from_to. reflexivity.
intros b. destruct b. destruct t. reflexivity.
  simpl. rewrite Iso.to_from. reflexivity.
Grab Existential Variables.
intros bot. contradiction.
intros f0. inversion f0.
Defined.

Lemma botNull (A : Type) : Iso.T A (A + False).
Proof.
refine (
{| Iso.to   := inl
 ; Iso.from := fun x => match x with
    | inl x' => x'
    | inr bot => False_rect A bot
   end
|}).
reflexivity.
intros b. destruct b. reflexivity. contradiction.
Qed.

Fixpoint split (m : nat)
  : forall (n : nat), Fin.t (m + n) -> (Fin.t m + Fin.t n).
refine (
  match m return (forall (n : nat), Fin.t (m + n) -> (Fin.t m + Fin.t n)) with
  | 0 => fun _ => inr
  | S m' => fun n x => (match x as x0 in Fin.t k 
    return forall (pf : k = (S m' + n)), (Fin.t (S m') + Fin.t n) with
    | Fin.F1 _ => fun pf => inl Fin.F1
    | Fin.FS n' x' => fun pf => _
    end) eq_refl
  end).
simpl in pf.
apply eq_add_S in pf.
rewrite pf in x'.
refine (match split m' n x' with
  | inl a => inl (Fin.FS a)
  | inr b => inr b
  end).
Defined.

Lemma splitL : forall {m n : nat} {x : Fin.t m},
  split m n (Fin.L n x) = inl x.
Proof.
intros m. induction m; intros n x.
- inversion x.
- dependent destruction x; simpl.
  + reflexivity.
  + rewrite (IHm n x). reflexivity.
Qed.

Lemma splitR : forall {m n : nat} {x : Fin.t n},
  split m n (Fin.R m x) = inr x.
Proof.
intros m. induction m; intros n x; simpl.
- reflexivity.
- rewrite (IHm n x). reflexivity.
Qed.

Lemma splitInj : forall {m n : nat} {x y : Fin.t (m + n)},
  split m n x = split m n y -> x = y.
Proof.
intros m; induction m; intros n x y Heq.
- inversion Heq. reflexivity.
- dependent destruction x; dependent destruction y.
  + reflexivity.
  + simpl in Heq. destruct (split m n y); inversion Heq.
  + simpl in Heq. destruct (split m n x); inversion Heq.
  + apply f_equal. simpl in Heq. apply IHm.
    destruct (split m n x) eqn:sx;
    destruct (split m n y) eqn:sy.
    apply f_equal. 
    assert (forall (A B : Type) (x y : A), @inl A B x = @inl A B y -> x = y).
    intros A B x0 y0 Heqn. inversion Heqn. reflexivity.
    apply H in Heq. apply Fin.FS_inj in Heq. assumption.
    inversion Heq. inversion Heq. apply f_equal. injection Heq. trivial.
Qed.

Fixpoint splitMult (m : nat)
  : forall (n : nat), Fin.t (m * n) -> (Fin.t m * Fin.t n) 
  := match m return (forall (n : nat), Fin.t (m * n) -> (Fin.t m * Fin.t n)) with
  | 0 => fun _ => Fin.case0 _
  | S m' => fun n x => match split n (m' * n) x with
    | inl a => (Fin.F1, a)
    | inr b => match splitMult m' n b with
      | (x, y) => (Fin.FS x, y)
      end
    end
  end.


Lemma finPlus : forall {m n : nat},
  Iso.T (Fin.t m + Fin.t n) (Fin.t (m + n)).
Proof.
intros m n.
refine (
{| Iso.to := fun x => match x with
   | inl a => Fin.L n a
   | inr b => Fin.R m b
   end
 ; Iso.from := split m n
|}).
intros. destruct a; simpl. induction m; simpl.
- inversion t.
Require Import Program.
- dependent destruction t; simpl.
  + reflexivity.
  + rewrite IHm. reflexivity.
- induction m; simpl. reflexivity. rewrite IHm. reflexivity.
- induction m; intros; simpl.
  + reflexivity.
  + dependent destruction b; simpl. reflexivity.
     pose proof (IHm b).
     destruct (split m n b) eqn:seqn;
     simpl; rewrite H; reflexivity.
Qed.

Lemma finMult : forall {m n : nat},
  Iso.T (Fin.t m * Fin.t n) (Fin.t (m * n)).
Proof.
intros m n.
refine (
{| Iso.to := fun x => match x with (a, b) => Fin.depair a b end
 ; Iso.from := splitMult m n
|}).
intros p. destruct p.
induction m; simpl.
- inversion t.
- dependent destruction t; simpl.
  + rewrite splitL. reflexivity.
  + rewrite splitR. rewrite (IHm t). reflexivity.

- induction m; intros b; simpl.
  + inversion b.
  + destruct (split n (m * n) b) eqn:seqn.
    * simpl. rewrite <- splitL in seqn. 
      apply splitInj in seqn. symmetry. assumption.
    * pose proof (IHm t). assert (b = Fin.R n t).
      apply splitInj. rewrite seqn. symmetry. apply splitR.
      rewrite H0. simpl.
      destruct (splitMult m n t) eqn:smeqn.
      simpl. rewrite <- H. reflexivity.
Defined.

Fixpoint pow (b e : nat) : nat := match e with
  | 0 => 1
  | S e' => b * pow b e'
  end.

Theorem finPow : forall {e b : nat},
  Iso.T (Fin.t (pow b e)) (Fin.t e -> Fin.t b).
Proof.
intros e. induction e; intros n; simpl.
- eapply Iso.Trans. apply finIso. simpl. eapply Iso.Trans.
  eapply Iso.Sym. apply botNull. eapply Iso.Trans. Focus 2.
  eapply Iso.FuncCong. eapply Iso.Sym. apply finIso. apply Iso.Refl.
  simpl. apply Iso.Sym. apply Iso.FFunc.
- eapply Iso.Trans. eapply Iso.Sym. apply finMult.
  eapply Iso.Trans. Focus 2. eapply Iso.FuncCong.
  eapply Iso.Sym. apply finIso. apply Iso.Refl.
  simpl. eapply Iso.Trans. Focus 2. eapply Iso.Sym. eapply Iso.PlusFunc.
  apply Iso.TFunc. eapply Iso.Trans. eapply Iso.FuncCong.
  eapply Iso.Sym. apply finIso. apply Iso.Refl. eapply Iso.Sym.
  apply IHe. apply Iso.Refl.
Qed.

Inductive U : Set :=
  | U0    : U
  | U1    : U
  | UPlus : U -> U -> U
  | UTimes : U -> U -> U
  | UFunc : U -> U -> U
  | UFint : nat -> U
  | UFin : nat -> U.

Fixpoint ty (t : U) : Set := match t with
  | U0 => False
  | U1 => True
  | UPlus a b => (ty a + ty b)%type
  | UTimes a b => (ty a * ty b)%type
  | UFunc a b => ty a -> ty b
  | UFint n => Fin.t n
  | UFin n => Fin n
  end.

Fixpoint card (t : U) : nat := match t with
  | U0 => 0
  | U1 => 1
  | UPlus a b => card a + card b
  | UTimes a b => card a * card b
  | UFunc a b => pow (card b) (card a)
  | UFint n => n
  | UFin n => n
  end.
    
Theorem finChar (t : U) : Iso.T (ty t) (Fin.t (card t)).
Proof.
induction t; simpl.
- apply Iso.Sym. apply (finIso 0).
- apply Iso.Sym. apply (@Iso.Trans _ (Fin 1)). apply (finIso 1).
  apply Iso.Sym. apply botNull.
- eapply Iso.Trans. eapply Iso.PlusCong. eassumption.
  eassumption.
  apply finPlus.
- eapply Iso.Trans. eapply Iso.TimesCong; try eassumption.
  apply finMult.
- eapply Iso.Trans. eapply Iso.FuncCong; try eassumption.
  apply Iso.Sym. apply finPow.
- apply Iso.Refl.
- apply Iso.Sym. apply finIso.
Qed.

Inductive T : Type -> Type :=
  | F0 : T False
  | F1 : T True
  | FPlus : forall {A B}, T A -> T B -> T (A + B)
  | FIso : forall {A B}, T A -> Iso.T A B -> T B
.



Lemma finiteSig {A : Type} (fa : T A)
  : forall {B : A -> Type}, 
  (forall (x : A), T (B x))
  -> sigT (fun S => (T S * Iso.T (sigT B) S)%type).
Proof.
induction fa; intros b fb.
- exists False. split. constructor. apply Iso.FSig.
- exists (b I). split. apply fb. apply Iso.TSig.
- pose proof (IHfa1 (fun x => b (inl x)) (fun x => fb (inl x))).
  pose proof (IHfa2 (fun x => b (inr x)) (fun x => fb (inr x))).
  destruct X. destruct X0. destruct p. destruct p0.
  exists (x + x0)%type. split.
  constructor; assumption.
  apply Iso.PlusSig; assumption.
- pose (Iso.Sym t).
  pose proof (IHfa (fun x => b (Iso.from t0 x))
                   (fun x => fb (Iso.from t0 x))).
  destruct X. destruct p.
  exists x. split. assumption.
  eapply Iso.Trans. Focus 2. apply t2.
  admit.
  (*apply Iso.sigmaProp.*)
Defined.

Theorem sig {A : Type} {B : A -> Type} 
  : T A 
  -> (forall (x : A), T (B x))
  -> T (sigT B).
Proof.
intros fA fB.
pose proof (finiteSig fA fB).
destruct X. destruct p.
eapply FIso. apply t.
apply Iso.Sym. assumption.
Defined.


Theorem times {A B : Type} : T A -> T B -> T (A * B).
Proof.
intros fa fb.
eapply FIso. Focus 2. eapply Iso.Sym. eapply Iso.sigTimes.
apply sig. assumption. apply (fun _ => fb).
Defined.

Fixpoint finiteMapped {A : Type} (fa : T A)
  : forall {B : Type}, T B -> sigT (fun S => (T S * Iso.T (A -> B) S)%type).
Proof.
induction fa.
- exists True. apply (F1, Iso.FFunc).
- intros B fb. exists B. apply (fb, Iso.TFunc).
- intros B1 fb.
  destruct (IHfa1 B1 fb). destruct (IHfa2 B1 fb).
  exists (x * x0)%type.
  destruct p. destruct p0.
  apply (times t t1, Iso.PlusFunc t0 t2).
- intros B1 fb.
  destruct (IHfa B1 fb).
  destruct p.
  exists x.
  split.
  assumption.  
  eapply Iso.Trans.
  eapply Iso.Sym.
  apply (Iso.FuncCong t (Iso.Refl B1)).
  assumption.
Defined.

Theorem func {A B : Type} : T A -> T B -> T (A -> B).
Proof.
intros FA FB.
pose proof (finiteMapped FA FB).
destruct X.
destruct p.
eapply FIso.
eassumption.
apply Iso.Sym.
assumption.
Defined.

Theorem eq_dec {A : Type} : T A -> forall a b : A, {a = b} + {a <> b}.
Proof.
intros finite.
induction finite; intros; try (decide equality).
- destruct a, b. left. reflexivity.
- destruct (IHfinite (Iso.from t a) (Iso.from t b)).
  + left. 
    replace a with (Iso.to t (Iso.from t a)) by apply Iso.to_from.
    replace b with (Iso.to t (Iso.from t b)) by apply Iso.to_from.
    f_equal. assumption.
  + right. congruence.
Qed.