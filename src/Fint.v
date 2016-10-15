Require Fin.

Fixpoint lastF {n} : Fin.t (S n) := match n with
  | 0 => Fin.F1
  | S n' => Fin.FS lastF
  end.

Fixpoint weak1 {n} (x : Fin.t n) : Fin.t (S n) := 
  match x  with
  | Fin.F1 _ => Fin.F1
  | Fin.FS _ n => Fin.FS (weak1 n)
  end.

Definition dec {n} : Fin.t (S n) -> Fin.t (S n) := 
  match n as n' return Fin.t (S n') -> Fin.t (S n') with
  | 0 => fun x => x
  | S m => fun x : Fin.t (S (S m)) => match x in Fin.t m'
     return match m' with
       | S m => Fin.t (S m)
       | 0 => False end with
    | Fin.F1 _ => lastF
    | Fin.FS _ n => weak1 n
    end
  end.

Fixpoint maybe_inc {n} (x : Fin.t n) : option (Fin.t n) := match x with
  | Fin.F1 _ => None
  | Fin.FS _ x' => match maybe_inc x' with
     | None => None
     | Some incr => Some (Fin.FS incr)
     end
  end.

Definition inc {n} (x : Fin.t (S n)) : Fin.t (S n) := match maybe_inc x with
  | None => Fin.F1
  | Some y => y
  end.

Fixpoint repeatN {A} (f : A -> A) {n} (k : Fin.t n) (x : A) : A := 
  match k in Fin.t n' with
  | Fin.F1 _ => x
  | Fin.FS n' k' => (match n' as n'' return Fin.t n'' -> A with
     | 0 => fun _ => x
     | S _ => fun k'' => f (repeatN f k'' x)
     end) k'
  end.

Fixpoint repeatNat {A} (f : A -> A) (n : nat) (x : A) : A := match n with
  | 0 => x
  | S n' => f (repeatNat f n' x)
  end.

Fixpoint toNat {n} (x : Fin.t n) := match x with
  | Fin.F1 _ => 0%nat
  | Fin.FS _ x' => S (toNat x')
  end.

Definition repeatN' {A} (f : A -> A) {n} (k : Fin.t n)
  := repeatNat f (toNat k).

Definition times {n} : Fin.t (S n) -> Fin.t (S n) -> Fin.t (S n) :=
  repeatN' inc.

Delimit Scope group_scope with group.
Infix "*" := times : group_scope.

Local Open Scope group.

Theorem identL {n} : forall x : Fin.t (S n), Fin.F1 * x = x.
Proof.
intros. simpl. reflexivity.
Qed.

Lemma repeatN'prop {A} : forall n (p : Fin.t n) (x : A) f, 
   repeatN' f (Fin.FS p) x = f (repeatN' f p x).
Proof.
intros. induction p. unfold repeatN'. simpl. reflexivity.
rewrite IHp. unfold repeatN'. simpl. reflexivity.
Qed.

Theorem identR {n} : forall x : Fin.t (S n), x * Fin.F1 = x.
Proof.
generalize dependent n.
apply Fin.rectS; intros.
- reflexivity.
- unfold times in *. simpl.
  remember (repeatN inc p (@Fin.F1 (S n))) as rpn.
  unfold inc.
  destruct (maybe_inc rpn) eqn:minc.
  admit. rewrite Heqrpn in minc. simpl in minc. simpl.
Abort.