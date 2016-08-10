Module SigAlg.

Require Import SetoidClass Morphisms.
Section Defn.

Context {A : Type}.

Record T {F : (A -> Prop) -> Prop} :=
  { top : F (fun _ => True)
  ; complement : forall {U}, F U -> F (fun x => ~ (U x))
  ; union : forall (s : nat -> A -> Prop), (forall n, F (s n)) -> F (fun x => exists n, s n x)
  ; proper :> Proper ((eq ==> iff) ==> iff) F
  }.

Arguments T : clear implicits.

Definition trivial (U : A -> Prop) : Prop :=
  (forall x, U x) \/ (forall x, ~ U x).

Require Import Coq.Logic.Classical.

Theorem Ttrivial : T trivial.
Proof.
constructor; unfold trivial; intros.
- left. intros. constructor.
- destruct H. right. auto. left. auto.
- destruct (classic (exists n, forall x, s n x)).
  left. intros. destruct H0. exists x0. apply H0. 
  right. intros. unfold not. intros.
  destruct H1.
  destruct (H x0).
  apply H0. exists x0. assumption.
  eapply H2. apply H1.
- simpl_relation. unfold respectful in H.
  assert (forall a, x a <-> y a) as xya. 
  intros. apply H. reflexivity.
  split; intros.
 destruct H0. left. intros. apply xya.
  apply H0. right. intros. rewrite <- xya. apply H0.
  destruct H0. left. intros. apply xya.
  apply H0. right. intros. rewrite xya. apply H0.
Qed.

Definition discrete (_ : A -> Prop) : Prop := True.

Theorem Tdiscrete : T discrete.
Proof.
constructor; unfold discrete; intros; auto.
repeat intro. tauto.
Qed.

Theorem intersection (F : ((A -> Prop) -> Prop) -> Prop)
  : (forall Sg, F Sg -> T Sg)
  -> T (fun U => forall Sg, F Sg -> Sg U).
Proof.
intros All.
constructor; intros.
- apply (top (All _ H)).
- apply complement.  apply All. assumption.
  apply H. apply H0.
- apply union. apply All. assumption.
  intros. apply H. apply H0.
- simpl_relation. assert (forall a, x a <-> y a) as xya.
  intros. apply H. reflexivity. admit.
Admitted.

Variable Sg : (A -> Prop) -> Prop.
Variable TSg : T Sg.

Theorem empty : Sg (fun _ => False).
Proof.
pose proof (proper TSg).
eapply (proper TSg). 2: eapply (complement TSg); apply (top TSg).
repeat intro. tauto.
Qed.

End Defn.

End SigAlg.