Require Import 
  Algebra.SetsC
  Algebra.OrderC
  Algebra.PreOrder
  Types.List
  Coq.Lists.List.

Import ListNotations.

Local Open Scope FT.

Module ML.
Section FreeMeetLattice.

Context {X : PreOrder}
        {POX : PreO.t (le X)}.

Definition FreeML : PreOrder :=
  {| PO_car := list X
  ; le := fun a b => Each (fun ub => LSome (fun ua => ua <=[X] ub) a) b 
  |}.

Global Instance PO : PreO.t (le FreeML).
Proof.
constructor; simpl; intros. 
- intros x' mem. econstructor. eassumption.
  reflexivity.
- unfold Each. intros. 
  specialize (X1 x0 X2). simpl in X1.
  induction X1.
  specialize (X0 _ S_member). simpl in X0.
  induction X0.
  econstructor. eassumption.
  etransitivity; eassumption.
Qed.

Lemma FSubset_le (xs ys : FreeML) : (ys ⊆ xs)%list -> xs <= ys.
Proof.
simpl. unfold FSubset, Each.
intros H x mem.
eexists x. apply H. assumption.
reflexivity.
Qed.

Local Open Scope Subset.

Definition bmeet (xs ys : FreeML) : FreeML := xs ++ ys.

Local Infix "++" := bmeet.

Lemma bmeet_le_r (l r : FreeML)
  : l ++ r <= r.
Proof.
unfold bmeet. apply FSubset_le. apply FSubset_app_r.
Qed.

Lemma bmeet_le_l (l r : FreeML)
  : l ++ r <= l.
Proof.
unfold bmeet. apply FSubset_le. apply FSubset_app_l.
Qed.

Lemma app_le (xs ys : FreeML) : 
  xs <= ys -> xs <= (xs ++ ys).
Proof.
simpl. unfold bmeet, Each. intros H x mem.
apply member_app in mem. induction mem.
- econstructor. eassumption. reflexivity.
- apply H. assumption.
Qed.

Lemma le_app_r (xs xs' ys : FreeML)
  : xs <= xs' -> (xs ++ ys) <= (xs' ++ ys).
Proof.
simpl. unfold Each, bmeet. intros H x mem.
apply member_app in mem. apply LSome_app.
induction mem.
- left. apply H. assumption.
- right. econstructor. eassumption. reflexivity. 
Qed.

Definition inj (a : X) : FreeML := [a].

Lemma le_singleton (a b : X)
  : a <= b -> inj a <= inj b.
Proof.
simpl; unfold Each, inj; intros H x mem.
apply member_singleton in mem.
subst. econstructor. econstructor. eassumption.
Qed.

Lemma le_singleton_opp (a b : X)
  : inj a <= inj b -> a <= b.
Proof.
simpl; unfold Each, inj; intros H.
specialize (H _ here). induction H.
apply member_singleton in S_member.
subst. assumption.
Qed.

Lemma bmeet_comm (xs ys : FreeML)
  : (xs ++ ys) <= (ys ++ xs).
Proof.
simpl. unfold Each, bmeet. intros x mem.
apply member_app in mem. apply LSome_app.
induction mem; [right | left]; 
  (econstructor; [eassumption | reflexivity]).
Qed.

Lemma le_app_l (ys ys' xs : FreeML)
  : ys <= ys' -> (ys ++ xs) <= (ys' ++ xs).
Proof.
intros H.
rewrite (bmeet_comm ys).
etransitivity.
Focus 2. eapply le_app_r. eassumption.
apply bmeet_comm.
Qed.

Lemma le_app_distr {xs xs' ys ys' : FreeML}
  : xs <= xs' -> ys <= ys' -> (xs ++ ys) <= (xs' ++ ys').
Proof.
simpl. unfold Each, bmeet.
intros Hx Hy x mem.
apply member_app in mem. apply LSome_app.
induction mem.
- left. apply Hx. assumption.
- right. apply Hy. assumption.
Qed.

Lemma le_cons (a b : X) (xs ys : FreeML)
  : a <= b -> xs <= ys -> (inj a ++ xs) <=[FreeML] (inj b ++ ys).
Proof.
intros H H'.
apply (@le_app_distr [a] [b] xs ys).
apply le_singleton. assumption. assumption.
Qed.

Lemma le_cons_r {xs ys : FreeML} {a : X}
  (Ha : xs <= inj a) (Hys : xs <= ys)
  : xs <=[FreeML] (inj a ++ ys).
Proof.
simpl. unfold Each.
intros x mem. inv mem.
- apply Ha. constructor.
- apply Hys. assumption.
Qed.

Lemma le_app_each (l x y : FreeML)
  (lx : l <= x) (ly : l <= y)
  : l <= (x ++ y).
Proof.
simpl. unfold Each, bmeet. intros u mem.
apply member_app in mem. destruct mem.
- apply lx. assumption.
- apply ly. assumption.
Qed.

Lemma down_app (b c : FreeML) : (eq b ↓ eq c) === ⇓ (eq (b ++ c) : FreeML -> Prop).
Proof.
apply Same_set_iff.
intros bc. split; intros.
- destruct X0. le_downH d. le_downH d0.
  le_down.
  apply le_app_each; assumption.
- le_downH X0. split; le_down.
  etransitivity. eassumption. apply FSubset_le.
  apply FSubset_app_l.
  etransitivity. eassumption. apply FSubset_le. 
  apply FSubset_app_r.
Qed.

Lemma Each_monotone (P : X -> Type)
  (Pmono : forall x y, x <= y -> P x -> P y)
  (xs ys : FreeML)
  (H : xs <= ys) : Each P xs -> Each P ys.
Proof.
intros E x mem. specialize (H x mem).
simpl in H. induction H.
eapply Pmono. eassumption. apply E. assumption.
Qed.

End FreeMeetLattice.
End ML.


Arguments ML.FreeML : clear implicits.

Delimit Scope FreeML_scope with FreeML.
Infix "∧" := ML.bmeet (at level 60) : FreeML_scope.
