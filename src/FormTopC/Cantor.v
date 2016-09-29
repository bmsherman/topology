Require Import
  FormTopC.FormTop
  Algebra.OrderC
  CMorphisms
  FormTopC.Bundled.

(** An inductively generated formal topology for the Cantor space.
    See Section 4.1 of [1]. *)
Section Cantor.

Variable A : Type.

Require Import Coq.Lists.List.
Import ListNotations.

Inductive C {s : list A} {i : True} {s' : list A} : Type := 
  | CSplit : forall b, s' = s ++ [b] -> C.

Arguments C : clear implicits.

Inductive LE {xs ys : list A} : Type :=
  | IsLE : forall zs, xs = ys ++ zs -> LE.
Arguments LE : clear implicits.

Local Instance LE_PO : @PO.t (list A) LE eq.
Proof.
constructor; intros.
- constructor; intros.
  + exists nil. rewrite app_nil_r. reflexivity.
  + destruct X, X0.
    exists (zs0 ++ zs). rewrite e, e0.
    rewrite app_assoc. reflexivity.
- unfold Proper, respectful. 
  intros. subst. reflexivity. 
- destruct X, X0.
  rewrite e0 in e. rewrite <- app_assoc in e.
  rewrite <- app_nil_r in e at 1.
  apply app_inv_head in e.
  symmetry in e. apply app_eq_nil in e.
  destruct e. subst. rewrite app_nil_r.
  reflexivity.
Defined.

Local Instance loc : FormTop.localized LE C.
Proof.
unfold FormTop.localized.
intros a c H i. unfold Ix in *. destruct i. exists I.
intros s H0. destruct H0.
simpl in H. destruct H. destruct zs.
- subst.
  exists (c ++ [b]). split. exists b. reflexivity.
  unfold FormTop.down. split; simpl.
  exists (b :: nil). reflexivity.
  exists nil. repeat rewrite app_nil_r. reflexivity.
- exists (c ++ a0 :: nil). split. exists a0. reflexivity.
  unfold FormTop.down. split; simpl.
  exists [b]. assumption. exists (zs ++ [b]).
  rewrite <- app_assoc. simpl.
  rewrite e. rewrite e0. rewrite <- app_assoc. reflexivity.
Qed.

(* This actually needs 'A' to be inhabited. *)
Local Instance pos : FormTop.gtPos LE C.
Proof.
Admitted.

Definition Cantor : IGT :=
  {| Bundled.S := list A
  ;  Bundled.C := C
  ;  Bundled.localized := loc
  |}.

End Cantor.
