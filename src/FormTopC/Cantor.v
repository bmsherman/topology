Require Import
  CMorphisms
  FormTopC.FormTop
  Algebra.OrderC
  Algebra.SetsC
  Algebra.PreOrder
  FormTopC.FormalSpace.

Local Open Scope Subset.

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

Definition CantorPO : PreOrder :=
  {| PO_car := list A
  ; le := LE |}.

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

Definition PreCantor : PreISpace.t :=
  {| PreISpace.S := CantorPO
   ; PreISpace.C := C |}.

Local Instance loc : FormTop.localized PreCantor.
Proof.
unfold FormTop.localized.
intros a c H i. simpl in *. destruct i. exists I.
intros s H0. destruct H0.
simpl in H. destruct H. destruct zs.
- subst. rewrite !app_nil_r.
  split. exists c. reflexivity.
  simpl. econstructor. reflexivity.
  exists (c ++ [b]). econstructor. reflexivity. 
  reflexivity.
- subst. split. eexists. reflexivity.
  simpl. rewrite <- app_assoc. eexists. 
  rewrite <- app_assoc. reflexivity.
  rewrite <- app_assoc. simpl.
  econstructor. exists a0. reflexivity. 
  econstructor. rewrite <- app_assoc. simpl.
  reflexivity.
Qed.

Hypothesis inhabited : A.

(* This actually needs 'A' to be inhabited. *)
Local Instance pos : FormTop.gtPos PreCantor.
Proof.
apply gall_Pos.
intros. destruct X. subst.
induction zs.
- exists (b ++ [inhabited]).
  split. econstructor. reflexivity.
  rewrite app_nil_r. econstructor. reflexivity.
  econstructor. Focus 2. reflexivity.
  econstructor. reflexivity.
- econstructor.
Admitted.

Definition Cantor : IGt :=
  {| IGS := PreCantor
  |}.

End Cantor.
