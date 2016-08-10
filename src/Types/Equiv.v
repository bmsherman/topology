Require Import FunctionalExtensionality.

Set Asymmetric Patterns.

Module EqualNotations.

Infix "#" := f_equal (at level 30, right associativity) : equal_scope.
Infix "@" := eq_trans (at level 60) : equal_scope.
Delimit Scope equal_scope with equal.

End EqualNotations.

Module Equiv. 
Import EqualNotations.
Local Open Scope equal.

(** Equivalences between types. *)
Record T { A B : Type } : Type :=
  { to    : A -> B
  ; from  : B -> A
  ; from_to : forall (a : A), from (to a) = a
  ; to_from : forall (b : B), to (from b) = b
  ; tau : forall (a : A), f_equal to (from_to a) = to_from (to a)  
  }.

Arguments T : clear implicits.

(** Isomorphisms form an equivalence relation: they are reflexivity,
    symmetric, and transitive. *)
Theorem Refl (A : Type) : T A A.
Proof.
refine (
  {| to   := fun x => x
   ; from := fun x => x
   ; from_to := fun _ => eq_refl
   ; to_from := fun _ => eq_refl |});
reflexivity.
Defined.

Definition f_equal_compose A B C (g : B -> C) (f : A -> B) x y (H : x = y) :
  g # f # H = (fun a => g (f a)) # H :=
  match H with
  | eq_refl => eq_refl
  end.

Definition transport {A} (P : A -> Type) {x y} (H : x = y) (f : P x) : P y
  := eq_rect x P f y H.

Definition f_equal_extensional A B (f g : A -> B)
  (fg : forall a, f a = g a) x y (H : x = y)
  : g # H =
     transport (fun fy => g x = fy) (fg y)
     (transport (fun fx => fx = f y) (fg x) 
      (f # H)).
Proof.
refine (match H with eq_refl => _ end).
clear H. unfold transport, eq_rect. simpl. 
refine (match fg x with eq_refl => _ end).
reflexivity.
Qed.

Definition f_equal_id A (x y : A) (H : x = y) : (fun z => z) # H = H
  := match H with eq_refl => eq_refl end.

Definition eq_trans_id_l {A} {x y : A} (p : x = y) : eq_refl @ p = p.
Proof.
intros. refine (match p with eq_refl => _ end). simpl. reflexivity.
Qed.

Definition eq_trans_id_r {A} {x y : A} (p : x = y) : p @ eq_refl = p.
Proof.
intros. refine (match p with eq_refl => _ end). simpl. reflexivity.
Qed.

Definition eq_trans_assoc {A} {w x y z : A} (p : w = x) (q : x = y) (r : y = z)
  : p @ (q @ r) = (p @ q) @ r.
Proof.
refine (match r with eq_refl => _ end). simpl.
reflexivity.
Qed.

(** Lemma 2.4.3 of HoTT book *)
Definition f_equal_natural {A B} {f g : A -> B} (H : forall a, f a = g a)
 {x y} (p : x = y) : H x  @  g # p = f # p   @   H y.
Proof.
refine (match p with eq_refl => _ end).
simpl. symmetry. apply f_equal_id. 
Qed.

Definition eq_sym_r {A} {x y : A} (p : x = y) :
  p @ eq_sym p = eq_refl :=
  match p with eq_refl => eq_refl end.

Definition eq_sym_l {A} {x y : A} (p : x = y) :
  eq_sym p @ p = eq_refl :=
  match p with eq_refl => eq_refl end.

Definition whisker_right : forall {A} {x y z : A} {p1 p2 : x = y} (q : y = z)
  , p1 @ q = p2 @ q -> p1 = p2.
Proof.
intros. rewrite <- (eq_trans_id_r p1). 
rewrite <- (eq_sym_r q). rewrite eq_trans_assoc. 
rewrite H. rewrite <- eq_trans_assoc. rewrite eq_sym_r. 
rewrite eq_trans_id_r. reflexivity.
Qed.

Definition whisker_left : forall {A} {x y z : A} {q1 q2 : y = z} (p : x = y)
  , p @ q1 = p @ q2 -> q1 = q2.
Proof.
intros. rewrite <- (eq_trans_id_l q1). 
rewrite <- (eq_sym_l p). rewrite <- eq_trans_assoc. 
rewrite H. rewrite eq_trans_assoc. rewrite eq_sym_l. 
rewrite eq_trans_id_l. reflexivity.
Qed.  

(** Corollary 2.4.4 of HoTT book *)
Definition f_equal_homotopy_commutes {A} {f : A -> A}
  (H : forall a, f a = a) (x : A) : H (f x) = f # (H x).
Proof.
pose proof (f_equal_natural (g := fun x => x) H (H x)).
rewrite f_equal_id in H0.
apply (whisker_right (H x)). assumption.
Qed.

Definition f_equal_eq {A B} {x y : A} (f : A -> B) {p q : x = y}
  (eqprf : p = q) : f # p = f # q :=
  match eqprf with eq_refl => eq_refl end.

Definition f_equal_trans_distr {A B} {x y z : A} (f : A -> B) 
  (p : x = y) (q : y = z)
  : f # (p @ q) = (f # p) @ (f # q).
Proof.
refine (match q with eq_refl => _ end). simpl.
reflexivity.
Qed. 

Definition lemma422 {A B : Type} (iso : T A B)
  : forall b : B,
   from iso # to_from iso b = from_to iso (from iso b).
Proof.
intros. 
pose proof (tau iso).
pose proof (f_equal_natural (to_from iso) (to_from iso b)).
apply (f_equal_eq (from iso)) in H0.
rewrite !f_equal_trans_distr in H0.
rewrite <- (tau iso (from iso b)) in H0.
rewrite f_equal_compose in H0.
rewrite <- (f_equal_homotopy_commutes (from_to iso)) in H0.
pose proof (f_equal_natural (from_to iso) (from iso # to_from iso b)).
rewrite !f_equal_id in H0, H1.
rewrite H0 in H1. 
rewrite !f_equal_compose in H1. 
rewrite (f_equal_compose _ _ _ (from iso) (fun b => to iso (from iso b))) in H1.
apply whisker_left in H1.
assumption.
Qed.

(** Lemma 4.2.2 of HoTT *)
Definition Sym {A B : Type} (iso : T A B) : T B A.
Proof. refine(
  {| to := from iso
   ; from := to iso
   ; from_to := to_from iso
   ; to_from := from_to iso
  |}).
apply lemma422.
Qed.

End Equiv.