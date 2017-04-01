Set Universe Polymorphism.
Set Asymmetric Patterns.

Require Import 
  CMorphisms
  Coq.Classes.RelationClasses
  Coq.Classes.CRelationClasses
  Prob.StdLib.
Record Setoid := 
  { sty :> Type
  ; seq : forall (A B : sty), Type
  ; seq_Equivalence : Equivalence seq
  }.

Infix "==" := (seq _) (at level 70, no associativity) : Setoid_scope.
Notation "a ==[ X ] b" := (seq X a b) (at level 70, format "a  ==[ X ]  b") : Setoid_scope.
Delimit Scope Setoid_scope with setoid.
Local Open Scope setoid.
Delimit Scope SetoidC_scope with setoidc.
Local Open Scope setoidc.

Instance setoid_Equivalence (s : Setoid) : Equivalence (seq s).
Proof.
apply seq_Equivalence.
Qed.

Definition unit_Setoid@{i P} : Setoid@{i P}.
Proof.
refine (
  {| sty := Datatypes.unit
  ; seq := fun _ _ => True
  |}).
constructor; unfold Reflexive, Symmetric, Transitive; auto.
Defined.

Definition prod_Setoid@{i P} (A B : Setoid@{i P}) : Setoid@{i P}.
Proof.
refine (
  {| sty := (sty A * sty B)%type
   ; seq := fun f f' => (seq A (fst f) (fst f') 
          * seq B (snd f) (snd f'))%type
  |}).
constructor; unfold Reflexive, Symmetric, Transitive; 
  intros.
- split; reflexivity.
- destruct X; split; symmetry; assumption. 
- destruct X, X0; split; etransitivity; eassumption.
Defined.

Record function_car@{i P} (A B : Setoid@{i P}) :=
  { sf :> A -> B
  ; sf_proper : forall a a', a == a' -> sf a == sf a'
  }.

Instance function_Proper {A B} (f : function_car A B) : 
  Proper (seq _ ==> seq _) f.
Proof.
unfold Proper, respectful. intros. 
apply sf_proper. assumption.
Qed.

Require Coq.Setoids.Setoid.
Definition function@{A P} (A B : Setoid@{A P}) : Setoid@{A P}.
Proof.
unshelve eapply
  {| sty := function_car A B
   ; seq := fun f g => forall a a', a == a' -> f a == g a'
  |}.
constructor; unfold Reflexive, Symmetric, Transitive;
  simpl; intros.
- apply sf_proper. assumption.
- symmetry. apply X. symmetry. assumption.
- etransitivity. eapply X. eassumption.
  apply X0. reflexivity.
Defined.

Infix "~~>" := (function) (at level 75) : SetoidC_scope.

Definition id {A : Setoid} : A ~~> A.
Proof.
unshelve econstructor.
- auto.
- simpl. auto.
Defined.

Definition compose {A B C : Setoid} (g : B ~~> C)
  (f : A ~~> B) : A ~~> C.
Proof.
unshelve econstructor.
- intros. apply g. apply f. assumption.
- simpl. intros. repeat apply sf_proper. assumption.
Defined.

Infix "∘" := (compose) (at level 40, left associativity) : SetoidC_scope.

Record Iso@{i P} {A B : Setoid@{i P}} : Type :=
  { to : A ~~> B
  ; from : B ~~> A
  ; to_from : forall a, to (from a) == a
  ; from_to : forall b, from (to b) == b
  }.

Arguments Iso : clear implicits.

Infix "≅" := Iso (at level 70, no associativity) : SetoidC_scope.

Lemma Iso_Refl A : A ≅ A.
Proof.
refine (
  {| to := id
  ; from := id
  |}
); intros; (reflexivity || assumption).
Defined.

Lemma Iso_Sym {A B : Setoid} (i : A ≅ B) : B ≅ A.
Proof.
refine (
  {| to := from i
   ; from := to i
  |}
); intros. 
- apply from_to.
- apply to_from.
Defined.

Require Coq.Setoids.Setoid.

Lemma Iso_Trans@{i P} {A B C : Setoid@{i P}} (ab : A ≅ B) (bc : B ≅ C)
  : A ≅ C.
Proof.
refine (
  {| to := to bc ∘ to ab
   ; from := from ab ∘ from bc
  |}); intros.
- etransitivity. simpl. apply sf_proper.
  apply (to_from ab). apply (to_from bc).
- etransitivity. simpl. apply sf_proper. 
  apply (from_to bc). apply (from_to ab).
Defined.

Local Instance Iso_Equivalence : Equivalence Iso.
Proof.
constructor; unfold Reflexive, Transitive, Symmetric; intros.
apply Iso_Refl. apply Iso_Sym. assumption. 
eapply Iso_Trans; eassumption.
Defined.

Module Leib.

(*
Inductive eq {A} {x : A} : A -> Type :=
  | eq_refl : eq x.

Arguments eq {A} x y.
*)

Definition Leibniz (A : Type) : Setoid.
Proof.
unshelve eapply (
  {| sty := A
   ; seq := eq |}).
Defined.

Definition Leibniz_func {A B} (f : A -> B)
  : Leibniz A ~~> Leibniz B.
Proof.
unshelve econstructor.
- simpl. assumption.
- simpl. intros. f_equal. assumption.
Defined.

End Leib.