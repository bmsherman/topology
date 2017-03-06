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

Record Iso@{i P} {A B : Setoid@{i P}} : Type :=
  { to : A -> B
  ; from : B -> A
  ; to_Proper : forall a a', a == a' -> to a == to a'
  ; from_Proper : forall b b', b == b' -> from b == from b'
  ; to_from : forall a, to (from a) == a
  ; from_to : forall b, from (to b) == b
  }.

Arguments Iso : clear implicits.

Infix "≅" := Iso (at level 70, no associativity) : Setoid_scope.

Local Instance to_Proper_I@{i P iP} {A B : Setoid@{i P}} (i : A ≅ B)
  : Proper@{i iP} (seq _ ==> seq _) (to i) := to_Proper i.

Local Instance from_Proper_I@{i P iP} {A B : Setoid@{i P}} (i : A ≅ B)
  : Proper@{i iP} (seq _ ==> seq _) (from i) := from_Proper i.


Lemma Iso_Refl A : A ≅ A.
Proof.
refine (
  {| to := fun x => x
  ; from := fun x => x
  |}
); unfold Proper, respectful
 ; intros; (reflexivity || assumption).
Defined.

Lemma Iso_Sym {A B : Setoid} (i : A ≅ B) : B ≅ A.
Proof.
refine (
  {| to := from i
   ; from := to i
  |}
); intros. 
- apply from_Proper. assumption.
- apply to_Proper. assumption. 
- apply from_to.
- apply to_from.
Defined.


Require Coq.Setoids.Setoid.

Lemma Iso_Trans@{i P} {A B C : Setoid@{i P}} (ab : A ≅ B) (bc : B ≅ C)
  : A ≅ C.
Proof.
refine (
  {| to := fun x => to bc (to ab x)
   ; from := fun x => from ab (from bc x)
  |}); 
  unfold Proper, respectful; intros.
- repeat apply to_Proper. assumption.
- repeat apply from_Proper. assumption.
- etransitivity. apply to_Proper.
  apply (to_from ab). apply (to_from bc).
- etransitivity. apply from_Proper. 
  apply (from_to bc). apply (from_to ab).
Defined.

Local Instance Iso_Equivalence : Equivalence Iso.
Proof.
constructor; unfold Reflexive, Transitive, Symmetric; intros.
apply Iso_Refl. apply Iso_Sym. assumption. 
eapply Iso_Trans; eassumption.
Defined.

Set Printing Universes.

Module Leib.

Inductive eq {A} {x : A} : A -> Type :=
  | eq_refl : eq x.

Arguments eq {A} x y.

Definition Leibniz (A : Type) : Setoid.
Proof.
unshelve eapply (
  {| sty := A
   ; seq := eq |}).
econstructor; unfold Reflexive, Symmetric, Transitive; intros.
constructor. induction X. constructor.
induction X, X0. constructor.
Defined.

End Leib.