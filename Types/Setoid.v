Set Universe Polymorphism.
Set Asymmetric Patterns.

Require Import Morphisms.
Record Setoid := 
  { sty :> Type
  ; seq : sty -> sty -> Prop
  ; seq_Equivalence : Equivalence seq
  }.

Infix "==" := (seq _) (at level 70, no associativity) : Setoid_scope.
Delimit Scope Setoid_scope with setoid.
Local Open Scope setoid.

Instance setoid_Equivalence (s : Setoid) : Equivalence (seq s).
Proof.
apply seq_Equivalence.
Qed.

Definition unit_Setoid@{i} : Setoid@{i}.
Proof.
refine (
  {| sty := Datatypes.unit
  ; seq := fun _ _ => True
  |}).
constructor; unfold Reflexive, Symmetric, Transitive; auto.
Defined.

Definition prod_Setoid (A B : Setoid) : Setoid.
Proof.
refine (
  {| sty := (sty A * sty B)%type
   ; seq := fun f f' => seq A (Datatypes.fst f) (Datatypes.fst f') 
          /\ seq B (Datatypes.snd f) (Datatypes.snd f')
  |}).
constructor; unfold Reflexive, Symmetric, Transitive; 
  intros.
- split; reflexivity.
- destruct H; split; symmetry; assumption. 
- destruct H, H0; split; etransitivity; eassumption.
Defined.

Record Iso {A B : Setoid} : Type :=
  { to : A -> B
  ; from : B -> A
  ; to_Proper : Proper (seq _ ==> seq _) to
  ; from_Proper : Proper (seq _ ==> seq _) from
  ; to_from : forall a, to (from a) == a
  ; from_to : forall b, from (to b) == b
  }.

Arguments Iso : clear implicits.

Infix "≅" := Iso (at level 70, no associativity) : Setoid_scope.

Local Instance to_Proper_I {A B} (i : A ≅ B)
  : Proper (seq _ ==> seq _) (to i) := to_Proper i.

Local Instance from_Proper_I {A B} (i : A ≅ B)
  : Proper (seq _ ==> seq _) (from i) := from_Proper i.


Lemma Iso_Refl A : A ≅ A.
Proof.
refine (
  {| to := fun x => x
  ; from := fun x => x
  |}
); unfold Proper, respectful
 ; intros; (reflexivity || assumption).
Defined.

Lemma Iso_Sym {A B} (i : A ≅ B) : B ≅ A.
Proof.
refine (
  {| to := from i
   ; from := to i
  |}
); unfold Proper, respectful; intros.
- apply from_to.
- apply to_from.
Defined.

Require Coq.Setoids.Setoid.

Lemma Iso_Trans {A B C} (ab : A ≅ B) (bc : B ≅ C)
  : A ≅ C.
Proof.
refine (
  {| to := fun x => to bc (to ab x)
   ; from := fun x => from ab (from bc x)
  |}); 
  unfold Proper, respectful; intros.
- repeat apply to_Proper. assumption.
- repeat apply from_Proper. assumption.
- rewrite (to_from ab). apply (to_from bc).
- rewrite (from_to bc). apply (from_to ab).
Defined.

Require Import CMorphisms.

Local Instance Iso_Equivalence : Equivalence Iso.
Proof.
constructor; unfold Reflexive, Transitive, Symmetric; intros.
apply Iso_Refl. apply Iso_Sym. assumption. 
eapply Iso_Trans; eassumption.
Defined.

Definition Leibniz (A : Type) : Setoid.
Proof.
unshelve eapply (
  {| sty := A
   ; seq := eq |}).
Defined.