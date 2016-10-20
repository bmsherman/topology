Require Import FormTopC.FormTop 
  FormTopC.Cont
  Algebra.OrderC
  Algebra.SetsC
  Prob.StdLib
  CMorphisms.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Delimit Scope loc_scope with loc.
Local Open Scope loc.

(** Bundle the definitions together *)
(* Inductively generated formal topology *)
Record IGT : Type :=
  { S : Type
    (** The type of basic opens, i.e., observable property *)
  ; le : crelation S
    (** a preorder on [S] which indicates when one basic open lies in another,
       i.e., one observable property implies another *)
  ; PO : PreO.t le
    (** the proof that [le] is a preorder *)
  ; Ix : S -> Type
    (** For each observable property, a type of indexes or addresses or names of
        covering axioms for subsets of basic opens which conspire to cover
        the given observable property. This type should be inductively
        generated, or similarly phrased, the axioms should be countable *)
  ; C : forall s, Ix s -> Subset S
    (** For each axiom index/name/address, this gives us a subset of basic
        opens whose union covers the given basic open *)
  ; localized : FormTop.localized le C
    (** The axiom set should be localized, as defined in CSSV2003 *)
  ; pos : FormTop.gtPos le C
    (** The space must have a positivity predicate. *)
  }.

Local Instance IGT_PreO `(X : IGT) : PreO.t (le X) := PO X.

Definition Cov (X : IGT) := FormTop.GCov (le X) (C X).

Notation "a <|[ X ] U" := (Cov X a U) (at level 63, format "a  <|[ X ]  U").
Notation "a <=[ X ] b" := (le X a b) (at level 40, format "a  <=[ X ]  b").

Local Instance local `(X : IGT) : FormTop.localized (le X) (C X)
  := localized X.

Local Instance IGTFT `(X : IGT) : FormTop.t (le X) (Cov X) :=
  FormTop.GCov_formtop.

Local Instance IGT_Pos `(X : IGT) : FormTop.gtPos (le X) (C X)
  := pos X.

Definition Contmap (A B : IGT) := Cont.map (S A) (S B).
Definition Contprf (A B : IGT) := Cont.t (le A) (le B) (Cov A) (Cov B).
Definition IGContprf (A B : IGT) := IGCont.t (le A) (Cov A) (le B) (C B).

Definition Contpt (A : IGT) := Cont.pt (le A) (Cov A).

Record cmap `{LA : IGT} `{LB : IGT} : Type :=
  { mp : Contmap LA LB
  ; mp_ok : Contprf LA LB mp
  }.

Arguments cmap LA LB : clear implicits.

Infix "~~>" := cmap (at level 75) : loc_scope.

Definition id `{LA : IGT} : LA ~~> LA := 
  {| mp := Cont.id
  ; mp_ok := Cont.t_id |}.

Definition comp `{LA : IGT} 
  `{LB : IGT} `{LD : IGT} (f : LB ~~> LD) (g : LA ~~> LB) : LA ~~> LD :=
  {| mp := compose (mp f) (mp g) 
  ; mp_ok := Cont.t_compose (mp g) (mp f) (mp_ok g) (mp_ok f)
  |}.

Infix "∘" := comp (at level 40, left associativity) : loc_scope.

Definition LE_map {A B : IGT} (f g : Contmap A B)
  := Cont.func_LE (CovS := Cov A) f g.

Definition EQ_map {A B : IGT} (f g : Contmap A B)
  := Cont.func_EQ (CovS := Cov A) f g.

Lemma LE_map_antisym {A B : IGT} (f g : Contmap A B)
  : LE_map f g -> LE_map g f -> EQ_map f g.
Proof.
unfold LE_map, EQ_map. intros.
apply Cont.func_LE_antisym; assumption.
Qed.

Lemma EQ_map_LE {A B : IGT} (f g : Contmap A B)
  : EQ_map f g -> LE_map f g.
Proof.
unfold EQ_map, LE_map. intros.
apply Cont.func_EQ_LE. assumption.
Qed.

Require Import CRelationClasses.

Instance LE_map_PreOrder {A B} : PreOrder (@LE_map A B).
Proof.
constructor; unfold Reflexive, Transitive, LE_map;
  intros.
- reflexivity.
- etransitivity; eassumption.
Qed.

Instance EQ_map_Equivalence {A B} : Equivalence (@EQ_map A B).
Proof.
constructor; unfold Reflexive, Transitive, Symmetric, EQ_map;
  intros.
- reflexivity.
- symmetry; assumption.
- etransitivity; eassumption.
Qed.

Lemma LE_map_compose {A B C} {f f' : cmap A B}
  {g g' : cmap B C}
  : LE_map (mp f) (mp f') -> LE_map (mp g) (mp g')
  -> LE_map (mp (g ∘ f)) (mp (g' ∘ f')).
Proof.
unfold LE_map in *.
intros. apply Cont.compose_proper_LE;
  try assumption. apply f'.
Qed.

Lemma EQ_map_compose {A B C} {f f' : cmap A B}
  {g g' : cmap B C}
  : EQ_map (mp f) (mp f') -> EQ_map (mp g) (mp g')
  -> EQ_map (mp (g ∘ f)) (mp (g' ∘ f')).
Proof.
intros. apply Cont.compose_proper.
apply f. apply f'. assumption. assumption.
Qed.

Lemma EQ_map_Sat {A B} {f g : Contmap A B}
  : EQ_map f g 
  -> EQ_map (Cont.Sat (CovS := Cov A) f) (Cont.Sat (CovS := Cov A) g).
Proof.
unfold EQ_map. eapply Cont.func_EQ_Sat.
typeclasses eauto.
Qed.

Definition eq_map {A B : IGT} (f g : A ~~> B)
  : Prop := inhabited (EQ_map (mp f) (mp g)).

Require Import CRelationClasses.
Lemma truncate_Equiv A (f : crelation A) :
  Equivalence f -> RelationClasses.Equivalence (fun x y => inhabited (f x y)).
Proof.
intros H. constructor;
  unfold RelationClasses.Reflexive,
         RelationClasses.Symmetric,
         RelationClasses.Transitive; intros.
- constructor. reflexivity.
- destruct H0. constructor. symmetry. assumption.
- destruct H0, H1. constructor. etransitivity; eassumption.
Qed.

Definition Open {A : IGT} : Type := S A -> Type.