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
  { S :> PreISpace.t
  ; PO : PreO.t (le S)
    (** the proof that [le] is a preorder *)
  ; localized : FormTop.localized S
    (** The axiom set should be localized, as defined in CSSV2003 *)
  ; pos : FormTop.gtPos S
    (** The space must have a positivity predicate. *)
  }.

Set Printing Universes.

Local Instance IGT_PreO `(X : IGT) : PreO.t (le X) := PO X.
Local Instance local `(X : IGT) : FormTop.localized (S X)
  := localized X.
Local Instance IGTFT `(X : IGT) : FormTop.t (S X) :=
  FormTop.GCov_formtop.
Local Instance IGT_Pos `(X : IGT) : FormTop.gtPos (S X)
  := pos X.

Definition Cov (X : IGT) := GCov X.

Record cmap `{LA : IGT} `{LB : IGT} : Type :=
  { mp : Cont.map LA LB
  ; mp_ok : Cont.t LA LB mp
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

Definition LE_map {A B : IGT} (f g : Cont.map A B)
  := Cont.func_LE (S := A) f g.

Definition EQ_map {A B : IGT} (f g : Cont.map A B)
  := Cont.func_EQ (S := A) f g.

Lemma LE_map_antisym {A B : IGT} (f g : Cont.map A B)
  : LE_map f g -> LE_map g f -> EQ_map f g.
Proof.
unfold LE_map, EQ_map. intros.
apply Cont.func_LE_antisym; assumption.
Qed.

Lemma EQ_map_LE {A B : IGT} (f g : Cont.map A B)
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

Lemma EQ_map_Sat {A B : IGT} {f g : Cont.map A B}
  : EQ_map f g 
  -> EQ_map (Cont.Sat (S := A) f) (Cont.Sat (S := A) g).
Proof.
unfold EQ_map. eapply Cont.func_EQ_Sat.
typeclasses eauto.
Qed.

Definition eq_map {A B : IGT} (f g : A ~~> B)
  : Type := EQ_map (mp f) (mp g).

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