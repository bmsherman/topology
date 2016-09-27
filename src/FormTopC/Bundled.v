Require Import FormTopC.FormTop 
  FormTopC.Cont
  Algebra.FrameC
  Algebra.SetsC
  Prob.StdLib.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Delimit Scope loc_scope with loc.
Local Open Scope loc.

(** Bundle the definitions together *)
(* Inductively generated formal topology *)
Record IGT : Type :=
  { S : Type
    (** The type of basic opens, i.e., observable property *)
  ; le : S -> Subset S
    (** a preorder on [S] which indicates when one basic open lies in another,
       i.e., one observable property implies another *)
  ; PO :> PreO.t le
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
    (** The space must be overt, i.e., have a positivity predicate. *)
  }.

Local Instance IGT_PreO `(X : IGT) : PreO.t (le X) := PO X.

Generalizable All Variables.

Definition Cov (X : IGT) := FormTop.GCov (le X) (C X).

Local Instance local `(X : IGT) : FormTop.localized (le X) (C X)
  := localized X.

Local Instance IGTFT `(X : IGT) : FormTop.t (le X) (Cov X) :=
  FormTop.GCov_formtop.

Definition Contmap (A B : IGT) := Cont.map (S A) (S B).
Definition Contprf (A B : IGT) := Cont.t (le A) (le B) (Cov A) (Cov B).

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

Definition eq_map {A B : IGT} (f g : A ~~> B)
  : Prop := inhabited (Cont.func_EQ (CovS := Cov A) (mp f) (mp g)).