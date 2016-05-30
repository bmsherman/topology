Require Import FormTop.FormTop 
  FormTop.Cont
  Frame FormTop.Product FormTop.InfoBase 
  Algebra.Sets.

Delimit Scope loc_scope with loc.
Local Open Scope loc.

Module Bundled.

(* Inductively-generated formal topology *)
Record IGT : Type :=
  { S : Type
  ; le : S -> Ensemble S
  ; PO :> PreO.t le
  ; Ix : S -> Type
  ; C : forall s, Ix s -> (Ensemble S)
  ; localized : FormTop.localized le C
  }.

Instance IGT_PreO : forall (X : IGT), PreO.t (le X) := PO.


Generalizable All Variables.

Definition Cov (X : IGT) := FormTop.GCov (le X) (C X).

Instance IGTFT `(X : IGT) : FormTop.t (le X) (Cov X) :=
  FormTop.GCov_formtop _ _ (localized X).

Definition InfoBase {A : Type} {ops : MeetLat.Ops A}
  (ML : MeetLat.t A ops) : IGT :=
  {| S := A 
  ; PO := PO.PreO
  ; localized := @InfoBase.loc _ _ _ MeetLat.PO
  |}.

Definition One : IGT := InfoBase MeetLat.one.

Definition times `(LA : IGT) `(LB : IGT) : IGT :=
  let PO1 := PO LA in let PO2 := PO LB in
  {| PO := Product.PO (S LA) (S LB)
  ; localized := Product.loc _ _ _ _ _ _ (localized LA) (localized LB)
  |}.

Infix "*" := times : loc_scope.

Record cmap `{LA : IGT} `{LB : IGT} : Type :=
  { mp : Cont.map (S LA) (S LB)
  ; mp_ok : Cont.t (le LA) (le LB) (Cov LA) (Cov LB) mp
  }.

Arguments cmap LA LB : clear implicits.

Infix "~~>" := cmap (at level 75) : loc_scope.

Definition id `{LA : IGT} : LA ~~> LA := 
  let POA := PO LA in 
  {| mp := Cont.id
  ; mp_ok := Cont.t_id |}.

Definition comp `{LA : IGT} 
  `{LB : IGT} `{LD : IGT} (f : LB ~~> LD) (g : LA ~~> LB) : LA ~~> LD :=
  let POA := PO LA in let POB := PO LB in
  let POD := PO LD in
  {| mp := compose (mp f) (mp g) 
  ; mp_ok := Cont.t_compose (mp g) (mp f) (mp_ok g) (mp_ok f)
  |}.

Infix "∘" := comp (at level 60) : loc_scope.

Definition One_intro_mp {A : IGT} : Cont.map (S A) (S One)
  := One.One_intro.

Require Import Ensembles FunctionalExtensionality.

(** This is so horrendously ugly... *)
Definition One_intro_mp_ok {A : IGT} :
  Cont.t (le A) (le One) (Cov A) (Cov One)
  One_intro_mp.
Proof.
simpl. replace (Cov One) with One.Cov.
unfold One_intro_mp.
apply One.One_intro_cont.
extensionality x.
apply Extensionality_Ensembles.
apply Same_set_iff. intros; simpl.
unfold One.Cov, Cov. destruct x. split; intros.
- apply FormTop.grefl.  assumption.
- induction H. assumption. destruct a, b. assumption.
  apply H0. destruct a. simpl. constructor.
Qed.

Definition One_intro `{A : IGT} : A ~~> One :=
  {| mp := One_intro_mp
   ; mp_ok := One_intro_mp_ok
  |}.

Definition proj1_mp {A B : IGT} : Cont.map (S (A * B)) (S A)
   := ProductMaps.proj_L (leS := le A).

Lemma proj1_mp_ok {A B : IGT} :
  Cont.t (le (A * B)) (le A) (Cov (A * B)) (Cov A)
  proj1_mp.
Proof.
simpl.
pose proof (PO A).
apply ProductMaps.t_proj_L; try apply localized.
apply PO.
Qed.

Definition proj1 {A B : IGT} : A * B ~~> A :=
  {| mp := proj1_mp
  ; mp_ok := proj1_mp_ok
  |}.

Definition proj2_mp {A B : IGT} : Cont.map (S (A * B)) (S B)
  := ProductMaps.proj_R (leT := le B).

Lemma proj2_mp_ok {A B : IGT} :
  Cont.t (le (A * B)) (le B) (Cov (A * B)) (Cov B)
  proj2_mp.
Proof.
simpl.
pose proof (PO A).
apply ProductMaps.t_proj_R; try apply localized.
apply PO.
Qed.

Definition proj2 {A B : IGT} : A * B ~~> B :=
  {| mp := proj2_mp
  ; mp_ok := proj2_mp_ok
  |}.

Definition diagonal_mp {A : IGT} : Cont.map (S A) (S (A * A))
  := ProductMaps.diagonal (leS := le A).

Definition diagonal_mp_ok {A : IGT} :
  Cont.t (le A) (le (A * A)) (Cov A) (Cov (A * A)) diagonal_mp.
Proof.
simpl. pose proof (PO A). apply ProductMaps.t_diagonal.
apply localized.
Qed.

Definition diagonal {A : IGT} : A ~~> A * A :=
  {| mp := diagonal_mp
  ; mp_ok := diagonal_mp_ok
  |}.

Definition parallel_mp {A B X Y : IGT} 
  (f : A ~~> X) (g : B ~~> Y) : Cont.map (S (A * B)) (S (X * Y))
  := ProductMaps.parallel (mp f) (mp g).

Definition parallel_mp_ok {A B X Y : IGT}
  (f : A ~~> X) (g : B ~~> Y) :
  Cont.t (le (A * B)) (le (X * Y)) (Cov (A * B)) (Cov (X * Y))
  (parallel_mp f g).
Proof.
simpl. apply ProductMaps.t_parallel.
apply (mp_ok f). apply (mp_ok g).
Qed.

Definition parallel {A B X Y : IGT} (f : A ~~> X) (g : B ~~> Y)
  : A * B ~~> X * Y :=
  {| mp := parallel_mp f g
   ; mp_ok := parallel_mp_ok f g
  |}.

Definition discrete (A : Type) : IGT :=
  {| S := A 
  ; PO := PreO.discrete A
  ; localized := @InfoBase.loc _ _ _ (PO.discrete A)
  |}.

(** Spaces of open sets (using Scott topology *)
Axiom Open : IGT -> IGT.

Axiom undefined : forall A, A.

Axiom Σ : IGT.
Axiom Σand : Σ * Σ ~~> Σ.
Axiom Σor : Σ * Σ ~~> Σ.
Definition Σconst {Γ} : bool -> Γ ~~> Σ := undefined _.

Definition open_abstract : forall {Γ A B : IGT}, Γ * A ~~> Σ -> Γ ~~> Open A
  := undefined _.

Class Hausdorff {A : IGT} : Type :=
  { apart : A * A ~~> Σ }.

Arguments Hausdorff A : clear implicits.

(** Could have used Sierpinski? *)
Class Discrete {A : IGT} : Type :=
  { bequal : A * A ~~> discrete bool }.

Require Import Numbers.Qnn.

(** non-negative real numbers *)
Axiom PR : IGT.
Axiom PRplus PRmult : PR * PR ~~> PR.
Axiom PRQnn : discrete Qnn ~~> PR.

(** Non-negative lower real numbers *)
Axiom LPR : IGT.
Axiom LPRplus : LPR * LPR ~~> LPR.
Axiom LPRmult : LPR * LPR ~~> LPR.
Axiom LPRind : Σ ~~> LPR.
Axiom LPRlower : PR ~~> LPR.

(** Real numbers *)
Axiom R : IGT.
Axiom Rplus Rmult : R * R ~~> R.
Axiom Rnegate : R ~~> R.
Axiom Rpow : R * discrete nat ~~> R.
Axiom square : R ~~> PR.
Definition Rzero {Γ} : Γ ~~> R := undefined _.

Axiom Stream : IGT -> IGT.

Definition Rminus : R * R ~~> R := Rplus ∘ parallel id Rnegate.

(** Measures and probabilities over a given space *)
Axiom Meas : IGT -> IGT.
Axiom Prob : IGT -> IGT.

Definition coinflip {Γ} : Γ ~~> Prob (discrete bool) := undefined _.

Axiom normal : R * PR ~~> Prob R.

Definition stream {Γ A} : Γ ~~> Prob A -> Γ * A ~~> Prob A -> Γ ~~> Prob (Stream A)
  := undefined _.

Definition ProbIsMeas {A} : Prob A ~~> Meas A := undefined _.

Definition MeasEval {A} : Meas A * Open A ~~> LPR := undefined _.

Axiom ProbBoolEval : Prob (discrete bool) ~~> PR.

End Bundled.

Module B := Bundled.

Require Import ContPL.

Instance IGT_Cat : CCat B.IGT :=
  {| CMap := B.cmap
  ;  product := B.times
  |}.

Instance IGT_CMC : CMC B.IGT :=
  {| identity := fun _ => B.id
   ; compose := fun _ _ _ => B.comp
   
   ; top := B.One
   ; top_intro := fun _ => B.One_intro

  ; proj1 := fun _ _ => B.proj1
  ; proj2 := fun _ _ => B.proj2

  ; diagonal := fun _ => B.diagonal
  ; parallel := fun _ _ _ _ => B.parallel
  |}.

Axiom MCProb : @MonadCat _ _ _ B.Prob. 

Local Open Scope cTy.

Require Import Coq.Lists.List.
Import ListNotations.

Infix "~>" := Map (at level 80) : loc_scope.

Notation "! x" := (Lift x) (at level 20) : loc_scope.

Notation "x <- e ; f" := (Bind e (makeFun1E (fun x => f))) 
  (at level 120, right associativity) : loc_scope.

Notation "'LAM' x => f" := (makeFun1E (fun x => f)) 
  (at level 120, right associativity) : loc_scope.

Definition Call1 {A B Γ : B.IGT} (f : A ~~> B) (x : Γ ~~> A)
  : Γ ~~> B := f ∘ x.

Definition Call2 {A B C Γ : B.IGT} 
  (f : A * B ~~> C) (x : Γ ~~> A) (y : Γ ~~> B) : Γ ~~> C := 
  f ∘ parallel x y ∘ diagonal.

Definition Rone {Γ} : Γ ~~> B.R := undefined _.

Infix "+" := (Call2 B.Rplus) : loc_scope.
(** Careful with the "*" sign. It's overloaded for products on
    the types too. *)
Infix "*" := (Call2 B.Rmult).
Infix "-" := (Call2 B.Rminus) : loc_scope.

Notation "0" := B.Rzero : loc_scope.
Notation "1" := Rone : loc_scope.

(** Discrete Ornstein-Uhlenbeck process *)
Definition ornstein : [B.R; B.R] ~> B.Prob (B.Stream B.R) :=
  makeFun [B.R; B.R] (fun _ θ σ =>
     B.stream (Ret 0) (LAM x =>
        (z <- Call2 B.normal 0 (Call1 B.square (!σ)) 
        ; Ret ( (1 - !θ) * !x + !z)))).