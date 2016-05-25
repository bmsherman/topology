Require Import FormTop.FormTop Frame FormTop.Product FormTop.InfoBase 
  Algebra.Sets.

Module Bundled.

Delimit Scope loc_scope with loc.
Open Scope loc.

(* Inductively-generated formal topology *)
Record IGT : Type :=
  { S : Type
  ; le : S -> Ensemble S
  ; PO :> PreO.t le
  ; Ix : S -> Type
  ; C : forall s, Ix s -> (Ensemble S)
  ; localized : FormTop.localized le C
  }.


Generalizable All Variables.

Definition Cov (X : IGT) := FormTop.GCov (le X) (C X).

Instance IGTFT `(X : IGT) : FormTop.t (le X) (Cov X) :=
  FormTop.GCov_formtop (PO X) _ _ (localized X).

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
  { mp : S LA -> S LB -> Prop
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
  {| mp := compose (mp g) (mp f)
  ; mp_ok := Cont.t_compose (mp g) (mp f) (mp_ok g) (mp_ok f)
  |}.

Definition One_intro_mp {A : IGT} : S A -> S One -> Prop
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

Definition proj1_mp {A B : IGT} :
  S (A * B) -> S A -> Prop := ProductMaps.proj_L (leS := le A).

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

Definition proj2_mp {A B : IGT} :
  S (A * B) -> S B -> Prop := ProductMaps.proj_R (leT := le B).

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

Definition diagonal_mp {A : IGT} :
  S A -> S (A * A) -> Prop := ProductMaps.diagonal (leS := le A).

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
  (f : A ~~> X) (g : B ~~> Y) :
  S (A * B) -> S (X * Y) -> Prop := ProductMaps.parallel (mp f) (mp g).

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
