Require Import FormTopC.FormTop 
  FormTopC.Cont
  Algebra.FrameC FormTopC.Product FormTopC.InfoBase 
  FormTopC.Discrete
  Algebra.SetsC
  Prob.StdLib.

Set Universe Polymorphism.
Set Asymmetric Patterns.

Delimit Scope loc_scope with loc.
Local Open Scope loc.

Module Bundled.

(* Inductively generated formal topology *)
Record IGT : Type :=
  { S : Type
  ; le : S -> Subset S
  ; PO :> PreO.t le
  ; Ix : S -> Type
  ; C : forall s, Ix s -> Subset S
  ; localized : FormTop.localized le C
  }.

Local Instance IGT_PreO `(X : IGT) : PreO.t (le X) := PO X.

Generalizable All Variables.

Definition Cov (X : IGT) := FormTop.GCov (le X) (C X).

Definition Contmap (A B : IGT) := Cont.map (S A) (S B).
Definition Contprf (A B : IGT) := Cont.t (le A) (le B) (Cov A) (Cov B).

Local Instance local `(X : IGT) : FormTop.localized (le X) (C X)
  := localized X.

Local Instance IGTFT `(X : IGT) : FormTop.t (le X) (Cov X) :=
  FormTop.GCov_formtop _ _.

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

Definition point_mp (A : IGT) (f : Subset (S A))
  (fpt : Cont.pt (le A) (Cov A) f)
  : Contprf One A (fun t _ => f t).
Proof.
simpl.
constructor; intros; auto.
- apply FormTop.grefl. pose proof (Cont.pt_here fpt).
  destruct X.
  econstructor. constructor. eassumption.
- apply FormTop.grefl. pose proof (Cont.pt_local fpt X X0). 
  destruct X1.  destruct i. econstructor. eassumption.
  assumption.
- pose proof (Cont.pt_cov fpt X X0). 
  destruct X1. destruct i. 
  apply FormTop.grefl. econstructor; eauto.
Qed.

Definition One_intro_mp {A : IGT} : Contmap A One
  := One.One_intro.

Require Import FunctionalExtensionality.

Definition One_intro_mp_ok {A : IGT} : Contprf A One One_intro_mp.
Proof.
unfold Contprf.
constructor; unfold Cov, One_intro_mp, One.One_intro; simpl; intros.
- apply FormTop.grefl. econstructor. constructor. constructor.
- constructor.
- apply FormTop.grefl. econstructor. constructor; constructor. constructor.
- apply FormTop.grefl. induction X.
  + econstructor. eassumption. constructor.
  + assumption.
  + induction i. eapply X. reflexivity.
Unshelve. constructor. constructor. constructor.
Qed.

Definition One_intro `{A : IGT} : A ~~> One :=
  {| mp := One_intro_mp
   ; mp_ok := One_intro_mp_ok
  |}.

Definition const {Γ A : IGT} (pt : One ~~> A) : Γ ~~> A
  := pt ∘ One_intro.

Definition proj1_mp {A B : IGT} : Contmap (A * B) A
   := ProductMaps.proj_L (leS := le A).

Lemma proj1_mp_ok {A B : IGT} : Contprf (A * B) A proj1_mp.
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

Definition proj2_mp {A B : IGT} : Contmap (A * B) B
  := ProductMaps.proj_R (leT := le B).

Lemma proj2_mp_ok {A B : IGT} : Contprf (A * B) B proj2_mp.
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

Definition diagonal_mp {A : IGT} : Contmap A (A * A)
  := ProductMaps.diagonal (leS := le A).

Definition diagonal_mp_ok {A : IGT} : Contprf A (A * A) diagonal_mp.
Proof.
simpl. pose proof (PO A). apply ProductMaps.t_diagonal.
apply localized.
Qed.

Definition diagonal {A : IGT} : A ~~> A * A :=
  {| mp := diagonal_mp
  ; mp_ok := diagonal_mp_ok
  |}.

Definition parallel_mp {A B X Y : IGT} 
  (f : A ~~> X) (g : B ~~> Y) : Contmap (A * B) (X * Y)
  := ProductMaps.parallel (leS := le A) (CS := C A) 
      (leT := le B) (CT := C B) (mp f) (mp g).

Definition parallel_mp_ok {A B X Y : IGT}
  (f : A ~~> X) (g : B ~~> Y) :
  Contprf (A * B) (X * Y) (parallel_mp f g).
Proof.
simpl. apply ProductMaps.t_parallel; try typeclasses eauto.
apply (mp_ok f). apply (mp_ok g).
Qed.

Definition parallel {A B X Y : IGT} (f : A ~~> X) (g : B ~~> Y)
  : A * B ~~> X * Y :=
  {| mp := parallel_mp f g
   ; mp_ok := parallel_mp_ok f g
  |}.

Definition pair {Γ A B : IGT} (f : Γ ~~> A) (g : Γ ~~> B)
  : Γ ~~> A * B
  := parallel f g ∘ diagonal.

Definition discrete (A : Type) : IGT :=
  {| S := A 
  ; PO := PreO.discrete A
  ; localized := @InfoBase.loc _ _ _ (PO.discrete A)
  |}.

Axiom undefined : forall A, A.

Definition discrete_f_mp {A B} (f : A -> B)
  : Contmap (discrete A) (discrete B) :=
  Discrete.discrF f.

Definition discrete_f_mp_ok {A B} (f : A -> B)
  : Contprf (discrete A) (discrete B) (discrete_f_mp f) := Discrete.fContI f.

Definition discrete_f {A B} (f : A -> B) : discrete A ~~> discrete B :=
  {| mp := discrete_f_mp f 
   ; mp_ok := discrete_f_mp_ok f |}.

Definition discrete_prod_assoc_mp {A B}
  : Contmap (discrete A * discrete B) (discrete (A * B)) := Logic.eq.

Lemma discrete_prod_assoc_mp_ok {A B}
  : Contprf (discrete A * discrete B) (discrete (A * B)) 
  discrete_prod_assoc_mp. 
Proof. apply Discrete.prod_assoc_cont.
Qed.

Definition discrete_prod_assoc {A B : Type} : 
  discrete A * discrete B ~~> discrete (A * B) :=
  {| mp := discrete_prod_assoc_mp
   ; mp_ok := discrete_prod_assoc_mp_ok
  |}.

(** Spaces of open sets (using Scott topology *)
Definition Open (A : IGT) : IGT :=
  let LE := @Scott.le_Open (S A) (le A) (Ix A) (C A) in 
  let PreO : PreO.t (le A) := IGT_PreO A in
  let PO := 
   @PO.PreO (Subset (S A)) LE _ (Scott.PO_le_eq (POT := PreO)
  (locT := localized A)) in
  {| S := Subset (S A)
   ; le := LE
   ; PO := PO
   ; Ix := InfoBase.Ix
   ; C := InfoBase.C (leS := LE) (eqS := PO.eq_PreO LE)
   ; localized := InfoBase.loc (PO := PO.fromPreO LE)
  |}.

Definition Σ : IGT := InfoBase Sierpinski.SML.

Definition Σand_mp : Cont.map (S (Σ * Σ)) (S Σ) := Sierpinski.sand.

(** I need to prove that a the information-base product of meet lattices
    is the same as the product of the information bases

    This will be phrased as a homeomorphism!
*)
(** Sierpinski.sand_cont *)
Definition Σand_mp_ok : Cont.t (le (Σ * Σ)) (le Σ)
  (Cov (Σ * Σ)) (Cov Σ) Σand_mp.
Proof.
simpl. unfold Cov. simpl. 
Admitted.

Definition Σand : Σ * Σ ~~> Σ :=
  {| mp := Σand_mp
   ; mp_ok := Σand_mp_ok
  |}.

Definition Σor_mp : Cont.map (S (Σ * Σ)) (S Σ) := Sierpinski.sor.

(** Sierpinski.sor_cont *)
Definition Σor_mp_ok : Cont.t (le (Σ * Σ)) (le Σ)
  (Cov (Σ * Σ)) (Cov Σ) Σor_mp.
Proof.
simpl. unfold Cov. simpl. 
Admitted.

Definition Σor : Σ * Σ ~~> Σ :=
  {| mp := Σor_mp
   ; mp_ok := Σor_mp_ok
  |}.

Definition open_abstract_mp {Γ A : IGT}
  (f : Cont.map (S (Γ * A)) (S Σ))
     : Cont.map (S Γ) (S (Open A))
  := Scott.absF (leT := le A) (IxT := Ix A) (CT := C A) f.

Definition open_abstract_mp_ok {Γ A : IGT}
  (f : Cont.map (S (Γ * A)) (S Σ))
  : Cont.t (le (Γ * A)) (le Σ) (Cov (Γ * A)) (Cov Σ) f
  -> Cont.t (le Γ) (le (Open A)) (Cov Γ) (Cov (Open A)) 
    (open_abstract_mp f).
Proof.
intros H.
apply Scott.absF_cont. apply H.
Qed.

Definition open_abstract {Γ A : IGT} (f : Γ * A ~~> Σ) : Γ ~~> Open A
  := 
  {| mp := open_abstract_mp (mp f)
   ; mp_ok := open_abstract_mp_ok (mp f) (mp_ok f)
  |}.

Class Hausdorff {A : IGT} : Type :=
  { apart : A * A ~~> Σ }.

Arguments Hausdorff A : clear implicits.

(** Could have used Sierpinski? *)
Class Discrete {A : IGT} : Type :=
  { bequal : A * A ~~> discrete bool }.

Require Import Spec.Category.
Import Category.

Instance IGT_Cat : CCat IGT :=
  {| arrow := cmap
  ;  prod := times
  ; eq := fun _ _ => eq_map
  |}.

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

Instance IGT_CMC : CMC IGT :=
  {| id := fun _ => Bundled.id
   ; compose := fun _ _ _ => comp
   
   ; unit := One
   ; tt := fun _ => One_intro

  ; fst := fun _ _ => proj1
  ; snd := fun _ _ => proj2

  ; pair := fun _ _ _ => Bundled.pair
  |}.
Proof.
intros. unfold eq. simpl. unfold eq_map.
- apply truncate_Equiv. constructor; 
  unfold Reflexive, Symmetric, Transitive; intros.
  + reflexivity. 
  + symmetry. assumption.
  + etransitivity; eassumption.
- unfold eq. simpl. unfold eq_map. intros.
  destruct H, H0. constructor.
  simpl. apply Cont.compose_proper;
    (apply mp_ok || assumption).
- apply undefined.
Defined.

Definition point (A : IGT) (f : Subset (S A)) (fpt : Cont.pt (le A) (Cov A) f)
  : unit ~~> A :=
  {| mp := fun t _ => f t
   ; mp_ok := point_mp A f fpt
  |}.

Require Import FormTopC.NatInfty.

Definition NatInfty : IGT.
Proof. refine (
  {| S := NatInfty.O
  ; le := NatInfty.le
  ; PO := NatInfty.le_PreO
  ; C := NatInfty.C
  |}).
apply FormTop.Llocalized. apply NatInfty.le_PreO.
Defined.

Definition NatInfty_exactly (n : nat) : unit ~~> NatInfty
  := point NatInfty (NatInfty.exactly n)
  (IGCont.pt_cont _ _ (NatInfty.pt_exactly n)).

Definition NatInfty_infty : unit ~~> NatInfty :=
  point NatInfty (NatInfty.infty) (IGCont.pt_cont _ _
    (NatInfty.pt_infty)).

Definition NatInfty_checker (f : nat -> bool) : unit ~~> NatInfty
  := point NatInfty (NatInfty.checkf f)
    (IGCont.pt_cont _ _ (NatInfty.checkf_cont f)).

Definition run_NatInfty (x : unit ~~> NatInfty) :
  NatInfty.Partial Datatypes.unit.
Proof.
Abort.


Local Close Scope loc.
Local Open Scope obj.
Local Open Scope morph.

Definition discrete_pt {A} (x : A) : unit ~~> discrete A :=
  point (discrete A) (Logic.eq x) (Discrete.pt_okI x).

Definition runDiscrete {A} (x : One ~~> discrete A) : A.
pose proof (Cont.here (mp_ok x) I) as H.
remember (union (fun _ : S (discrete A) => True) (mp x)) as U. 
induction H; subst. destruct u. destruct i.
- exact a0.
- apply IHGCov. reflexivity.
- induction i. simpl in *. apply (X I).
  unfold InfoBase.C. constructor. reflexivity.
Defined.

Definition discrBinOp {A B C : Type} 
  (f : A -> B -> C) : discrete A * discrete B ~~> discrete C :=
 discrete_f (fun p : A * B => let (x, y) := p in f x y) ∘ discrete_prod_assoc.

Definition natMult : discrete nat * discrete nat ~~> discrete nat :=
  discrBinOp Nat.mul.

Definition natAdd : discrete nat * discrete nat ~~> discrete nat :=
  discrBinOp Nat.add.

Definition testFunc : discrete nat * discrete nat ~~> discrete nat
  := ap2 natMult (ap2 natAdd fst snd) snd.

Definition add3 : discrete nat ~~> discrete nat :=
  discrete_f (fun n => n + 3).

Definition five : One ~~> discrete nat :=
  discrete_pt 5.

Definition eight : One ~~> discrete nat :=
  add3 ∘ five.

Definition func_1 : discrete nat ~~> discrete nat :=
  ap2 testFunc (ap0 eight) id.

Require Import Spec.CCC.CCC.
Require Import Spec.CCC.Presheaf.
Import Presheaf.
Import CCC.

Instance CMC_Props_IGT : CMC_Props IGT := undefined _.

Existing Instances 
  CCat_PSh CCCOps_PSh CMC_Psh CMCProps_PSh CCCProps_PSh.

Hint Constructors FirstOrder Basic : FO_DB.

Lemma func_1_fo : FirstOrder (discrete nat * unit) (discrete nat) 
  (Y (discrete nat) ==> Y (discrete nat))%obj.
Proof.
econstructor 2. econstructor.
econstructor. econstructor.
Defined.

Definition func_1_CCC : Const (Y (discrete nat) ==> Y (discrete nat))%obj.
Proof.
apply (to_presheaf func_1_fo).
refine (_ ∘ fst). apply func_1.
Defined.

Require Import Language.CCCPL.

Definition func1_twice_term : Term (Y (discrete nat) ==> Y (discrete nat))%obj := 
    ([ λ x => #func_1_CCC @ (#func_1_CCC @ !x) ])%stlc.

  Lemma func1_twiceWF : Wf func1_twice_term.
  Proof. proveWF.
  Defined.

Definition func1_twice : 
  Presheaf.Const (Y (discrete nat) ==> Y (discrete nat))%obj.
Proof.
eapply compile_phoas. apply func1_twiceWF.
Defined.

Definition discrete_pt_CCC {A} (x : A)
  : Presheaf.Const (Y (discrete A)).
Proof.
apply pt_to_presheaf. apply discrete_pt. assumption.
Defined.

Lemma discrete_fo {A B : Type} : FirstOrder (discrete A * unit) (discrete B)
  (Y (discrete A) ==> Y (discrete B))%obj.
Proof.
repeat econstructor.
Defined.

Definition runDiscrete_CCC {A B : Type}
 (f : Presheaf.Const (Y (discrete A) ==> Y (discrete B))%obj) : (A -> B).
Proof.
pose proof (from_presheaf (@discrete_fo A B) f).
intros.
apply (runDiscrete (X ∘ ⟨ discrete_pt X0 , tt ⟩)).
Defined.

Definition test_computation : nat -> nat 
  := runDiscrete_CCC func1_twice.

End Bundled.

(*
Extraction Language Haskell.
Extraction "test.hs" Bundled.test_computation.
*)