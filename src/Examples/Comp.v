Require Import
  FormTopC.Bundled
  FormTopC.Discrete
  FormTopC.Cont
  FormTopC.InfoBase
  Spec.Category
  StdLib
  Algebra.SetsC
  FormTopC.All.
Import Category.

Local Open Scope morph.
Local Open Scope obj.

Set Universe Polymorphism.

Module ExampleComp.

Existing Instances All.IGT_Cat All.IGT_CMC.

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


Definition discrete_pt {A} (x : A) : unit ~~> discrete A :=
  point (discrete A) (Logic.eq x) (DiscreteFunc.pt_okI x).

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

Instance CMC_Props_IGT : @CMC_Props IGT IGT_Cat IGT_CMC := undefined _.


Existing Instances 
  CCat_PSh CCCOps_PSh CMC_Psh CMCProps_PSh CCCProps_PSh.


Hint Constructors FirstOrder Basic : FO_DB.

Set Printing Universes.

Check (Y (cmcprops := CMC_Props_IGT) (discrete nat)).

Lemma func_1_fo : FirstOrder (discrete nat * unit) (discrete nat) 
  (Y (cmcprops := CMC_Props_IGT) (discrete nat) ==> Y (cmcprops := CMC_Props_IGT) (discrete nat))%obj.
Proof.
econstructor 2. econstructor.
econstructor. econstructor.
Defined.

Definition func_1_CCC : unit ~~> (Y (discrete nat) ==> Y (discrete nat))%obj.
Proof.
apply (to_presheaf func_1_fo).
refine (_ ∘ fst). apply func_1.
Defined.

Require Import Language.CCCPL.

(* Why do I need to set these implicits to avoid a typeclass loop? 
   So frustrating! *)
Definition func1_twice : unit ~~> (Y (discrete nat) ==> Y (discrete nat))%obj := 
compile_phoas (U := PSh IGT) (
  Build_WfTerm (U := PSh IGT) (fun _ => Abs (U := PSh IGT) (fun x => (# func_1_CCC) @ ((# func_1_CCC) @ (! x))))%stlc (ltac:(proveWF))).

Definition discrete_pt_CCC {A} (x : A)
  : CCC.Const (Y (discrete A)).
Proof.
apply pt_to_presheaf. apply discrete_pt. assumption.
Defined.

Lemma discrete_fo {A B : Type} : FirstOrder (discrete A * unit) (discrete B)
  (Y (discrete A) ==> Y (discrete B))%obj.
Proof.
repeat econstructor.
Defined.

Require Import FormTopC.Bundled
  FormTopC.FormTop.

Definition runDiscrete {A} (x : unit ~~> discrete A) : A.
pose proof (Cont.here (mp_ok x) I) as H.
simpl in H. 
remember (@union A True(fun _ : A => True) (@mp One (discrete A) x)) as U. 
induction H; subst. destruct a. destruct u.
- exact a.
- apply IHGCov. reflexivity.
- induction i. 
Defined.

Definition runDiscrete_CCC {A B : Type}
 (f : CCC.Const (Y (discrete A) ==> Y (discrete B))%obj) : (A -> B).
Proof.
pose proof (from_presheaf (@discrete_fo A B) f).
intros.
apply (runDiscrete (X ∘ ⟨ discrete_pt X0 , tt ⟩)).
Defined.

End ExampleComp.

Definition test_computation : nat -> nat 
  := ExampleComp.runDiscrete_CCC ExampleComp.func1_twice.

(*
Extraction Language Haskell.
Extraction "test.hs" test_computation.
*)
