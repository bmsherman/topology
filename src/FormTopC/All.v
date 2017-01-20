Require Import 
  FormTopC.FormTop
  FormTopC.Bundled
  FormTopC.Cont
  FormTopC.Product
  FormTopC.InfoBase
  Spec.Category.

Set Universe Polymorphism.
Set Printing Universes.

Import Category.

Existing Instances Bundled.PO Bundled.local Bundled.IGTFT.

Axiom undefined : forall A, A.

Instance IGT_Cat : CCat IGT := 
  {| arrow := cmap 
  ;  prod := times
  ; eq := fun _ _ => eq_map
  |}.

Require Import CRelationClasses.

Instance IGT_CMC : CMC IGT :=
  {| Category.id := fun _ => Bundled.id
   ; Category.compose := fun _ _ _ => comp
   
   ; Category.unit := One
   ; Category.tt := fun _ => One_intro

  ; Category.fst := fun _ _ => proj1
  ; Category.snd := fun _ _ => proj2

  ; Category.pair := fun _ _ _ => Product.pair
  |}.
Proof.
intros. unfold eq. simpl. unfold eq_map.
- constructor; 
  unfold Reflexive, Symmetric, Transitive; intros.
  + reflexivity. 
  + symmetry. assumption.
  + etransitivity; eassumption.
- unfold eq. simpl. unfold eq_map. intros A B C f f' g g' H H0.
  simpl. apply (Cont.compose_proper (T := B));
    (apply mp_ok || assumption).
- intros. simpl. unfold eq_map.
  unfold Product.pair. apply EQ_map_compose.
  reflexivity. apply ProductMaps.parallelIG_Proper_EQ;
  apply EQ_map_Sat; assumption.
Defined.