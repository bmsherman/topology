Require Import 
  FormTopC.FormTop
  FormTopC.Bundled
  FormTopC.Cont
  FormTopC.Product
  FormTopC.InfoBase
  Spec.Category.

Import Category.

Existing Instances Bundled.PO Bundled.local Bundled.IGTFT.

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
- apply truncate_Equiv. constructor; 
  unfold Reflexive, Symmetric, Transitive; intros.
  + reflexivity. 
  + symmetry. assumption.
  + etransitivity; eassumption.
- unfold eq. simpl. unfold eq_map. intros.
  destruct H, H0. constructor.
  simpl. apply (Cont.compose_proper (T := B));
    (apply mp_ok || assumption).
- intros. simpl. unfold eq_map.
  induction H, H0. constructor.
  unfold Product.pair. apply EQ_map_compose.
  reflexivity. apply ProductMaps.parallelIG_Proper_EQ;
  apply EQ_map_Sat; assumption.
Defined.