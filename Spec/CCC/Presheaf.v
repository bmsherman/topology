(* Category of presheaves over a given category *)

Set Universe Polymorphism.
Set Asymmetric Patterns.

Module Presheaf.

Require Import Morphisms.
Record Setoid := 
  { sty :> Type
  ; seq : sty -> sty -> Prop
  ; seq_Equivalence : Equivalence seq
  }.

Instance setoid_Equivalence (s : Setoid) : Equivalence (seq s).
Proof.
apply seq_Equivalence.
Qed.

Definition unit_Setoid : Setoid.
Proof.
refine (
  {| sty := unit
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

Require Import Prob.Spec.Category.
Import Category.

Local Open Scope obj.
Local Open Scope morph.


Section Presheaf.

Context {U : Type} {ccat : CCat U} {cmc : CMC U}.


Definition cmap_Setoid A B :=
  {| sty := A ~~> B
   ; seq := eq
  |}.


Record PSh := 
  { psh_obj :> U -> Setoid
  ; psh_morph : forall {Γ Δ} (ext : Δ ~~> Γ), psh_obj Γ -> psh_obj Δ
  ; psh_morph_Proper :
     forall Γ Δ, Proper (eq ==> seq _ ==> seq _) (@psh_morph Γ Δ)
  ; psh_morph_id : forall A (x : psh_obj A),
    seq (psh_obj A) (psh_morph id x) x
  ; psh_morph_compose : forall A B C (g : C ~~> B) (f : B ~~> A) (x : psh_obj A),
   seq (psh_obj C) (psh_morph g (psh_morph f x))
       (psh_morph (f ∘ g) x)
  }.

Record CFunc {A B : PSh} {Γ : U} : Type :=
  { Func_eval :> forall Δ, Δ ~~> Γ -> A Δ -> B Δ
  ; Func_Proper : forall Δ, Proper (eq ==> seq (A Δ) ==> seq (B Δ)) (Func_eval Δ)
  ; Func_ok : forall Δ (ext : Δ ~~> Γ) Δ' (ext' : Δ' ~~> Δ) (x x' : A Δ),
     seq (psh_obj A Δ) x x'
   -> seq (psh_obj B Δ')
       (psh_morph B ext' (Func_eval Δ ext x))
       (Func_eval Δ' (ext ∘ ext') (psh_morph A ext' x'))
  }.

Record NatTrns (A B : PSh) :=
  { nattrns :> forall Γ : U, A Γ -> B Γ
  ; nattrns_Proper : forall Γ, Proper (seq _ ==> seq _) (nattrns Γ)
  ; nattrns_ok : forall Γ Δ (ext : Δ ~~> Γ) (x x' : A Γ),
     seq (psh_obj A Γ) x x' ->
     seq (psh_obj B Δ) 
        (psh_morph B ext (nattrns Γ x))
        (nattrns Δ (psh_morph A ext x'))
  }.


Arguments CFunc : clear implicits.

Require Import Morphisms.
Definition func_Setoid (A B : PSh)
 (Γ : U) : Setoid.
Proof. refine (
  {| sty := CFunc A B Γ
   ; seq := fun f f' => forall Δ ext e e', seq (A Δ) e e' -> seq (B Δ) (f Δ ext e) (f' Δ ext e')
  |}).
constructor; unfold Reflexive, Symmetric, Transitive;
  intros.
- apply x. reflexivity. assumption.
- symmetry. eapply H. symmetry. assumption.
- etransitivity. apply H. eassumption.
  apply H0. reflexivity.
Defined.

Context {cmcprops : CMC_Props U }.

Definition CFunc_morph {A B} {Γ Δ} (ext : Δ ~~> Γ) 
  (f : CFunc A B Γ) : (CFunc A B Δ).
Proof.
refine (
  {| Func_eval := fun G ext' x => f _ (ext ∘ ext') x |}).
- intros. unfold Proper, respectful.
  intros. apply Func_Proper. rewrite H. reflexivity.
  assumption.
- intros. rewrite Func_ok.
  apply Func_Proper. symmetry. apply compose_assoc. 
  apply psh_morph_Proper. reflexivity. eassumption. reflexivity.
Defined.

Definition func_PSh (A B : PSh) : PSh.
Proof.
refine ( 
 {| psh_obj := func_Setoid A B
  ; psh_morph := fun _ _ => CFunc_morph
 |}).
- intros. unfold Proper, respectful.
  simpl. intros.
  rewrite Func_Proper.
  apply H0. eassumption. rewrite H. reflexivity.
  reflexivity.
- simpl. intros. apply Func_Proper.
  apply compose_id_left. assumption.
- simpl. intros. apply Func_Proper.
  apply compose_assoc. assumption.
Defined.

Definition prod_PSh (A B : PSh) : PSh.
Proof.
refine (
  {| psh_obj := fun Γ => prod_Setoid (A Γ) (B Γ)
  ;  psh_morph := fun Γ Δ f p => let (x, y) := p in 
      (psh_morph _ f x, psh_morph _ f y)
  |} ).
- intros. 
  unfold Proper, respectful. intros.
  destruct x0, y0, H0.
  simpl in *. split; apply psh_morph_Proper; assumption.
- simpl. intros. destruct x. simpl.
  split; apply psh_morph_id.
- simpl. intros. destruct x. simpl. 
  split; apply psh_morph_compose.
Defined.

Definition id_PSh {A : PSh} : NatTrns A A.
Proof.
refine (
  {| nattrns := fun Γ x => x |}).
- unfold Proper, respectful. intros. auto.
- intros. simpl. apply psh_morph_Proper.
  reflexivity. assumption.
Defined.

Definition compose_PSh {A B C : PSh}
  (g : NatTrns B C) (f : NatTrns A B) : NatTrns A C.
Proof.
refine (
  {| nattrns := fun Γ x => g Γ (f Γ x) |}
).
- unfold Proper, respectful. intros.
  repeat apply nattrns_Proper. assumption.
- intros. rewrite (nattrns_ok _ _ g). 
  apply nattrns_Proper.
  rewrite (nattrns_ok _ _ f).
  apply nattrns_Proper. apply psh_morph_Proper.
  reflexivity. eassumption. symmetry. eassumption.
  apply nattrns_Proper. assumption.
Defined.


Definition unit_PSh : PSh.
Proof.
refine (
  {| psh_obj := fun _ => unit_Setoid
   ; psh_morph := fun _ _ _ x => x
  |}).
- unfold Proper, respectful. intros.
  simpl. auto.
- simpl. intros. auto.
- simpl. intros. auto.
Defined.

Definition tt_PSh {A : PSh} : NatTrns A unit_PSh.
Proof.
apply ( Build_NatTrns A unit_PSh
    (fun _ _ => Datatypes.tt)).
- intros. unfold Proper, respectful.
  intros. reflexivity.
- intros. constructor.
Defined.

Definition pair_PSh {X A B} (f : NatTrns X A)
  (g : NatTrns X B) : NatTrns X (prod_PSh A B).
Proof.
apply (Build_NatTrns _ (prod_PSh A B)
  (fun Γ (x : X Γ) => (f Γ x, g Γ x))).
- intros. unfold Proper, respectful.
  intros. simpl. split; apply nattrns_Proper; assumption.
- intros. simpl. split; apply nattrns_ok; assumption.
Defined.

Definition fst_Psh {A B} : NatTrns (prod_PSh A B) A.
Proof.
apply (Build_NatTrns (prod_PSh A B) A
  (fun Γ p => let (x, _) := p in x)).
- intros. unfold Proper, respectful.
  intros. destruct x, y, H. simpl in *. assumption.
- intros. destruct x, x', H.
  simpl in *. apply psh_morph_Proper. reflexivity.
  assumption.
Defined.

Definition snd_Psh {A B} : NatTrns (prod_PSh A B) B.
Proof.
apply (Build_NatTrns (prod_PSh A B) B
  (fun Γ p => let (_, y) := p in y)).
- intros. unfold Proper, respectful.
  intros. destruct x, y, H. simpl in *. assumption.
- intros. destruct x, x', H.
  simpl in *. apply psh_morph_Proper. reflexivity.
  assumption.
Defined.

Definition eq_map (A B : PSh) (f g : NatTrns A B) :=
  forall Γ (x x' : A Γ),
     seq (psh_obj A Γ) x x' ->
     seq (psh_obj B Γ) (f Γ x) (g Γ x').

Instance eq_Equivalence_PSh A B : Equivalence (eq_map A B).
Proof.
constructor; unfold eq_map, Reflexive, Symmetric, Transitive; intros.
- apply nattrns_Proper. assumption.
- symmetry. apply H. symmetry. assumption.
- etransitivity. apply H. eassumption.
  apply H0. reflexivity.
Qed.

Definition eval_PSh_trns {A B : PSh} :
  forall Γ, (prod_PSh (func_PSh A B) A) Γ -> B Γ.
Proof.
simpl. intros. destruct X.
exact (c Γ id s).
Defined.

Definition eval_PSh {A B : PSh} : NatTrns (prod_PSh (func_PSh A B) A) B.
Proof.
constructor 1 with eval_PSh_trns.
- intros. unfold Proper, respectful. simpl. intros.
  destruct x, y, H. simpl in *. auto.
- simpl. intros. destruct x, x', H. simpl in *.
  etransitivity. Focus 2.
  apply H. apply psh_morph_Proper.
  reflexivity. eassumption.
  etransitivity. apply Func_ok. eassumption.
  apply Func_Proper.
  rewrite compose_id_left, compose_id_right.
  reflexivity. apply psh_morph_Proper. reflexivity.
  symmetry. assumption.
Defined.

Axiom undefined : forall A, A.

Definition abstract_PSh_trns {X A B : PSh}
 (f : NatTrns (prod_PSh X A) B)
 (Γ : U) (x : X Γ) : 
 forall Δ, Δ ~~> Γ -> A Δ -> B Δ.
Proof.
intros. apply f. simpl. split.
eapply psh_morph; eassumption. assumption.
Defined.

Definition abstract_PSh_CFunc {X A B : PSh}
 (f : NatTrns (prod_PSh X A) B)
 (Γ : U) (x : X Γ) : (func_PSh A B) Γ.
Proof.
simpl. refine (
  {| Func_eval := abstract_PSh_trns f Γ x |}).
- intros. unfold Proper, respectful.
  unfold abstract_PSh_trns.
  intros.  apply nattrns_Proper. simpl.
  split. apply psh_morph_Proper. assumption.
  reflexivity. assumption.
- simpl. intros. unfold abstract_PSh_trns.
  etransitivity.  Focus 2.
  apply nattrns_Proper.
 simpl.
  instantiate (1 := psh_morph (prod_PSh X A) ext'
   (psh_morph X ext x, x')).
  simpl. split. apply psh_morph_compose. reflexivity.
 apply nattrns_ok. simpl. split. 
  apply psh_morph_Proper; reflexivity. assumption.
Defined.

Definition abstract_PSh {X A B : PSh} 
  (f : NatTrns (prod_PSh X A) B) : NatTrns X (func_PSh A B).
Proof.
apply (Build_NatTrns X (func_PSh A B) (abstract_PSh_CFunc f)).
- intros. unfold Proper, respectful. simpl.
  unfold abstract_PSh_trns. intros.
  apply nattrns_Proper. simpl. split.
  apply psh_morph_Proper. reflexivity. assumption. assumption.
- simpl. unfold abstract_PSh_trns. intros.
  apply nattrns_Proper. simpl. split.
  etransitivity. apply psh_morph_Proper. reflexivity. eassumption.
  symmetry. apply psh_morph_compose. assumption.
Defined.

Require CMorphisms.

Instance CCat_PSh : CCat PSh :=
  {| arrow := NatTrns
   ; prod := prod_PSh
   ; eq := eq_map
  |}.

Instance CMC_Psh : CMC PSh :=
  {| id := fun _ => id_PSh
  ; compose := fun _ _ _ => compose_PSh
  ; unit := unit_PSh
  ; tt := fun _ => tt_PSh
  ; fst := fun _ _ => fst_Psh
  ; snd := fun _ _ => snd_Psh
  ; pair := fun _ _ _ => pair_PSh
  ; eq_Equivalence := eq_Equivalence_PSh |}.
Proof.
- simpl. unfold eq_map. intros.
  simpl. auto.
- simpl. unfold eq_map. intros. simpl.
  split; auto.
Defined.

Require Import Prob.Spec.CCC.CCC.
Import CCC.

Instance CCCOps_PSh : @CCCOps PSh CCat_PSh :=
  {| Func := func_PSh
  ; eval := fun _ _ => eval_PSh
  ; abstract := fun _ _ _ => abstract_PSh
  |}.

Instance CMCProps_PSh : CMC_Props PSh.
Proof.
constructor; simpl; unfold eq_map; simpl; intros.
- apply nattrns_Proper. assumption.
- apply nattrns_Proper. assumption.
- repeat apply nattrns_Proper. assumption.
- pose proof (nattrns_Proper _ _ h).
  unfold Proper, respectful in H0.
  specialize (H0 Γ x x' H). destruct H0.
  split; assumption.
- apply nattrns_Proper. assumption.
- apply nattrns_Proper. assumption.
- auto.
Qed.

Instance CCCProps_PSh : CCCProps (cccops := CCCOps_PSh).
Proof.
constructor.
simpl. unfold eq_map. simpl. intros.
destruct x, x', H. unfold abstract_PSh_trns. simpl in *.
apply nattrns_Proper. simpl. split.
rewrite psh_morph_id. assumption.
assumption.
Qed. 

End Presheaf.

End Presheaf.