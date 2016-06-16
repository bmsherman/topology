Require Import Coq.Lists.List.
Import ListNotations.
Require Import ContPL.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream.
Import Category.
Import ContPL.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Lift.
Import Stream.
Import Discrete.
Local Open Scope morph.
Local Open Scope obj.

Section Samplers.

  Context {U : Type}.
  Context `{mops : MeasOps U}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) U 
   (LRnn := LRnn)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (R := R)
  (Σ := Σ)}.
  Context {sumops : SumOps}.
  Context `{sigmaops : ΣOps (U := U) (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (Stream:=Stream) (ccat := ccat)}.

  Definition swap {A B : U} : A * B ~~> B * A :=
    ⟨snd, fst⟩.

  Lemma snd_swap {A B : U} : snd ∘ (@swap A B) == fst.
  Proof. unfold swap. rewrite pair_snd. reflexivity.
  Defined.

  
Definition indep {A B : U} : [Prob A ; Prob B] ~> Prob (A * B) := 
   makeFun [Prob A ; Prob B] (fun Γ DA DB =>
                                  a <- !DA;
                                  b <- !DB;
                                  Ret ⟨!a, !b⟩).

Definition inner_indep : forall {A B : U}, (Prob A) * (Prob B) ~~> Prob (A * B).
Proof. intros A B. eapply compose. exact indep.
       unfold nprod. exact ⟨fst, ⟨snd, tt⟩⟩.
Defined.

Definition marg {A B : U} : Prob (A * B) ~~> (Prob A) * (Prob B) := ⟨map fst , map snd⟩.
(* 'marg' for 'marginal' --- I think that this is the correct statistics term. *)

Lemma emap_snd_pair : forall {Γ A B C : U} (f : B ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B), (emap (f ∘ snd)) ∘ ⟨h , k⟩ == (map f) ∘ k.
Proof. intros Γ A B C f h k. unfold emap. rewrite <- map_compose.
       rewrite <- (compose_assoc _ (map snd)).
       rewrite snd_strong. rewrite <- (compose_assoc _ snd). rewrite pair_snd. reflexivity.
Defined.

Lemma emap_fst_pair : forall {Γ A B C : U} (f : Γ ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B), (emap (f ∘ fst)) ∘ ⟨h , k⟩ == ret ∘ f ∘ h.
Proof. intros Γ A B C f h k. unfold emap. rewrite <- map_compose.
       rewrite <- (compose_assoc strong).
       rewrite fst_strong. rewrite -> compose_assoc.
       rewrite ret_nat. rewrite <- (compose_assoc _ fst). rewrite pair_fst.
       reflexivity.
Defined.

Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : (Call indep DS DA) == (emap sample) ∘ ⟨id, DS⟩
      }.

Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.

Theorem map_Ret : forall {Γ A B : U} (f : Γ ~~> A) (h : A ~~> B) , (map h) ∘ (Ret f) == Ret (h ∘ f).
Proof. intros Γ A B f h.
       unfold Ret. rewrite compose_assoc. rewrite <- ret_nat. rewrite compose_assoc.
       reflexivity.
Defined.

Theorem map_Bind : forall {Γ A B C} (f : Γ * A ~~> Prob B) (m : Γ ~~> Prob A) (g : B ~~> C), (map g) ∘ (Bind m f) == Bind m ((map g) ∘ f).
Proof.
  intros Γ A B C f m g.
  unfold Bind. unfold bind. rewrite (compose_assoc _ (join ∘ map f)). rewrite (compose_assoc _ join).
  rewrite join_nat. rewrite <- (compose_assoc _ (map (map g))). rewrite map_compose. reflexivity.
  Defined.

Theorem map_Bind1 : forall {Γ A B C} (f : (Γ * A ~~> A) -> (Γ * A ~~> Prob B)) (e : Γ ~~> Prob A)(g : B ~~> C),
    ((map g) ∘ (x <- e; (f x))) == (x <- e; ((map g) ∘ (f x))).
  intros Γ A B C f e g.
  apply map_Bind.
Defined.

Theorem Bind_emap : forall {Γ A B} (m : Γ ~~> Prob A)(f : Γ * A ~~> Prob B), (Bind m f) == join ∘ (emap f) ∘ ⟨id, m⟩.
Proof. intros Γ A B m f.
       unfold Bind, bind, emap. rewrite compose_assoc, compose_assoc. reflexivity.
Defined.

Definition jmap {Γ A B} (f : Γ * A ~~> Prob B) : Γ * Prob A ~~> Prob B := join ∘ (emap f).

Theorem Bind_push : forall {Γ Δ A B} (m : Γ ~~> Prob A) (f : Γ * A ~~> Prob B) (g : Δ ~~> Γ),
    (Bind m f) ∘ g == (jmap f) ∘ ⟨g, m ∘ g⟩.
Proof. intros Γ Δ A B m f g.
       unfold Bind, bind, jmap, emap. rewrite compose_assoc, compose_assoc.
       rewrite <- (compose_assoc g). rewrite pair_f, compose_id_left.
       reflexivity.
Defined.

Theorem Bind1_push : forall {Γ Δ A B} (e : Γ ~~> Prob A) (f : Γ * A ~~> A -> Γ * A ~~> Prob B) (g : Δ ~~> Γ),
    (x <- e; f x) ∘ g == jmap (f snd) ∘ ⟨ g, e ∘ g ⟩.
Proof. intros Γ Δ A B e f g.
       apply Bind_push.
Defined.

Theorem jmap_Bind_push : forall {Γ Δ A B C} (m : Γ * C ~~> Prob A) (f : (Γ * C) * A ~~> Prob B) (g : Δ ~~> Γ * Prob C),
    (jmap (Bind m f)) ∘ g == ( (jmap (f ∘ prod_assoc_left)) ∘ (id ⊗ inner_indep) ∘ prod_assoc_right ∘ ⟨g, (jmap m) ∘ g⟩).
Proof. intros Γ Δ A B C m f g.
       unfold Bind, bind, jmap, emap.
Abort.      

 
Theorem Bind_Ret : forall {Γ A B} (m : Γ ~~> Prob A) (x : Γ * A ~~> B), (Bind m (Ret x)) == (emap x) ∘ ⟨id, m⟩.
Proof. intros Γ A B m x. (* Probably exists a more direct proof of this from the previous. *) 
       unfold Bind, Ret, emap, bind. rewrite <- map_compose. rewrite (compose_assoc (map x)).
       rewrite join_map_ret, compose_id_left. rewrite compose_assoc. reflexivity.
Defined.

Theorem Bind1_Ret : forall {Γ A B}  (f : (Γ * A ~~> A) -> (Γ * A ~~> B)) (e : Γ ~~> Prob A), (x <- e; Ret (f x)) == (emap (f snd)) ∘ ⟨id, e⟩.
Proof. intros Γ A B f e. apply Bind_Ret.
Defined.

(* This should be true, but I don't think it's useful enough to bother proving. Maybe if I need it later I will.
Theorem strength_indep : forall {A B : U}, (strong (A:=A)(B:=B)) == inner_indep ∘ (ret ⊗ id).
Proof. Abort.
 *)

Lemma ret_Ret : forall {Γ A} (x : Γ ~~> A), (Ret x) == ret ∘ x.  (*TODO is there a non-stupid way to do this? *)
Proof. unfold Ret. reflexivity.
Defined.

Hint Rewrite (@compose_id_left _ _ _ _) (@compose_id_right _ _ _ _) (@pair_fst _ _ _ _) (@pair_snd _ _ _ _) : cat_db.

Theorem marg_inner_indep : forall {A B : U}, (marg (A:=A)(B:=B)) ∘ inner_indep == id.
Proof. intros A B.
       unfold marg. apply proj_eq.
       - rewrite compose_assoc. rewrite pair_fst.
         assert ((map fst) ∘ inner_indep (A:=A)(B:=B) == fst).
         {
           unfold inner_indep.  unfold indep, makeFun. simpl. rewrite compose_assoc.
           setoid_rewrite map_Bind1.
           setoid_rewrite map_Bind1.
           setoid_rewrite map_Ret.
           rewrite pair_fst.
           rewrite Bind_Ret.
           unfold Lift, Extend_Refl, Extend_Prod. simpl. (* I should automate this maybe? *)
           autorewrite with cat_db.
           rewrite emap_fst_pair. autorewrite with cat_db.
           rewrite <- ret_Ret.
           (* NB at this point we've reduced one Bind ... Ret ... to a Ret ... *)
           rewrite Bind_Ret.
           rewrite <- (compose_id_left snd). (* A bit silly, maybe make this special later? *)
           rewrite emap_snd_pair.
           rewrite map_id. rewrite compose_id_left. rewrite pair_fst. reflexivity.
         }

         rewrite compose_id_right. assumption.
         
       - rewrite compose_assoc. rewrite pair_snd.
         assert ((map snd) ∘ inner_indep (A:=A)(B:=B) == snd). (* This and the previous assertion should probably be their own lemmas. *)
         {
           unfold inner_indep. unfold indep, makeFun. simpl. rewrite compose_assoc.
           setoid_rewrite map_Bind1. 
           setoid_rewrite map_Bind1.
           setoid_rewrite map_Ret.
           rewrite pair_snd.
           rewrite Bind_Ret.
           unfold Lift, Extend_Refl, Extend_Prod. simpl.
           autorewrite with cat_db.
           rewrite <- (compose_id_left snd).
           rewrite emap_snd_pair.
           rewrite map_id. rewrite compose_id_left.
           rewrite Bind_emap.
           rewrite <- (compose_assoc _ _ join).
           rewrite emap_fst_pair. rewrite compose_id_right. rewrite compose_assoc.
           rewrite join_ret, compose_id_left. rewrite <- compose_assoc.
           rewrite pair_snd, pair_fst. reflexivity.
         } 
         rewrite compose_id_right. assumption.
Defined.

Section Constant_Sampler.
  (* Δ S ~~> S A := (Δ * A) * S ~~> S * A. *)
Definition const_sampler {Δ A S : U} {D : Δ * A ~~> Prob S} : Sampler (Δ := Δ * A) (A := A) (S := S) D (ret ∘ snd).
Proof. refine (sampler ⟨snd, snd ∘ fst⟩ _).
       Check (map swap) ∘ strong ∘ ⟨snd, D⟩. Check (emap ⟨snd , snd ∘ fst ⟩ ∘ ⟨id, D⟩).
       assert (emap ⟨snd , snd ∘ fst ⟩ ∘ ⟨id, D⟩ == (map swap) ∘ strong ∘ ⟨snd, D⟩).
       {
         unfold emap, swap.
         assert (⟨snd, D⟩ == (snd ⊗ id) ∘ ⟨id, D⟩).
         {
           rewrite parallel_pair. autorewrite with cat_db. reflexivity.
         }
         rewrite H0, compose_assoc.
         rewrite <- (compose_assoc (snd ⊗ id)).
         rewrite <- map_id. rewrite strong_nat.
         rewrite compose_assoc, map_compose, pair_f.
         unfold parallel. rewrite pair_snd, pair_fst, compose_id_left.
         reflexivity.
       }
       rewrite H0.
       
       (* ***** *)
       unfold indep. unfold makeFun, Call, prodsplay. 
       unfold Lift, Extend_Prod, Extend_Refl. simpl.
       rewrite Bind1_push.
       autorewrite with cat_db.
       
Abort.
       

End Constant_Sampler.

Section Coinflip_Sampler.

  Definition Boole := unit + unit.
  Definition Cantor := Stream Boole.

  Definition infinite_coinflips : unit ~~> Prob Cantor := pstream (MeasOps := mops) coinflip (coinflip ∘ tt).

  Definition coinflip_sampler : Sampler (Δ := unit) (S := Cantor) (A := Boole) infinite_coinflips coinflip.
  Proof.
    refine (sampler (⟨tl, hd⟩ ∘ snd) _).
    rewrite emap_snd_pair.
    unfold Call, indep, makeFun, Lift, prodsplay, Extend_Prod, Extend_Refl. simpl.
  Abort.
  
End Coinflip_Sampler.
