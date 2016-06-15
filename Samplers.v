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


Theorem Bind_Ret : forall {Γ A B} (m : Γ ~~> Prob A) (x : Γ * A ~~> B), (Bind m (Ret x)) == (emap x) ∘ ⟨id, m⟩.
Proof. intros Γ A B m x. (* Probably exists a more direct proof of this from the previous. *) 
       unfold Bind, Ret, emap, bind. rewrite <- map_compose. rewrite (compose_assoc (map x)).
       rewrite join_map_ret, compose_id_left. rewrite compose_assoc. reflexivity.
Defined.


(* This should be true, but I don't think it's useful enough to bother proving. Maybe if I need it later I will.
Theorem strength_indep : forall {A B : U}, (strong (A:=A)(B:=B)) == inner_indep ∘ (ret ⊗ id).
Proof. Abort.
 *)

Lemma ret_Ret : forall {Γ A} (x : Γ ~~> A), (Ret x) == ret ∘ x.  (*TODO is there a non-stupid way to do this? *)
Proof. unfold Ret. reflexivity.
       Defined.

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
           rewrite compose_id_left, compose_id_left.  (*This too.*)
           rewrite emap_fst_pair. rewrite compose_id_right, compose_id_right.
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
           rewrite compose_id_right, compose_id_right. rewrite <- (compose_id_left snd).
           rewrite emap_snd_pair. rewrite compose_id_left.
           rewrite map_id. rewrite compose_id_left.
           rewrite Bind_emap.
           rewrite <- (compose_assoc _ _ join).
           rewrite emap_fst_pair. rewrite compose_id_right. rewrite compose_assoc.
           rewrite join_ret, compose_id_left. rewrite <- compose_assoc.
           rewrite pair_snd, pair_fst. reflexivity.
         } 
         rewrite compose_id_right. assumption.
Defined.
          

Definition const_sampler {A : U} : Sampler (Δ := A) (S := unit) (ret ∘ tt) ret.
Proof. refine (sampler swap _). unfold emap. eapply (isom_eq_left _ _ (M_iso unit_isom_left)).
       unfold M_iso. simpl. rewrite (compose_assoc _ (map swap ∘ strong)), (compose_assoc _ (map swap)).
       rewrite map_compose. rewrite snd_swap.
       assert ((strong ∘ ⟨id (A:=A), ret ∘ tt⟩) == (ret ∘ ⟨id, tt⟩)) as beginning.
       { assert (⟨id (A:=A), ret ∘ tt⟩ == (id ⊗ ret) ∘ ⟨id, tt⟩) as Δ0.
         { rewrite parallel_pair. rewrite compose_id_left. reflexivity.
         } rewrite Δ0. rewrite compose_assoc. rewrite <- strength_ret. reflexivity.
       }
       rewrite <- compose_assoc, beginning. eapply (isom_eq_right _ _ (unit_isom_right)).
       simpl. rewrite <- (compose_assoc _ (ret ∘ ⟨id, tt⟩)). rewrite <- (compose_assoc _ ⟨id, tt⟩).
       assert (⟨id (A:=A), tt⟩ ∘ fst == id) as cancel.
       { apply (from_to unit_isom_right). }
       rewrite cancel. rewrite compose_id_right. rewrite <- ret_nat.
       unfold indep. unfold makeFun, Call, prodsplay. simpl.
       rewrite compose_assoc.
       rewrite map_Bind1.
       setoid_rewrite (map_Bind1 _ _ snd).
       setoid_rewrite map_Ret.
       rewrite pair_snd. 
       unfold Lift, Extend_Prod, Extend_Refl.
       rewrite compose_id_right, compose_id_left, compose_id_right.
       rewrite Bind_Ret.
       rewrite <- (compose_id_left snd). rewrite emap_snd_pair.
       rewrite map_id, compose_id_left.
       rewrite Bind_emap.
       rewrite <- (compose_assoc _ _ join).
       rewrite emap_fst_pair, compose_id_right.
       rewrite compose_assoc, join_ret, compose_id_left.
       rewrite <- (compose_assoc _ snd fst).
       rewrite pair_snd, pair_fst.
       reflexivity.
Defined.
