Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Samplers.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Language.ContPL Language.ContPLProps.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream
  Spec.SMonad Spec.Vec Spec.Power Spec.Fix.
Import Category.
Import ContPL.
Import ContPLProps.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Fix.
Import Vec.
Import Lift.
Import Power.
Import Stream.
Import CCC.
Import Discrete.
Import Presheaf.
Local Open Scope morph.
Local Open Scope obj.

Section PartialSamplers.

  Context {U : Type}.
  Context `{sigmaops : ΣOps (U := U)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) (Σ := Σ) U}.
  Context `{sumops : SumOps (U:=U) (ccat := ccat)}.
  Context `{sumprops : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc) (sts:=sts)(H:=sumops)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{Streamprops : StreamProps (U:= U)(ccat:=ccat) (Stream:=Stream)(cmc:=cmc) (sps:=Streamops)}.
  Context `{mops : MeasOps U (ccat := ccat) (cmcprops := CMCprops)
                           (Σ:=Σ)  (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)
                                    (cmcprops := CMCprops) (smd := ProbMonad)}.
  Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete}.
  Context {DProps : (@DiscreteProps U ccat cmc discrete DOps)}.
  Context `{pos : PowOps (U:=U) (ccat:=ccat)(power:=power)}.
  Variable L : U -> U. 
  Context `{los : LiftOps (U:=U)(Σ:=Σ)(ccat:=ccat)(Stream:=Stream)(cmc:=cmc)(sts:=sts)(Lift:=L)}.
  Context {lps : LiftProps (Embedding := Embedding)}.
  
  
  Infix "-~>" := power (at level 90). 
  
  Existing Instance ProbMonad.
  Existing Instance Streamops.
 (*

Candidates for below I'm not sure about:
 (@to_from _ _ _ _ _ _), (@from_to _ _ _ _ _ _ _)

There's an argument to be made for adding parallel_pair, but I don't think I want it.

  *)
 
  Hint Rewrite
       (@compose_id_left _ _ _ _) (@compose_id_right _ _ _ _)
       (@pair_fst _ _ _ _) (@pair_snd _ _ _ _)
       (@parallel_fst _ _ _ _) (@parallel_snd _ _ _ _)
       (@unit_uniq _ _ _ _)
       (@map_id _ Prob _ _ _ _ _)
       (@join_map_ret _ _ _ _ _ _ _) (@join_ret _ _ _ _ _ _ _)
       (@strength_ret _ _ _ _ _ _ _)
       (@fst_strong _ _ _ _) (@snd_strong _ _ _ _ _ _ _)
       (@stream_hd _ _ _) (@stream_tl _ _ _)
    : cat_db.

  (* Theoretically this should be imported from elsewhere, but I don't know how to. *)
  Ltac simpl_ext := unfold liftF, Lift, Extend_Prod, Extend_Refl, extend;
                    repeat rewrite compose_id_right.
  
  Notation "'LAM'<< Γ | E >> x => f" := (makeFun1E (fun Γ E x => f))
                                          (at level 120, right associativity). 
  
  Notation "x <- e ;<< Γ | E >> f" := (Bind e (makeFun1E (fun Γ E x => f))) 
                                        (at level 120, right associativity).
  
(*  Definition PTerm : PSh U -> Type := (@Term (PSh U) (CCat_PSh) CMC_PSh CCCOps_PSh).
  Definition Fun (A B : PSh U) : PSh U.
  Proof. refine (A ==> B). exact CCCOps_PSh. Defined.
  Definition konst {A B : PSh U} : PTerm (Fun A (Fun B A)) :=
    [ λ (x : _ A) y => ! x ]%stlc. *)
  
  Record PartialSampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    par_sampler
      {
        sample : Δ * S ~~> L (S * A);
        sampling_cond :  Prob_to_Meas ∘ indep DS DA == 
          unlift ∘ Prob_to_Meas ∘ (Map sample DS)  
      }.

  Arguments par_sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.

  Existing Instance MeasMonad.

  Definition Cantor := Samplers.Cantor (Stream:=Stream).
  
  Definition F : unit * Cantor ~~> L (Cantor * Boole) ->
                 unit * Cantor ~~> L (Cantor * Boole).
  Proof. intros f.
         refine (_ ∘ ⟨tl, hd⟩ ∘ snd).
         eapply sum_elim.
         - exact  (f ∘ add_unit_left ∘ fst). (* recurse *)
         - refine (strict ∘ _). (* respond *)
           exact ⟨fst, inl ∘ tt⟩.
  Defined.

  Existing Instance sleq_Proper.
  
  Lemma F_Proper : Proper (sleq(Σ:=Σ) ==> sleq(Σ:=Σ)) F.
  Proof.
    unfold Proper, respectful.
    intros x y H.
    unfold F.
    repeat (apply compose_sleq; try apply sleq_reflexive).
    apply sum_sleq.
    - rewrite !sum_elim_inl. repeat apply compose_sleq; try apply sleq_reflexive; try assumption.
    - rewrite !sum_elim_inr. apply sleq_reflexive.
  Qed.

  Definition fixF : unit * Cantor ~~> L (Cantor * Boole).
  Proof. eapply (sfix F). apply (ishas bottom_min). eapply F_Proper.
  Defined.

  Definition stupid_sampler : PartialSampler (Δ := unit) (S := Samplers.Cantor) (A := Boole)
                                             infinite_coinflips (Ret inl).
  Proof. unshelve eapply par_sampler.         
         refine (recursion (id ∘ snd) _). (* could make this be 'snd' and rewrite later in proof *)
         refine (_ ∘ ⟨tl, hd⟩).
         eapply sum_elim.
         (* Left, we got a zero; look in the tail. *)
         apply (recall fst).
         (* Right, we got a one; we're done. *)
         apply (throw (id ⊗ inl)).         

         (* Now 'only' the proof goal is left. *)
         rewrite recursion_ext1.
         rewrite Map_snd.
  Abort.
  
  Definition stupid_sampler' : PartialSampler (Δ := unit) (S := Samplers.Cantor) (A := Boole)
                                              infinite_coinflips (Ret inl).
  Proof.
    unshelve eapply par_sampler.
    apply fixF.
    unfold Map.
  Abort.    

End PartialSamplers.
        