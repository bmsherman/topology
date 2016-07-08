Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Language.ContPL Language.ContPLProps.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream
  Spec.SMonad.
Import Category.
Import ContPL.
Import ContPLProps.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Lift.
Import Stream.
Import CCC.
Import Discrete.
Import Presheaf.
Local Open Scope morph.
Local Open Scope obj.

Section Samplers.

  Context {U : Type}.
  Context `{sigmaops : ΣOps (U := U)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) (Σ := Σ) U}.
  Context `{sumops : SumOps (U:=U) (ccat := ccat)}.
  Context `{sumprops : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc) (sts:=sts)(H:=sumops)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{Streamprops : StreamProps (U:= U)(ccat:=ccat) (Stream:=Stream)(cmc:=cmc) (sps:=Streamops)}.
  Context `{mops : MeasOps U
(ccat := ccat) (cmcprops := CMCprops)
  (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)
                                    (cmcprops := CMCprops) (smd := ProbMonad)}.
  Context {discrete : Type -> U}.
  Context {pow : Type -> U -> U}.
  Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete pow}.
  Context {DProps : (@DiscreteProps U ccat cmc discrete pow DOps)}.

  Infix "-~>" := pow (at level 30) : obj_scope. 
  
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
  
  Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : indep DS DA == Map sample DS
      }.

  Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.

  Section Constant.
  
  Definition const_sampler_prog {Δ A S : U} (x : Δ ~~> A) : Δ * S ~~> S * A :=
    'LAM'<< _ | _ >> s => ⟨s, !x⟩.
         
  
  Definition const_sampler {Δ A S : U} {D : Δ ~~> Prob S} {x : Δ ~~> A} :
    Sampler (Δ := Δ) (A := A) (S := S) D (Ret x).
  Proof. refine (sampler (const_sampler_prog x) _).       
         unfold indep. 
         simpl_ext.
         rewrite bind_extensional. Focus 2. intros.
         setoid_rewrite Ret_ext.
         setoid_rewrite Bind'_Ret_f.
         rewrite lam_eval. rewrite compose_id_right.
         rewrite <- (compose_id_right ⟨a, x ∘ ext⟩).
         reflexivity.
         rewrite Map_prog.
         apply Bind_Proper; try reflexivity.
         apply lam_extensional; intros.
         rewrite !ret_Ret. remove_eq_left.
         rewrite compose_id_right.
         unfold const_sampler_prog.
         rewrite ap2_ext_eval.
         simpl_ext.
         reflexivity.
  Qed.

  End Constant.

  Section Infinite.
    
  Definition constant_stream {Γ A : U} (mu : Γ ~~> Prob A) :
    Γ ~~> Prob (Stream A) := 
    pstream (MeasOps := mops) (Γ := Γ) tt (LAM _ => map add_unit_right ∘ !mu).
  
  Theorem constant_stream_ext1 : forall {Γ Δ A : U} (mu : Δ ~~> Prob A) (f : Γ ~~> Δ),
      constant_stream (mu ∘ f) == (constant_stream mu) ∘ f.
  Proof. intros Γ Δ A mu f.
         unfold constant_stream.
         rewrite pstream_ext1.
         apply pstream_Proper.
         - symmetry. apply unit_uniq.
         - unfold makeFun1E, Lift, Extend_Prod, Extend_Refl, extend.
           autorewrite with cat_db.
           rewrite <- !compose_assoc.
           rewrite parallel_fst. reflexivity.
  Qed.
  
  
  Definition constant_unfold_prog : forall {Γ A : U} (mu : Γ ~~> Prob A), Γ ~~> Prob (Stream A).
  Proof. intros. (* Check (constant_stream mu). *)
         unshelve eapply (y <- mu;<< _ | _>> (zs <- constant_stream (!mu);<<_ | _>> _)).
         unshelve eapply (Ret (cons (!y) zs)).
         (* Show Proof.  *)
  Defined.
  
  Existing Instance pstream_Proper.
  
  
  Theorem constant_unfold : forall {Γ A : U} (mu : Γ ~~> Prob A),
      (constant_stream mu) == (constant_unfold_prog mu).
  Proof. intros Γ A mu.
         unfold constant_unfold_prog, constant_stream.
         rewrite pstream_unfold.
         symmetry.
         apply Bind_iso with add_unit_right.
         rewrite lam_eval. simpl_ext. reflexivity.
         rewrite lam_eval_par. apply lam_extensional. 
         intros. apply Bind_Proper. apply pstream_Proper. 
         symmetry. apply unit_uniq. unfold liftF.
         rewrite lam_eval_par'. apply lam_extensional.
         intros. simpl_ext. rewrite <- !compose_assoc. reflexivity.
         apply lam_extensional. intros. 
         unfold Ret. remove_eq_left. apply cons_Proper.
         simpl_ext. unfold add_unit_right. 
         rewrite <- !compose_assoc. rewrite compose_assoc.
         autorewrite with cat_db. reflexivity.
         reflexivity.
  Qed.
  

  
  Existing Instance Streamprops.

  Definition infinite_sampler_prog {Δ A : U} : Δ * (Stream A) ~~> (Stream A) * A.
  Proof. eapply ('LAM'<< Δ' | e >> aa => ⟨tl, hd⟩ ∘ aa). (* Show Proof. *)
  Defined.

  
  Definition infinite_sampler (Δ A : U) (D : Δ ~~> Prob A) : Sampler (Δ := Δ)(S := Stream A)(A :=A)
                                                                   (constant_stream D) D.
  Proof. refine (sampler infinite_sampler_prog _).
         rewrite Map_prog.
         unfold indep, infinite_sampler_prog.
         rewrite constant_unfold at 2; unfold constant_unfold_prog.
         rewrite Bind'_Bind'.
         rewrite Fubini_pair.
         apply Bind_Proper; try reflexivity.
         apply lam_extensional; intros.
         rewrite Bind'_Bind'. apply Bind_Proper.
         simpl_ext. symmetry. apply constant_stream_ext1.
         apply lam_extensional; intros.
         rewrite Bind'_Ret_f. rewrite lam_eval.
         unfold ret; remove_eq_left.
         rewrite ap2_ext_eval.
         rewrite pair_f.
         rewrite cons_tl', cons_hd.
         reflexivity.
  Qed.
  
  Section Coinflip.
    
  Definition Boole := unit + unit.
  Definition Cantor := Stream Boole.
  
  Definition infinite_coinflips : unit ~~> Prob Cantor := 
    constant_stream coinflip.
  
  Definition coinflip_sampler :
    Sampler (Δ := unit) (S := Cantor) (A := Boole) infinite_coinflips coinflip :=
    infinite_sampler _ _ _.

  End Coinflip.
  
  End Infinite.
  
  (* Definition compose_sampler (Δ S A B : U) (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ ~~> Prob B) :
    (Sampler DS DA) -> (Sampler DA DB) -> (Sampler DS DB).  (* This is overkill, since the A ~> B could destroy A and we'd still be fine. *)
  Proof. intros [ S0 samples0 ] [S1 samples1].
         refine (sampler _ _).
         Unshelve. Focus 2.
         refine (_ ∘ ⟨fst, S0⟩).
         refine (_ ∘ prod_assoc_right ∘ swap).
  Abort. *)

  Section Pullback.
  
  Definition pullback_sampler {Δ Δ' S A : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (ext : Extend Δ Δ') :
    (Sampler (Δ := Δ) DS DA) -> (Sampler (Δ := Δ') (DS ∘ ext) (DA ∘ ext)).
  Proof. intros [SA samples]. refine (sampler (SA ∘ (ext ⊗ id)) _).
         unfold Extend in ext.
         rewrite <- indep_ext.
         rewrite samples.
         rewrite !Map_prog.
         rewrite Bind'_ext.
         apply Bind_Proper; try reflexivity.
         apply lam_extensional; intros.
         unfold Ret, ap2; remove_eq_left.
         rewrite parallel_pair.
         rewrite compose_id_left.
         reflexivity.
  Qed.

  End Pullback.

  Section Bind.

  Definition bind_distr_prog {Δ A B : U} (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    (Δ ~~> Prob B).
  Proof. refine (a <- DA;<< _ | _ >> (b <- DB ∘ ⟨!id, a⟩;<< _ | _ >> (Ret b))).
  Defined.

  Definition bind_sampler_prog {Δ A B S : U} (SA : Δ * S ~~> S * A) (SB : Δ * A * S ~~> S * B)
    : Δ * S ~~> S * B.
  Proof. refine (SB ∘ prod_assoc_left ∘ ⟨fst , swap ∘ SA⟩).
        (* refine ('LAM'<< Δ' | e >> s => 
                              let s':= fst ∘ (ap2 SA e s) in
                              let a := snd ∘ (ap2 SA e s)
                              in (ap3 SB e a s)). *)
  Defined.

  Theorem bind_distr_prog_spec : forall {Δ A B : U} (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B),
      bind_distr_prog DA DB == Bind DA DB.
  Proof. intros Δ A B DA DB. unfold bind_distr_prog.
         setoid_rewrite Bind_m_Ret.
         rewrite emap_snd.
         simpl_ext.
         autorewrite with cat_db.
         rewrite pair_id, compose_id_right.
         reflexivity.
  Qed.         
         
      
  
  Definition bind_sampler {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    forall (SA : Sampler DS DA) (SB : Sampler (Δ := Δ * A) (DS ∘ fst) DB),
      Sampler DS (bind_distr_prog DA DB).
  Proof. intros [SA samplesA] [SB samplesB].

         refine (sampler (bind_sampler_prog SA SB) _).
         pose proof (Bind_Proper DA DA (Equivalence_Reflexive DA) _ _ samplesB) as samplesB'.
         rewrite indep_integral_right in samplesB'.
         rewrite Bind_Map_indep in samplesB'.
         unfold bind_sampler_prog.
         rewrite <- Map_compose.
         assert (Map (SB ∘ prod_assoc_left) (Map (swap ∘ SA) DS)
                 == Map (SB ∘ prod_assoc_left) ((map swap) ∘ (indep DS DA))).
         { apply Map_Proper; try reflexivity. rewrite Map_post. rewrite samplesA. reflexivity. }
         rewrite H.
         rewrite bind_distr_prog_spec. rewrite samplesB'.
         apply Map_Proper; try reflexivity.
         rewrite swap_indep. reflexivity.
  Qed.
  
  (* Program transforms. 
         rewrite Map_prog.
         unfold indep, bind_distr_prog, bind_sampler_prog.
         unfold indep in samplesB. rewrite Map_prog in samplesB.
         unfold indep in samplesA. rewrite Map_prog in samplesA.
         unfold Lift at 1. *)
  
  End Bind.

  Section Unzip.
    
    Theorem constant_unzip : forall {Γ A} (f : Γ ~~> Prob A),
      (map (unzip (sps:=Streamops)(A:=A)) ∘ (constant_stream f)) == indep (constant_stream f) (constant_stream f).
    Proof. intros.
           rewrite constant_unfold at 1. unfold constant_unfold_prog.
    Abort.

  End Unzip.

  Section Geometric.

    Existing Instance DProps.

    Notation "| A |" := (unit ~~> A) (at level 90).

    Definition natlist_to_stream {A} : (nat -> |A|) -> |Stream A|.
    Proof. intros L.  refine (stream (X := (nat -~> A)) (A:=A) _ _).
           - refine (pow_app2' _ _ L).  (* initial *)
           - refine ⟨_, _⟩. (* step *)
             + apply (pow_app1  _ _ 0).
             + apply (pmap _ _ S id).
           (* Show Proof. *)
    Defined.
    
    Definition stream_to_natlist {A} : (unit ~~> Stream A) -> (nat -> (unit ~~> A)) :=
      fun s n => idx n ∘ s.

    Theorem stream_to_stream : forall {A} (s : unit ~~> Stream A),
        natlist_to_stream (stream_to_natlist s) == s.
    Proof. 
    Abort.


    
  End Geometric.
  
End Samplers.
