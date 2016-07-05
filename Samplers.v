Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Language.ContPL Language.ContPLProps.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream.
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
(ccat := ccat) (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc) (smd := ProbMonad)}.

  Existing Instance ProbMonad.
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
       (@map_id _ Prob _ _ _ _)
       (@join_map_ret _ _ _ _ _ _) (@join_ret  _ _ _ _ _ _)
       (@strength_ret _ _ _ _ _ _)
       (@fst_strong _ _ _) (@snd_strong _ _ _ _ _ _)
       (@stream_hd _ _ _) (@stream_tl _ _ _)
    : cat_db.

  
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
  
    
    Definition const_sampler {Δ A S : U} {D : Δ ~~> Prob S} {x : Δ ~~> A} :
      Sampler (Δ := Δ) (A := A) (S := S) D (Ret x).
    Proof. refine (sampler ⟨snd, x ∘ fst⟩ _).       
           unfold indep. 
           unfold Lift, Extend_Prod, Extend_Refl. simpl.
           rewrite bind_extensional. Focus 2.
           intros a.
           setoid_rewrite Ret_ext.
           (* Check Bind'_Ret_f. *)
           setoid_rewrite Bind'_Ret_f.
           unfold makeFun1E. intros.
           rewrite Ret_ext.
           rewrite pair_f. 
           reflexivity.
           simpl.
           setoid_rewrite Ret_ext. setoid_rewrite pair_f.
           unfold extend, Extend_Prod, Extend_Refl.
           autorewrite with cat_db.
           rewrite <- (compose_assoc _ fst snd). autorewrite with cat_db.
           rewrite Bind_m_Ret.
           reflexivity.
Defined.
 
  
  
  Definition Boole := unit + unit.
  Definition Cantor := Stream Boole.
  
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
           

  
  Definition infinite_coinflips : unit ~~> Prob Cantor := 
    constant_stream coinflip.
  
  Definition constant_unfold_prog : forall {Γ A : U} (mu : Γ ~~> Prob A), Γ ~~> Prob (Stream A).
  Proof. intros. (* Check (constant_stream mu). *)
         refine (y <- mu; (zs <- constant_stream (!mu); _)).
         refine (Ret (cons (!y) zs)).
         (* Show Proof. *)
  Defined.

  Existing Instance pstream_Proper.

  (* Theoretically this should be imported from elsewhere, but I don't know how to. *)
  Ltac simpl_ext := unfold liftF, Lift, Extend_Prod, Extend_Refl, extend;
                    repeat rewrite compose_id_right.
  

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
           


  (* Maybe this should be elsewhere? *)
  
  Theorem Fubini_pair : forall {Γ A B} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
    (x <- mu; y <- !nu; Ret ⟨!x, y⟩) == (y <- nu; x <- !mu; Ret ⟨x, !y⟩).
  Proof. intros Γ A B mu nu.
         refine (Fubini mu nu (fun _ _ a b => Ret ⟨a, b⟩) (fun _ _ a b => Ret ⟨a, b⟩) _).
         intros. reflexivity.         
  Qed.                

  Existing Instance Streamprops.


  Definition infinite_sampler (Δ A : U) (D : Δ ~~> Prob A) : Sampler (Δ := Δ)(S := Stream A)(A :=A)
                                                                   (constant_stream D) D.
  Proof. refine (sampler (⟨tl, hd⟩ ∘ snd) _).
         unfold Map; rewrite emap_snd_pair.
         unfold indep. rewrite Fubini_pair.
         rewrite constant_unfold; unfold constant_unfold_prog.

         rewrite map_Bind. apply Bind_Proper; try reflexivity.
         rewrite lam_postcompose; apply lam_extensional.
         intros. simpl.

         rewrite map_Bind. apply Bind_Proper.
         - simpl_ext. rewrite constant_stream_ext1.
           reflexivity.
         - rewrite lam_postcompose; apply lam_extensional.
           intros. simpl.
           rewrite map_Ret.
           apply Ret_Proper.
           rewrite pair_f.
           rewrite cons_tl', cons_hd.
           reflexivity.
  Qed.

  Definition coinflip_sampler :
    Sampler (Δ := unit) (S := Cantor) (A := Boole) infinite_coinflips coinflip :=
    infinite_sampler _ _ _.
  
  Definition compose_sampler (Δ S A B : U) (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ ~~> Prob B) :
    (Sampler DS DA) -> (Sampler DA DB) -> (Sampler DS DB).  (* This is overkill, since the A ~> B could destroy A and we'd still be fine. *)
  Proof. intros [ S0 samples0 ] [S1 samples1].
         refine (sampler _ _).
         Unshelve. Focus 2.
         refine (_ ∘ ⟨fst, S0⟩).
         refine (_ ∘ prod_assoc_right ∘ swap).
  Abort.

  Definition pullback_sampler {Δ Δ' S A : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (ext : Extend Δ Δ') :
    (Sampler (Δ := Δ) DS DA) -> (Sampler (Δ := Δ') (DS ∘ ext) (DA ∘ ext)).
  Proof. intros [SA samples]. refine (sampler (SA ∘ (ext ⊗ id)) _).
         unfold Extend in ext.
         rewrite <- indep_ext.
         rewrite samples.
         unfold Map, emap. (* extract to Map_ext? *)
         rewrite map_compose.
         rewrite <- (compose_assoc strong).
         rewrite <- strong_nat.
         rewrite <- !compose_assoc.
         rewrite parallel_pair.
         autorewrite with cat_db.
         rewrite <- (compose_id_left ext) at 2.
         rewrite <- pair_f.
         rewrite !compose_assoc.
         reflexivity.
  Qed.
            

  Definition bind_sampler_prog {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    (Δ ~~> Prob B).
  Proof. refine (a <- DA; _).
         refine (b <- DB ∘ ⟨e, a⟩; _).
         refine (Ret b).
  Defined.
  

  
  Definition bind_sampler {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    forall (SA : Sampler DS DA) (SB : Sampler (Δ := Δ * A) (DS ∘ fst) DB),
      Sampler DS (bind_sampler_prog DS DA DB).
  Proof. intros [SA samplesA] [SB samplesB].
         refine (sampler _ _).
         Unshelve. Focus 2.
         refine ('LAM'<< Δ' | e >> s =>
                               let s':= fst ∘ (ap2 SA e s) in
                               let a := snd ∘ (ap2 SA e s)
                               in (ap3 SB e a s)).
         rewrite Map_program. 

         assert ((s <- DS;<< Δ0 | e >>
    Ret
      (ap2
         ('LAM'<< Δ' | e0 >> s0 =>
                       (let s' := fst ∘ ap2 SA e0 s0 in let a := snd ∘ ap2 SA e0 s0 in ap3 SB e0 a s0)) e s)) ==
                 (s <- DS;<< Δ0 | e >>
     Ret (ap3 SB e (snd ∘ ap2 SA e s) s))).
         { apply bind_extensional; intros. rewrite ap2_ext_eval. reflexivity. }
         rewrite H.
         
         (* refine (SB ∘ (prod_assoc_left ∘ id ⊗ swap) ∘ ⟨fst, SA⟩). *)
   
(*         unfold bind_sampler_prog. (* Just Bind DA DB *)
         setoid_rewrite Bind_m_Ret.
         rewrite <- (compose_id_left snd). rewrite emap_snd_pair.
         simpl_ext.
         autorewrite with cat_db. *)
         unfold indep.
  Abort.

  End Samplers.