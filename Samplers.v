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
         rewrite Map_program.
         apply Bind_Proper; try reflexivity.
         apply lam_extensional; intros.
         rewrite !ret_Ret. remove_eq_left.
         autorewrite with cat_db.
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
  

  
  (* Maybe this should be elsewhere? *)
  
  Theorem Fubini_pair : forall {Γ A B} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
      (x <- mu; y <- !nu; Ret ⟨!x, y⟩) == (y <- nu; x <- !mu; Ret ⟨x, !y⟩).
  Proof. intros Γ A B mu nu.
         unshelve eapply (Fubini mu nu (fun _ _ a b => Ret ⟨a, b⟩) (fun _ _ a b => Ret ⟨a, b⟩) _).
         intros. reflexivity.         
  Qed.                
  
  Existing Instance Streamprops.

  Definition infinite_sampler_prog {Δ A : U} : Δ * (Stream A) ~~> (Stream A) * A.
  Proof. eapply ('LAM'<< Δ' | e >> aa => ⟨tl, hd⟩ ∘ aa). Show Proof.
  Defined.

  
  Definition infinite_sampler (Δ A : U) (D : Δ ~~> Prob A) : Sampler (Δ := Δ)(S := Stream A)(A :=A)
                                                                   (constant_stream D) D.
  Proof. refine (sampler infinite_sampler_prog _).
         rewrite Map_program.
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
         rewrite !Map_program.
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

  Definition bind_sampler_prog {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    (Δ ~~> Prob B).
  Proof. unshelve eapply (a <- DA; _).
         unshelve eapply (b <- DB ∘ ⟨e, a⟩; _).
         eapply (Ret b).
  Defined.
  

  
  Definition bind_sampler {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    forall (SA : Sampler DS DA) (SB : Sampler (Δ := Δ * A) (DS ∘ fst) DB),
      Sampler DS (bind_sampler_prog DS DA DB).
  Proof. intros [SA samplesA] [SB samplesB].
         unshelve eapply sampler.
         apply ('LAM'<< Δ' | e >> s =>
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
         unfold bind_sampler_prog. simpl_ext.
         assert ((a <- DS;<< Δ0 | ext >>
                  b <- (a0 <- DA;<< Δ1 | ext0 >>
                        b <- DB ∘ ⟨ ext0, a0 ⟩;<< Δ2 | _ >>
                        Ret b) ∘ ext;<< Δ1 | ext0 >>
                 Ret ⟨ a ∘ ext0, b ⟩) ==
                 (a <- DS;<< Δ0 | ext >>
                  b <- (a <- DA ∘ ext;<< Γ' | eΓ >>
                       b <- DB ∘ ⟨ ext ∘ eΓ, a ⟩;<< Δ2 | _ >>
                       Ret b);<< Δ1 | ext0 >>                                                                               Ret ⟨ a ∘ ext0, b ⟩)) as change0.
         { apply bind_extensional. intros. rewrite Bind'_ext. reflexivity. }
         rewrite change0.
         assert (( (a <- DS;<< Δ0 | ext >>
                    b <- a0 <- DA ∘ ext;<< Γ' | eΓ >>
                         b <- DB ∘ ⟨ ext ∘ eΓ, a0 ⟩;<< Δ2 | _ >>
                        Ret b;<< Δ1 | ext0 >>
                    Ret ⟨ a ∘ ext0, b ⟩)) ==
                  ((a <- DS;<< Δ0 | ext >>
                    y <- DA ∘ ext;<< Δ' | eΔ >>
                    x <- b <- DB ∘ ⟨ ext ∘ eΔ, y ⟩;<< Δ2 | _ >>
                        Ret b;<< Δ'' | eΔ' >>
                    Ret ⟨ a ∘ (eΔ ∘ eΔ'), x ⟩) )) as change1.
         { apply bind_extensional. intros. rewrite Bind'_Bind'. reflexivity. }
         rewrite change1.
         assert ((a <- DS;<< Δ0 | ext >>
                    y <- DA ∘ ext;<< Δ' | eΔ >>
                    x <- b <- DB ∘ ⟨ ext ∘ eΔ, y ⟩;<< Δ2 | _ >>
                        Ret b;<< Δ'' | eΔ' >>
                    Ret ⟨ a ∘ (eΔ ∘ eΔ'), x ⟩) ==
                 (s <- DS;<< Δ0 | ext0 >>
                  a <- !DA;<< Δ1 | ext1 >>
                  b <- !(DB ∘ ⟨ !id, a ⟩);<< Δ2 | ext2 >>
                  Ret ⟨ !(!s) , b ⟩)
                 ) as change2.
         { apply bind_extensional; intros. apply bind_extensional; intros.
           rewrite (Bind'_m_Ret (DB ∘ ⟨ext ∘ ext0, a0⟩)).
           rewrite lam_id. rewrite emap_snd. simpl_ext. unfold Extend_Compose. autorewrite with cat_db.
           apply Bind_Proper; try reflexivity. apply lam_extensional; intros. rewrite compose_assoc.
           reflexivity. }
         rewrite change2.
         (* assert ((s <- DS;<< Δ0 | ext0 >>
                  a <- !DA;<< Δ1 | ext1 >>
                  b <- !(DB ∘ ⟨ !id, a ⟩);<< Δ2 | ext2 >>
                  Ret ⟨ !(!s) , b ⟩) ==
                 (a <- DA;<< Δ0 | ext0 >>
                  s <- !DS;<<Δ1 | ext1>>
                  b <- !(DB ∘ ⟨!id, !a⟩);<< Δ2 | ext2>>
                  Ret ⟨!s, b⟩)) as change3.
         { admit. (* Fubini DS DA... *) }
         rewrite change3. *)
         unfold indep in samplesA.
         rewrite Map_program in samplesA.
  Abort.

  End Bind. 
  
  End Samplers.
