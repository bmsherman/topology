Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Language.ContPL Language.ContPLProps.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream
  Spec.SMonad Spec.Vec Spec.Power.
Import Category.
Import ContPL.
Import ContPLProps.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Vec.
Import Lift.
Import Power.
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
  Context `{sumprops : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc) (sts:=sts)(sos:=sumops)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{Streamprops : StreamProps (U:= U)(ccat:=ccat) (Stream:=Stream)(cmc:=cmc) (sps:=Streamops)}.
  Context `{mops : MeasOps U
(ccat := ccat) (cmcprops := CMCprops)(lrnnops:=lrnnops)(sumops:=sumops)
  (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts) (Σ:=Σ)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)
                                    (cmcprops := CMCprops) (smd := ProbMonad)}.
  Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete}.
  Context {DProps : (@DiscreteProps U ccat cmc discrete DOps)}.
  Context `{pos : PowOps (U:=U) (ccat:=ccat)(power:=power)}.
  Context `{oos : OpenOps (U:=U)(ccat:=ccat)(Σ:=Σ)(sts:=sts)(Open:=Open)}.
  
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
       (*@unit_uniq _ _ _ _*)
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
  
    Theorem Fubini_Bind : forall {Δ A B C : U} (DA : Δ ~~> Prob A) (DB : Δ ~~> Prob B) (h : Δ * A * B ~~> Prob C),
      (Bind DA (Bind (DB ∘ fst) h)) ==
      (Bind DB (Bind (DA ∘ fst) (h ∘ prod_assoc_left ∘ (id ⊗ swap) ∘ prod_assoc_right))).
  Proof. intros Δ A B C DA DB h.  
         pose proof (Fubini (C := C) DA DB
                            (fun Δ0 e a b => h ∘ ⟨⟨e, a⟩, b⟩)
                            (fun Δ0 e a b => h ∘ ⟨⟨e, a⟩, b⟩)) as given.
         simpl in given.
         unfold makeFun1E in given.
         unfold Lift, extend, Extend_Prod, Extend_Refl in given.
         assert ( Bind DA (Bind (DB ∘ (id ∘ fst)) (h ∘ ⟨ ⟨ id ∘ fst ∘ (id ∘ fst), snd ∘ (id ∘ fst) ⟩, snd ⟩)) ==
          Bind DB (Bind (DA ∘ (id ∘ fst)) (h ∘ ⟨ ⟨ id ∘ fst ∘ (id ∘ fst), snd ⟩, snd ∘ (id ∘ fst) ⟩)))
           as given'.
         { eapply given. reflexivity. }
         autorewrite with cat_db in given'.
         rewrite <- pair_f in given'.
         repeat (rewrite pair_id in given'; autorewrite with cat_db in given').
         unfold prod_assoc_right, prod_assoc_left, swap, parallel.
         autorewrite with cat_db.
         rewrite given'.
         repeat (apply Bind_Proper; try reflexivity).
         remove_eq_left.
         apply proj_eq.
         - rewrite compose_assoc.
           autorewrite with cat_db. rewrite pair_f.
           rewrite !compose_assoc. autorewrite with cat_db.
           rewrite <- (compose_assoc _ snd).
           autorewrite with cat_db.
           rewrite !compose_assoc.
           autorewrite with cat_db.
           rewrite <- compose_assoc.
           autorewrite with cat_db. reflexivity.
         - rewrite compose_assoc. autorewrite with cat_db.
           rewrite pair_f. autorewrite with cat_db.
           rewrite <- compose_assoc. autorewrite with cat_db.
           rewrite !pair_f. autorewrite with cat_db.
           rewrite <- compose_assoc. autorewrite with cat_db.
           reflexivity.
  Qed.

  Theorem indep_integral_right : forall {Δ A B C : U}
                                   (DA : Δ ~~> Prob A) (DB : Δ  ~~> Prob B) (DC : Δ * A ~~> Prob C),
      Bind DA (indep (DB ∘ fst) DC) == indep DB (Bind DA DC).
  Proof. intros Δ A B C DA DB DC.
         unfold indep. unfold makeFun1E.
         simpl_ext. autorewrite with cat_db.
         rewrite (Bind_ext _ _ _ _ fst).
         rewrite Bind_Bind.
         rewrite Fubini_Bind.
         repeat (apply Bind_Proper; try reflexivity).
         rewrite !Bind_ext.
         apply Bind_Proper.
         - remove_eq_left.
           unfold prod_assoc_left. rewrite compose_assoc.
           rewrite pair_fst.
           unfold prod_assoc_right. rewrite !parallel_pair.
           autorewrite with cat_db.
           unfold swap. rewrite pair_f.
           autorewrite with cat_db.
           apply proj_eq; autorewrite with cat_db; reflexivity.
         - unfold Ret; remove_eq_left.
           apply proj_eq.
           + rewrite !compose_assoc. autorewrite with cat_db.
             rewrite <- !(compose_assoc _ _ snd).
             rewrite !parallel_fst.
             unfold prod_assoc_left.
             rewrite !compose_assoc; autorewrite with cat_db.
             unfold swap, prod_assoc_right.
             rewrite <- !compose_assoc.
             rewrite (compose_assoc _ _ fst).
             rewrite parallel_fst.
             rewrite <- compose_assoc.
             rewrite parallel_fst.
             rewrite pair_f. rewrite parallel_pair.
             autorewrite with cat_db.
             rewrite pair_f.
             rewrite !compose_assoc.
             autorewrite with cat_db.
             reflexivity.
           + rewrite !compose_assoc; autorewrite with cat_db.
             reflexivity.
  Qed.

  
  Theorem swap_indep : forall {Γ A B : U} (DA : Γ ~~> Prob A) (DB : Γ ~~> Prob B),
      (map swap) ∘ (indep DA DB) == (indep DB DA).
  Proof. intros Γ A B DA DB.
         unfold indep. rewrite Fubini_pair at 1.
         rewrite map_Bind. apply Bind_Proper; try reflexivity.
         rewrite lam_postcompose; apply lam_extensional; intros.
         rewrite map_Bind. apply Bind_Proper; try reflexivity.
         rewrite lam_postcompose; apply lam_extensional. intros.
         rewrite map_Ret. apply Ret_Proper. unfold swap.
         rewrite pair_f; autorewrite with cat_db.
         reflexivity.
  Qed.




  Section Constant.
  
  Definition const_sampler_prog {Δ A S : U} (x : Δ ~~> A) : Δ * S ~~> S * A :=
    'LAM'<< _ | _ >> s => ⟨s, !x⟩.
         
  
  Theorem const_sampler : forall {Δ A S : U} (D : Δ ~~> Prob S) (x : Δ ~~> A),
      Sampler (Δ := Δ) (A := A) (S := S) D (Ret x).
  Proof. intros Δ A S D x.
         refine (sampler (const_sampler_prog x) _).       
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
  Defined.

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
         - apply unit_uniq.
         - unfold makeFun1E, Lift, Extend_Prod, Extend_Refl, extend.
           remove_eq_left.
           autorewrite with cat_db.
           reflexivity.
  Qed.

  Theorem constant_stream_Proper : forall {Γ A}, Proper (eq ==> eq) (constant_stream (Γ:=Γ)(A:=A)).
  Proof. intros Γ A. unfold Proper, respectful. intros x y H.
         unfold constant_stream.
         apply pstream_Proper; try reflexivity.
         apply lam_extensional; intros.
         apply compose_Proper; try reflexivity.
         unfold Lift; apply compose_Proper; try assumption; try reflexivity.
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

  Existing Instance constant_stream_Proper.

  Lemma Bind_m_fst : forall {Γ A B} {m : Γ ~~> Prob A} {f : Γ ~~> Prob B},
      Bind m (f ∘ fst) == f.
  Proof. intros Γ A B m f.
         unfold Bind, bind.
         rewrite map_compose.
         rewrite <- !compose_assoc.
         rewrite (compose_assoc _ strong).
         rewrite fst_strong.
         rewrite <- compose_assoc.
         rewrite -> pair_fst, -> compose_id_right, <- ret_nat,
         -> compose_assoc, -> join_ret, -> compose_id_left.
         reflexivity.
  Qed.                                                      
  
  Lemma tail_constant_stream : forall {Γ A} (f : Γ ~~> Prob A),
      (map (M:=Prob) tl) ∘ (constant_stream f) == (constant_stream f).
  Proof. intros Γ A f.
         rewrite -> constant_unfold at 1; unfold constant_unfold_prog.
         rewrite map_Bind', lam_postcompose.
         setoid_rewrite map_Bind'.
         setoid_rewrite lam_postcompose.
         setoid_rewrite map_Ret.
         setoid_rewrite cons_tl'.
         rewrite Bind_m_Ret.
         rewrite emap_snd. unfold Lift, extend, Extend_Prod, Extend_Refl.
         rewrite compose_id_left. rewrite constant_stream_ext1.
         rewrite Bind_m_fst. reflexivity.
  Qed.
         
  
  Existing Instance Streamprops.

  Definition infinite_sampler_prog {Δ A : U} : Δ * (Stream A) ~~> (Stream A) * A.
  Proof. eapply ('LAM'<< Δ' | e >> aa => ⟨tl, hd⟩ ∘ aa). (* Show Proof. *)
  Defined.

  
  Theorem infinite_sampler : forall {Δ A : U} (D : Δ ~~> Prob A),
      Sampler (Δ := Δ)(S := Stream A)(A :=A) (constant_stream D) D.
  Proof. intros Δ A D.
         refine (sampler infinite_sampler_prog _).
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
  Defined.
  
  Section Coinflip.
    
  Definition Boole := unit + unit.
  Definition Cantor := Stream Boole.
  
  Definition infinite_coinflips : unit ~~> Prob Cantor := 
    constant_stream coinflip.
  
  Definition coinflip_sampler :
    Sampler (Δ := unit) (S := Cantor) (A := Boole) infinite_coinflips coinflip :=
    infinite_sampler _.

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
  
  Theorem pullback_sampler : forall {Δ Δ' S A : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (ext : Extend Δ Δ'),
      (Sampler (Δ := Δ) DS DA) -> (Sampler (Δ := Δ') (DS ∘ ext) (DA ∘ ext)).
  Proof. intros Δ Δ' S A DS DA ext.
         intros [SA samples]. refine (sampler (SA ∘ (ext ⊗ id)) _).
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
  Defined.

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
         
      
  
  Theorem bind_sampler : forall {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B)
                           (SA : Sampler DS DA) (SB : Sampler (Δ := Δ * A) (DS ∘ fst) DB),
      Sampler DS (bind_distr_prog DA DB).
  Proof. intros Δ A B S DS DA DB.
         intros [SA samplesA] [SB samplesB].
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
  Defined.
  
  (* Program transforms. 
         rewrite Map_prog.
         unfold indep, bind_distr_prog, bind_sampler_prog.
         unfold indep in samplesB. rewrite Map_prog in samplesB.
         unfold indep in samplesA. rewrite Map_prog in samplesA.
         unfold Lift at 1. *)
  
  End Bind.

  Section Unzip.

    Fixpoint indeps {Γ A} (n : nat) (f : Γ ~~> Prob A) : Γ ~~> Prob (Vec n A) :=
      match n with
      | O => Ret (tt)
      | (S m) => indep f (indeps m f)
      end.

    Definition constant_prefix_stmnt : forall {Γ A} {n : nat} {f : Γ ~~> Prob A}, Prop.
    Proof. intros Γ A n f. refine (_ == _).
           refine (_ ∘ _).
           refine (map (prefix n)). Focus 2.
           refine (constant_stream f). refine (indeps n f). 
    Defined.

    Theorem constant_prefix : forall {Γ A} {n : nat} {f : Γ ~~> Prob A}, @constant_prefix_stmnt Γ A n f.
    Proof.
      intros Γ A n f.
      unfold constant_prefix_stmnt.
      induction n.
      - (* 0 *)
        simpl.
        apply (Iso_Mono Prob_unit_Iso).
        simpl. apply unit_uniq.
      - (* S _ *)
        simpl.
        rewrite <- IHn.
        unfold indep.
        rewrite constant_unfold.
        unfold constant_unfold_prog.
        rewrite map_Bind'; rewrite lam_postcompose.
        apply Bind_Proper; try reflexivity.
        apply lam_extensional; intros Γ' ext a.
        simpl_ext.
        rewrite map_Bind'; rewrite lam_postcompose.
        rewrite <- !compose_assoc. rewrite Bind_map_f.
        apply Bind_Proper. apply constant_stream_ext1.
        rewrite lam_eval_par. apply lam_extensional; intros Γ'' ext' s.
        rewrite map_Ret. apply Ret_Proper.
        apply proj_eq.
        rewrite compose_assoc. rewrite !pair_fst.
        rewrite cons_hd. reflexivity.
        rewrite compose_assoc. rewrite !pair_snd.
        remove_eq_left. rewrite cons_tl'.
        reflexivity.
    Qed.
    
    Theorem constant_unzip : forall {Γ A} (f : Γ ~~> Prob A),
      (map (unzip (sps:=Streamops)(A:=A)) ∘ (constant_stream f)) ==
      indep (constant_stream f) (constant_stream f).
    Proof. intros.
           apply (Iso_Mono (Iso_Sym (M_iso (Stream_Prod (A:=A)(B:=A))))).
           simpl.
           apply Prob_Stream_eq.
           intros n.
           rewrite !compose_assoc.
           rewrite <- !map_compose.
           rewrite squeeze_vsqueeze. rewrite <- compose_assoc. rewrite unzip_vnzip.
           rewrite !map_compose.
           rewrite <- !compose_assoc.
           rewrite parallel_indep.
           rewrite !constant_prefix.
           remove_eq_left.

           (* map vnzip ∘ indeps (n * 2) f == indep (indeps n f) (indeps n f) *)

           induction n.

           - (* 0 *)
             simpl. unfold indep.
             rewrite Bind_Ret_f. rewrite lam_eval. simpl_ext.
             rewrite Bind_Ret_f. rewrite lam_eval. rewrite map_Ret.
             apply Ret_Proper. apply proj_eq; apply unit_uniq.
           - (* S _ *) 
             simpl indeps.
             rewrite (indep_assoc f (indeps n f)).
             rewrite <- (swap_indep (indep f (indeps n f))).
             rewrite <- parallel_indep_right.
             rewrite indep_assoc.
             rewrite <- (swap_indep (indeps n f)). (* This appears useless, but it is necessary for the deterministic transformations to line up exactly. *)
             rewrite <- !parallel_indep_right.
             rewrite <- IHn.
             rewrite <- !parallel_indep_right.
             remove_eq_right.
             (* This now looks horrible, but it's all deterministic! *)
             rewrite <- !map_compose.
             apply map_Proper.
             simpl. unfold prod_assoc_left, swap.
             (* apply proj_eq. *)
             rewrite !pair_f, !parallel_compose.
             autorewrite with cat_db.
             rewrite <- !compose_assoc.
             rewrite !parallel_compose.
             autorewrite with cat_db.
             rewrite !pair_f.
             autorewrite with cat_db.
             unfold parallel.
             rewrite !pair_f.
             autorewrite with cat_db.
             rewrite <- !compose_assoc.
             rewrite !pair_f.
             autorewrite with cat_db.
             rewrite !compose_assoc.
             reflexivity.
    Qed.

    Theorem unzip_sampler : forall {Γ A : U} (f : Γ ~~> Prob A),
        Sampler (Δ := Γ) (S:=Stream A) (A:=Stream A) (constant_stream f) (constant_stream f).
    Proof. intros Γ A f.
           refine (sampler (unzip ∘ snd) _).
           unfold Map.
           rewrite emap_snd_pair.
           symmetry.
           apply constant_unzip.
    Defined.           
                     
  End Unzip.

  Section Geometric.

    Import Qnn.
    Import Lift.
    Variable L : U -> U.
    Context `{los : LiftOps (U:=U) (ccat:=ccat)(Stream:=Stream)(cmc:=cmc)(sts:=sts)(Σ:=Σ)(Lift:=L)}.

    Notation "| A |" := (unit ~~> A) (at level 90).

    Fixpoint Qnnpow (q : Qnn) (n : nat) : Qnn :=
       (match n with
        | O => 1
        | (S m) => (q * (Qnnpow q m))
        end)%Qnn.

    Notation "A ^ B" := (Qnnpow A B) : qnn_scope.

    Definition Geo_spec : |Prob (discrete nat)| -> Prop.
    Proof. intros P. assert (discrete nat ~~> LRnn) as f.
           {
             apply discrete_func'.  
             intros n. apply (Qnn_to_LRnn (Σ:=Σ)). exact lrnnops.
             exact (Qnnonehalf ^ n)%Qnn.
           }
           refine (_ == f).
           apply dfs_to.
           refine (Prob_discrete ∘ _).
           exact P.
    Defined.

    
    Notation "'dλ' x => f" := (discrete_func' (fun x => f)) (at level 93).
    Notation "∙ A" := (discrete_pt A) (at level 9).
    
    Definition diverge_if_zero_else_pred {Γ} : Γ ~~> (discrete nat) -> Γ ~~> (L (discrete nat)).
    Proof. intros n. eapply (recursion (Γ := Γ) (A := discrete nat) (X := discrete nat)).
           - (* Initial state. *) exact n.
           - (* Step. 
Use `throw' to have a final answer or `recall' to call this function on another argument. *)
             refine (dλ m => _).
             refine (match m with
                     | O => recall ∙O
                     | (S k) => throw ∙k
                     end).
             Show Proof.
    Defined.

    Notation "'Match' A 'Left' B 'Right' C" := (copair B C ∘ A) (at level 80).

    Definition geom : unit ~~> (Prob (L ( discrete nat))).
    Proof. eapply (precursion (Γ := unit) (A := discrete nat) (X := discrete nat)).
           - (* initial state *) exact (∙0).
           - refine (_ ∘ snd). refine (dλ m => _).
             refine (x <- coinflip; _).
             apply (
                 Match x Left (Ret (throw ∙m)) Right (Ret (recall ∙(S m)))      
               ).
             Show Proof.
    Defined.

    
  End Geometric.
  
End Samplers.
