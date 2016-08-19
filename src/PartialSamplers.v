Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Samplers.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Language.ContPL Language.ContPLProps.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream
        Spec.SMonad Spec.Vec Spec.Power Fix Sums Spec.Sup Spec.Pullback Spec.OEmbedding.
Require Import Coq.setoid_ring.Ring_theory.
Import Category.
Import ContPL.
Import ContPLProps.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Fix Sums.
Import Sup.
Import Vec.
Import Lift.
Import Power.
Import OEmbedding.
Import Stream.
Import CCC.
Import Discrete.
Import Presheaf.
Import Pullback.
Local Open Scope morph.
Local Open Scope obj.

Section PartialSamplers.
  
  Context {U : Type}.
  Context `{sigmaops : ΣOps (U := U)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) (Σ := Σ) U}.
  Context `{lrnnps : LRnnProps (U:=U)(ccat:=ccat)(cmc:=cmc)(Σ:=Σ) (LRnn:=LRnn)(H1:=lrnnops)}.
  Context `{sos : SumOps (U:=U) (ccat := ccat)}.
  Context `{sumprops : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc) (sts:=sts)(sos:=sos)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{Streamprops : StreamProps (U:= U)(ccat:=ccat) (Stream:=Stream)(cmc:=cmc) (sps:=Streamops)}.
  Context `{mops : MeasOps U (ccat := ccat) (cmcprops := CMCprops)(sumops:=sos)(sumprops:=sumprops)
           (lrnnops:=lrnnops) (Σ:=Σ)  (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{PMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc)
                                    (cmcprops := CMCprops) (smd := ProbMonad)}.
  Context `{MMDprops : SMonad_Props (U := U) (M := Meas) (ccat := ccat) (cmc := cmc)
                                    (cmcprops := CMCprops) (smd := MeasMonad)}.
  Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete}.
  Context {DProps : (@DiscreteProps U ccat cmc discrete DOps)}.
  Context `{pos : PowOps (U:=U) (ccat:=ccat)(power:=power)}.
  Variable L : U -> U. 
  Context `{los : LiftOps (U:=U)(Σ:=Σ)(ccat:=ccat)(Stream:=Stream)(cmc:=cmc)(sts:=sts)(Lift:=L)}.
  Context {lps : LiftProps}.
  Context {Σps : ΣProps}.
  
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


  Section Lift_Prob.


    Definition unlift {A : U} : Meas (L A) ~~> Meas A.
    Proof. apply
             (Meas_Embed _ (strict_open_embedding)).
    Defined.

    Existing Instance MeasMonad.
    
    Lemma unlift_strict : forall {A}, unlift ∘ (map (M:=Meas)strict) == id (A:=Meas A).
    Proof. intros A. unfold unlift. apply Embed_map.
    Qed.
    
    Lemma unlift_bot : forall {A : U}, unlift ∘ (map (M:=Meas) bottom) == zero(A:=A).
    Proof.
      intros A. unfold unlift. etransitivity.
      apply (Embed_nat False_elim bottom False_elim (strict(A:=A))
                       zero_open_embedding strict_open_embedding).
      
      unfold Pullback. split. split.
      - apply False_elim_unique.
        
      - unfold Mono; intros.
        apply (Embedding_Mono (zero_open_embedding(A:=unit))).
        apply unit_uniq.
        
      - intros X j k stricteqbot. (* This is a kind of "inequality of distinct constructors" for Lift. *)
        exfalso.
        apply (apart _ _ stricteqbot).
        
      -  assert (forall {X}, map (M:=Meas) False_elim == zero(A:=X)). {
           intros X. rewrite <- (zero_scale (f:=(map False_elim))).
           rewrite (unit_uniq tt (tt ∘ (map(B:=X) False_elim))).
           rewrite -> compose_assoc.
           rewrite <- (compose_id_left (map False_elim)) at 3.
           rewrite <- pair_f.
           rewrite !compose_assoc.
           pose (map_scale (B:=X) (r:=Real.Real.LRnnzero _)(f:=False_elim)).
           etransitivity; symmetry; etransitivity. apply e.
           rewrite <- (compose_id_right (map False_elim)) at 2.
           remove_eq_left.
           rewrite <- compose_id_left.
           rewrite <- (from_to Meas_false) at 1.
           rewrite <- (from_to Meas_false) at 2.
           rewrite <- !compose_assoc.
           apply compose_Proper; try reflexivity.
           apply unit_uniq.
           reflexivity.
           remove_eq_right. remove_eq_left.
           unfold add_unit_left. rewrite parallel_pair, compose_id_left. reflexivity.
         }
         rewrite H. rewrite zero_ext. reflexivity.
    Qed.
    
    
  End Lift_Prob.
  
  
  Record PartialSampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    par_sampler
      {
        sample : Δ * S ~~> L (S * A);
        sampling_cond :  Prob_to_Meas ∘ indep DS DA == 
          unlift ∘ Prob_to_Meas ∘ (Map sample DS)  
      }.

  Arguments par_sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.
  
  Existing Instance MeasMonad.
    
  Let Cantor := Samplers.Cantor (Stream:=Stream).
  Let sleq {A B} := sleq (A:=A) (B:=B) (Σ:=Σ).

  Hint Unfold Cantor Samplers.Cantor Boole.
  
  Definition Zero {Γ} : Γ ~~> Boole := inl ∘ tt.
  Definition One {Γ} : Γ ~~> Boole := inr ∘ tt.

  Lemma Zero_ext : forall {Γ Γ'} (f : Γ ~~> Γ'), Zero ∘ f == Zero.
  Proof. intros Γ Γ' f.
         unfold Zero; remove_eq_left. apply unit_uniq.
  Qed.
  
  Lemma One_ext : forall {Γ Γ'} (f : Γ ~~> Γ'), One ∘ f == One.
  Proof. intros Γ Γ' f.
         unfold One; remove_eq_left. apply unit_uniq.
  Qed.
  
  Definition F : Cantor ~~> L (Cantor * Boole) ->
                 Cantor ~~> L (Cantor * Boole).
  Proof. intros f.
         refine (_ ∘ ⟨tl, hd⟩).         
         eapply sum_elim.
         - refine (strict ∘ _ ∘ fst). (* respond *)
           exact ⟨id, Zero⟩.
         - exact  (f ∘ fst). (* recurse *)
  Defined.

  Existing Instance sleq_Proper.
  
  Lemma F_Proper : Proper (sleq ==> sleq) F.
  Proof.
    unfold Proper, respectful.
    intros x y H.
    unfold F.
    repeat (apply compose_sleq; try apply sleq_reflexive).
    apply sum_sleq.
    - rewrite !sum_elim_inl. apply sleq_reflexive.
    - rewrite !sum_elim_inr. repeat apply compose_sleq; try apply sleq_reflexive; try assumption.
  Qed.

  Definition fixF : Cantor ~~> L (Cantor * Boole).
  Proof. eapply (sfix F). apply (ishas bottom_min). eapply F_Proper.
  Defined.

  Definition H : (Cantor ~~> L (Cantor * Boole)) -> (unit ~~> Meas (Cantor * Boole)).
  Proof. intros f. refine (unlift ∘ Prob_to_Meas ∘ _). refine (map f ∘ infinite_coinflips).
  Defined.

  Lemma H_Proper : Proper (sleq ==> sleq) H.
  Proof.
    unfold Proper, respectful.
    intros f g fg.
    unfold H. repeat (apply compose_sleq; try apply sleq_reflexive).
    apply (map_sleq (M0:=Prob) f g fg).
  Qed.

  Lemma Hbot : H (bottom ∘ tt) == zero.
  Proof. unfold H. unfold Map, emap.
         rewrite map_compose.
         assert (forall {Q}, map (A:=Q)(M:=Prob) tt == Ret id ∘ tt). {
           intros Q. rewrite <- compose_id_left at 1.
           rewrite unit_Prob. unfold Ret. remove_eq_left.
           rewrite unit_uniq. rewrite compose_id_left. reflexivity.
         }
         rewrite H0. rewrite <- !compose_assoc.
         rewrite (unit_uniq (tt ∘ _) tt).
         rewrite (compose_assoc _ (map _) _).
         rewrite <- Prob_Meas_map.
         rewrite !compose_assoc.
         rewrite unlift_bot. rewrite !zero_ext. reflexivity.
  Qed.


  Lemma HCont : Cont H H_Proper.
  Proof. unfold Cont. intros.
         unfold H at 1.
         rewrite map_Cont. unfold Cantor, Samplers.Cantor, Boole.
         pose (fun c => precompose_Cont (Σ:=Σ)(C:=c) infinite_coinflips) as p.
         unfold Cantor, Samplers.Cantor, Boole in p.
         rewrite p.
         rewrite !postcompose_Cont.
         apply sup_exacteq_sup.
         reflexivity.
  Qed.

  Definition G : (unit ~~> Meas (Cantor * Boole)) -> (unit ~~> Meas (Cantor * Boole)).
  Proof. intros f.
         refine (Meas_add ∘ ⟨_, _⟩).
         - refine (Meas_scale ∘ ⟨_, _⟩).
           + exact (LRnnonehalf _).
           + refine (indep _ _). refine (map _ ∘ _).
             * unfold Cantor, Samplers.Cantor. apply tl.
             * apply (Prob_to_Meas ∘ infinite_coinflips).
             * apply (Ret Zero).
         - refine (Meas_scale ∘ ⟨_, _⟩).
           + exact (LRnnonehalf _).
           + apply f.
  Defined.

  Lemma G_Proper : Proper (sleq ==> sleq) G.
  Proof. unfold Proper, respectful.
         intros f g fg.
         unfold G.
         repeat (try apply compose_sleq; try apply pair_sleq; try apply sleq_reflexive; try assumption).
  Qed.

  Notation "A + B" := (Meas_add ∘ ⟨A, B⟩).
  Notation "A ⨰ B" := (Meas_scale ∘ ⟨A, B⟩) (at level 40).
  Arguments LRnnonehalf {U} {ccat} {cmc} {Σ} {LRnn} {H1}.

  Definition sc : forall {A}, (unit ~~> LRnn) -> Meas A ~~> Meas A :=
    fun A r => (Meas_scale ∘ (r ⊗ id) ∘ add_unit_left).

  Lemma scale_sc : forall {A B} (r : unit ~~> LRnn) (f : A ~~> Meas B),
      (r ∘ tt) ⨰ f == (sc r) ∘ f.
  Proof. intros A B r f.
         unfold sc, add_unit_left. remove_eq_left.
         rewrite pair_f, parallel_pair.
         rewrite (unit_uniq (tt ∘ _) tt), !compose_id_left.
         reflexivity.
  Qed.
         
  Lemma Cantor_Iso : Sum.sum Cantor Cantor ≅ Cantor.
  Proof.
    unfold Cantor, Samplers.Cantor, Boole.
    refine (Iso_Trans (Iso_Sum _ _) (Iso_Trans (Iso_Trans _ _) _)).
    apply (Iso_Sym (unit_isom_right)). apply (Iso_Sym (unit_isom_right)).
    apply (Iso_Sym (distrib_Iso_left)).
    apply Iso_Prod_Symm.  apply (Iso_Sym Stream_Iso).
  Defined.
  
  Lemma to_Cantor : (to Cantor_Iso) == cons snd fst ∘ undistrib_left ∘ coparallel ⟨ id, tt ⟩ ⟨ id, tt ⟩.
  Proof.
    simpl. remove_eq_right. rewrite cons_ext. unfold swap. apply cons_Proper; rewrite ?pair_fst, ?pair_snd;
    reflexivity.
  Qed.

  Lemma from_Cantor : (from Cantor_Iso) == coparallel fst fst ∘ (distrib_left ∘ ⟨ tl, hd ⟩).
  Proof.
    simpl. remove_eq_left. unfold swap. rewrite pair_f, pair_fst, pair_snd.
    reflexivity.
  Qed.

  Existing Instance coparallel_Proper.
  Existing Instance copair_Proper.

  Arguments Meas_Embed {U} {ccat} {cmc} {cmcprops} {Σ} {Σos} {LRnn} {lrnnops}
            {R} {sts} {sumops} {sumprops} {Stream} {power} {Open} {Meas} {Prob}
            {SubProb} {discrete} {MeasOps} {A} {B} f {_}.
(*  Arguments embedding_Proper {U} {ccat} {Embedding} {A} {B} {f} {_} {_} {_}.*)

             
  Lemma inverse : (Cantor ~~> (pb (B:=Cantor)(strict ∘ ⟨id, Zero⟩) strict)).
  Proof.
    unshelve eapply pb_Exists.
    exact id. exact ⟨id, Zero⟩. rewrite compose_id_right; reflexivity.
  Defined.

  Lemma inverse_iso : Cantor ≅ pb (B:=Cantor) (strict ∘ ⟨id, Zero⟩) strict.
  Proof. unshelve eapply Build_Iso.
         apply inverse. apply pb_fst.
         - apply pb_Uniq. rewrite !pair_f.
           rewrite !compose_assoc. unfold inverse; rewrite !pb_Exists_left, !pb_Exists_right.
           apply pair_Proper.
           + rewrite compose_id_left, compose_id_right. reflexivity.
           + apply strict_mono. rewrite !compose_assoc. rewrite pb_Comm.
             rewrite compose_id_right. reflexivity.
         - unfold inverse; rewrite pb_Exists_left. reflexivity.
  Defined.

  Lemma Cantor_Pullback : Pullback (id(A:=Cantor)) (strict ∘ ⟨id, Zero⟩) ⟨id, Zero⟩ strict.
  Proof. split; try split; try unshelve eexists.
         - rewrite compose_id_right. reflexivity.
         - unfold Mono; intros. assert (fst ∘ ⟨id, ⟨id, Zero⟩⟩ == id(A:=Cantor)) by apply pair_fst.
           rewrite <- (compose_id_left g1), <- (compose_id_left g2).
           rewrite <- H1. rewrite <- !compose_assoc. rewrite H0. reflexivity.
         - apply j.
         - split.
           + apply compose_id_left.
           + apply strict_mono. rewrite compose_assoc. assumption.
  Defined.

  Existing Instance MEv_Proper.

  Lemma Bind_unit : forall {Γ A} (h : Γ ~~> Meas unit) (f : Γ * unit ~~> Meas A),
      Bind h f == Meas_scale ∘ ⟨(to Meas_unit) ∘ h, f ∘ add_unit_right⟩.
  Proof. admit. (* Not sure if this follows from something simpler. Alternatively, could become the 
 definition of Meas_scale. *)
  Admitted.
           
  Theorem HF_GH : forall f, H (F f) == G (H f).
  Proof. intros.     
         unfold G, H, Cantor.
         rewrite <- (compose_assoc _ _ unlift).
         rewrite (compose_assoc infinite_coinflips _ Prob_to_Meas).
         rewrite <- Prob_Meas_map. rewrite !compose_assoc.
         pose (Cantor_Pullback) as P0.
         pose (pb_is_Pullback f strict) as P1.
         pose (Pullback_sum P0 P1) as P''.
         pose (Pullback_B_Iso Cantor_Iso P'') as P'.
         assert (Pullback (to Cantor_Iso ∘ coparallel id (pb_fst f strict))
                          (sum_elim (strict ∘ ⟨ id, Zero ⟩ ∘ fst) (f ∘ fst) ∘ ⟨ tl, hd ⟩)
                          (copair ⟨ id, Zero ⟩ (pb_snd f strict))
                          strict)
           as P.
         {
           unshelve eapply (Pullback_Proper _ _ _ _ P').
           - (*rewrite to_Cantor. unfold Cantor, Samplers.Cantor, Boole.
             remove_eq_left.
             rewrite -> coparallel_compose.
             rewrite !pair_f.
             unfold undistrib_left.
             rewrite <- copair_coparallel. rewrite -> !parallel_pair.
             rewrite !compose_id_left. rewrite !compose_id_right. rewrite (unit_uniq (tt ∘ _) tt). *)
             reflexivity.
           - rewrite from_Cantor. unfold Cantor, Samplers.Cantor, Boole.
             remove_eq_right.
             unfold distrib_left. 
             rewrite <- copair_coparallel.
             rewrite copair_distrib_elim.
             reflexivity.
           - reflexivity.
           - reflexivity.
         }
         clear P'. clear P''.
         assert (OpenEmbedding (Σ:=Σ)(pb_fst f strict)) as Q0. { admit. }
         assert (OpenEmbedding (Σ:=Σ)
          ((to Cantor_Iso) ∘ coparallel id (pb_fst f strict))) as Q1.
         {
           apply compose_open_embedding. apply coparallel_open_embedding.
           apply id_open_embedding. apply Q0. apply Iso_OpenEmbedding.
         }
         pose (Embed_nat _ _ _ _ Q0 strict_open_embedding P1) as C0.
         pose (Embed_nat _ _ _ _ Q1 strict_open_embedding P) as C1.
         unfold Cantor, Samplers.Cantor, Boole in C1. unfold unlift at 1.
         unfold F, Cantor, Samplers.Cantor, Boole. rewrite C1.
         rewrite copair_add.
         rewrite <- !compose_assoc, -> !pair_f. (* Distribute the addition. *)
         apply compose_Proper. reflexivity.
         apply pair_Proper. (* Says: We'll prove corresponding summands are equal. *)
         - rewrite <- !compose_assoc.
           etransitivity. { apply compose_Proper.
           - reflexivity.
           - unfold Cantor, Samplers.Cantor, Boole.
             rewrite !compose_assoc. rewrite Embed_compose.
             rewrite <- !compose_assoc. 
             apply compose_Proper. unshelve eapply Meas_Embed_Proper0. Focus 2.
             rewrite <- compose_assoc, -> coparallel_inl.
             rewrite compose_id_right. rewrite to_Cantor.
             rewrite <- !compose_assoc, -> coparallel_inl.
             unfold undistrib_left. rewrite (compose_assoc _ inl).
             rewrite copair_inl. rewrite <- pair_parallel_id.
             rewrite cons_ext. apply cons_Proper.
             apply pair_snd. apply pair_fst. reflexivity.
                          } (*rewrite Embed_irrel.*)
             etransitivity. apply compose_Proper. reflexivity.
           apply compose_Proper.
           unshelve eapply Meas_Embed_Proper1. apply Cons_Zero_OpenEmbedding. apply dir_img_unique.
           reflexivity.
           (* probably get rid of `map tl` and `Ret Zero` / `map ⟨id, Zero⟩` right here *)
           apply MEv_determines.
           admit.
         - rewrite <- !compose_assoc.
           etransitivity. { apply compose_Proper.
           - reflexivity.
           - unfold Cantor, Samplers.Cantor, Boole.
             rewrite !compose_assoc. rewrite Embed_compose.
             rewrite <- !compose_assoc. apply compose_Proper.
             + unshelve eapply (Meas_Embed_Proper0 _ _ (compose_open_embedding inr_open_embedding Q1)).
               Focus 2.
               rewrite <- compose_assoc. rewrite coparallel_inr.
               rewrite to_Cantor. rewrite compose_assoc. apply compose_Proper.
               unfold Cantor, Samplers.Cantor, Boole.
               rewrite <- !compose_assoc, -> coparallel_inr.
               unfold undistrib_left. rewrite (compose_assoc _ inr).
               rewrite copair_inr. rewrite <- pair_parallel_id.               
               rewrite cons_ext. apply cons_Proper. apply pair_snd. apply pair_fst.
             + reflexivity.
             + reflexivity. }
                          etransitivity. apply compose_Proper. reflexivity.
           apply compose_Proper.
           unshelve eapply Meas_Embed_Proper1.
           apply compose_open_embedding. apply Q0. apply Cons_One_OpenEmbedding.
           apply dir_img_unique. reflexivity.
           unfold unlift, Cantor, Samplers.Cantor, Boole.
           rewrite (compose_assoc _ _ Prob_to_Meas).
           rewrite <- Prob_Meas_map. 
           rewrite !(compose_assoc _ _ (Meas_Embed strict _)).
           unfold Cantor, Samplers.Cantor, Boole in C0. rewrite C0.

           rewrite <- (compose_id_right LRnnonehalf).
           rewrite (unit_uniq id tt).
           rewrite scale_sc.

           unfold Cantor, Samplers.Cantor, Boole.
           rewrite !(compose_assoc _ _ (sc _)). unfold sc; rewrite map_scale.
           symmetry; etransitivity. apply compose_Proper. apply compose_Proper.
           rewrite <- compose_assoc. apply compose_Proper. reflexivity.
           rewrite Embed_scale. reflexivity. reflexivity. reflexivity.
           
           rewrite <- Embed_compose. remove_eq_left. unfold Cantor, Samplers.Cantor, Boole.
           rewrite !compose_assoc.
           pose (compose_assoc infinite_coinflips Prob_to_Meas
                               (Meas_scale ∘ LRnnonehalf ⊗ id ∘ add_unit_left)) as temp;
             unfold Cantor, Samplers.Cantor, Boole in temp; rewrite <- temp; clear temp.
           rewrite <- (compose_assoc _ _ (Meas_Embed _ _)).
           apply MEv_determines. intros V.
           rewrite MEv_scale. rewrite MEv_embed. unfold dir_img, open_map, Cons_One_OpenEmbedding.
           unfold infinite_coinflips at 2. rewrite constant_unfold. unfold constant_unfold_prog.
           rewrite Prob_Meas_Bind; rewrite lam_postcompose.
           unfold Boole.
           rewrite MEv_Bind_coprod.
           (* Now we want to tackle the subexpressions on their own. *)
           symmetry; etransitivity.
           apply compose_Proper. reflexivity. apply pair_Proper.
           assert (Meas_Embed inl inl_open_embedding ∘ (Prob_to_Meas ∘ coinflip) ==
                   (from Meas_unit ∘ LRnnonehalf)) as C. { admit. } (* Definition of coinflip? *)
           rewrite C. rewrite Bind_unit. rewrite !compose_assoc.
           rewrite (to_from Meas_unit), compose_id_left. unfold makeFun1E at 1.
           rewrite MEv_scale'. apply compose_Proper. reflexivity. apply pair_Proper. reflexivity.
           rewrite <- (compose_assoc _ _ Prob_to_Meas). rewrite Bind'_ext.
           rewrite <- (compose_assoc _ _ Prob_to_Meas). rewrite Bind'_ext.
           rewrite <- !constant_stream_ext1. unfold Lift, extend, Extend_Prod, Extend_Refl.
           rewrite Prob_Meas_Bind. etransitivity.
           apply MEv_Proper. apply Bind_Proper.
           apply compose_Proper. reflexivity.
           apply constant_stream_Proper. rewrite <- !compose_assoc. rewrite (unit_uniq _ id).
           apply compose_id_right. rewrite lam_postcompose. apply lam_extensional; intros.
           etransitivity. rewrite Prob_Meas_Ret. apply Ret_Proper.
           apply cons_Proper. rewrite !compose_assoc. unfold Extend in ext.
           rewrite parallel_snd. unfold add_unit_right. rewrite <- compose_assoc.
           rewrite !pair_f. rewrite <- compose_assoc. rewrite pair_snd.
           apply compose_Proper. reflexivity. apply (unit_uniq _ tt). reflexivity.
           Focus 2. reflexivity. Focus 2.
           
           
           (*unfold MEv at 2.
           rewrite <- (compose_assoc _ (map _)). rewrite (compose_assoc _ Prob_to_Meas).
           rewrite Prob_Meas_map. rewrite <- (compose_assoc _ (map _)).
           unfold infinite_coinflips. unfold Cantor, Samplers.Cantor, Boole.
           symmetry; etransitivity. apply compose_Proper. reflexivity.
           apply compose_Proper. reflexivity. rewrite constant_unfold.
           Unshelve. Focus 3. apply (y <- coinflip;<< Δ | ext >> zs <- constant_stream (! coinflip);<< Δ0 | ext0 >> Ret (sum_elim (false ∘ tt ∘ fst) (V ∘ fst) ∘ ⟨ zs, !y ⟩)).
           
           unfold constant_unfold_prog.
           rewrite map_Bind', lam_postcompose.
           apply Bind_Proper; try reflexivity. apply lam_extensional; intros.
           rewrite map_Bind', lam_postcompose.
           apply Bind_Proper; try reflexivity. apply lam_extensional; intros.
           rewrite map_Ret. apply Ret_Proper. remove_eq_left. rewrite pair_f, cons_hd, cons_tl'.
           reflexivity.
           (* Intuitively the way to prove this is: break it into a linear combination 1/2 p + 1/2 q, one part where y = 0 and one part where y = 1. Then if y = 0 the sum-elim works out to false, and so the weight is 0; if y = 1, the sum-elim works out to the measure of the original subset. *)
           (* Possibly this can be proven without unfolding MEv. *)           *)
           admit.
  Admitted.

  Fixpoint ttm (n : nat) : unit ~~> LRnn :=
    match n with
    | O => LRnnone _
    | (S m) => LRnnmult _ ∘ ⟨LRnnonehalf, (ttm m)⟩
    end. (* ttm for _t_wo _t_o the _m_inus *)
  
  Definition Gsum : (unit ~~> Meas (Cantor * Boole)).
    unshelve eapply sum. intros n.
    unshelve eapply (Meas_scale ∘ ⟨_, _⟩).
    - apply (ttm (S n)).
    - apply indep.
      + unfold Cantor, Samplers.Cantor, Boole.
        unshelve eapply (map tl ∘ Prob_to_Meas ∘ _).
        pose infinite_coinflips as e; unfold Samplers.Cantor, Boole in e; apply e.
      + apply (Ret Zero).
  Defined.
        
  Theorem G_fix_sum : sfix G (ishas zero_min) G_Proper == Gsum.
  Proof.
    unfold Gsum, sum, sfix. apply sup_exacteq_sup. simpl.
    intros n. induction n.
    - (* O *)
      reflexivity.
    - simpl. etransitivity. apply (sleq_Proper_eq_Proper G_Proper). apply IHn. clear IHn.
      unfold G.
      (* Goal: 1/2 (constant thing) + 1/2 Pn == 1/2 * 2^-n * constant thing + Pn. *)
      { induction n. 
      - simpl. (* Basis: 1/2c + 1/2 * 0 == 1/2 * 1 * c + zero. *)
        apply compose_Proper; try reflexivity; try apply pair_Proper.
        + apply compose_Proper; try reflexivity; try apply pair_Proper.
          * (* Goal is 1/2 = 1/2 * 1. Presumably this is doable. *)
            pose (SRmul_comm ((Lrnnsemiring _) unit)) as e.
            unfold ap2 in e. rewrite e. clear e.
            pose (SRmul_1_l ((Lrnnsemiring _) unit)) as e.
            unfold ap2, ap0 in e. rewrite <- (compose_id_right (LRnnone _)).
            rewrite (unit_uniq id tt). rewrite e. clear e.
            reflexivity.
          * rewrite compose_assoc. reflexivity.
        + rewrite scale_zero. reflexivity.
      - (* We know that: 1/2 * c + 1/2 * Pn == 1/2 * 2^-n * c + Pn. *)
        (* We want that: 1/2 * c + 1/2 * P(Sn) == 1/2 * 2^-(Sn) * c + P(Sn) *)
        simpl.
        (* By simplification, this is equivalent to
             1/2 * c + 1/2 * ((1/2 * 2^-n * c) + Pn) == 1/2 * 1/2 * 2^-n * c + 1/2 * 2^-n * c + Pn *)
        rewrite scale_add.
        (* Distribute:  
            1/2 * c + 1/2 * (1/2 * 2^-n * c) + 1/2 * Pn == 1/2 * 1/2 * 2^-n * c + 1/2 * 2^-n * c + Pn *)
        rewrite <- add_assoc. rewrite (add_commute (f:=LRnnonehalf ⨰ indep _ _)). rewrite -> add_assoc.
        rewrite IHn. clear IHn.
        (* Commute and apply the induction hypothesis: 
            1/2 * (1/2 * 2^-n * c) + 1/2 * 2^-n * c + Pn == 1/2 * 1/2 * 2^-n * c + 1/2 * 2^-n * c + Pn *)
        rewrite <- !add_assoc.
        apply compose_Proper; try reflexivity; try apply pair_Proper; try reflexivity.
        (* Remove Pn from each side:
            1/2 * (1/2 * 2^-n * c) + 1/2 * 2^-n * c == 1/2 * 1/2 * 2^-n * c + 1/2 * 2^-n * c *)
        (* Now we can equate summands. *)
        apply compose_Proper; try reflexivity; try apply pair_Proper.
        + rewrite !mult_scale. reflexivity.
        + reflexivity.
      }
  Qed.

  Lemma infinitary_add_scale : forall {A B} {f : A ~~> Meas B} {r : nat -> A ~~> LRnn},
      sum' r ⨰ f == sum (fun n : nat => r n ⨰ f).
  Proof. intros A B f r.
         unfold sum'. rewrite pairL_Cont.
         rewrite postcompose_Cont. apply sup_exacteq_sup. simpl.
         intros n. induction n.
         - simpl. rewrite zero_scale. reflexivity.
         - simpl. rewrite add_scale. apply compose_Proper; try reflexivity; apply pair_Proper.
           + reflexivity.
           + apply IHn.
  Qed.

  Lemma Prob_Meas_indep : forall {Γ A B} {f : Γ ~~> Prob A} {g : Γ ~~> Prob B},
      Prob_to_Meas ∘ (indep f g) == indep (Prob_to_Meas ∘ f) (Prob_to_Meas ∘ g).
  Proof. intros Γ A B f g.
         unfold indep. unfold Bind, bind. rewrite !compose_assoc.
         rewrite Prob_Meas_join. remove_eq_left.
         unfold makeFun1E. rewrite (compose_assoc _ (map _) (map _)).
         rewrite <- map_compose.
         rewrite !compose_assoc. rewrite Prob_Meas_join.
         rewrite <- !(compose_assoc _ _ join), -> !(map_compose _ join).
         rewrite !compose_assoc. rewrite <- Prob_Meas_map.
         remove_eq_left.
         rewrite -> !compose_assoc, <- Prob_Meas_map.
         rewrite <- (compose_assoc _ Prob_to_Meas). rewrite <- Prob_Meas_strong.
         rewrite <- !compose_assoc, -> parallel_pair, -> compose_id_left.
         remove_eq_right.
         unfold Ret. rewrite <- (compose_assoc _ (map Prob_to_Meas)).
         rewrite <- map_compose. rewrite (compose_assoc _ ret).
         rewrite Prob_Meas_ret. rewrite <- Prob_Meas_map.
         rewrite !map_compose.
         remove_eq_left.
         rewrite <- !map_compose. apply map_Proper.
         rewrite compose_assoc. rewrite <- Prob_Meas_strong.
         remove_eq_left.
         rewrite parallel_pair, compose_id_left.
         unfold Lift, extend, Extend_Prod, Extend_Refl.
         rewrite !compose_id_left, compose_assoc. reflexivity.
  Qed.

  Lemma sums_to_one : LRnnone LRnn == sum' (fun n : nat => ttm (S n)).
  Proof. admit. Admitted.
  
  Definition wait_for_heads : PartialSampler (Δ := unit) (S := Samplers.Cantor) (A := Boole)
                                              infinite_coinflips (Ret Zero).
  Proof.
    unshelve eapply par_sampler.
    apply (fixF ∘ snd).
    unfold Cantor, Samplers.Cantor, Boole. rewrite Map_snd.
    pose (sfix_map(Σ:=Σ) F G H F_Proper G_Proper (ishas bottom_min) (ishas zero_min)
         H_Proper HF_GH Hbot HCont) as P.
    unfold H, Cantor, Samplers.Cantor, Boole in P. unfold fixF, Cantor, Samplers.Cantor, Boole.
    rewrite P; clear P.
    pose (G_fix_sum) as P; unfold Cantor, Samplers.Cantor, Boole in P; rewrite P; clear P.
    unfold Gsum.
    rewrite <- infinitary_add_scale.
    rewrite Prob_Meas_map. rewrite <- compose_assoc.
    unfold infinite_coinflips.
    rewrite tail_constant_stream.
    unshelve etransitivity.
    apply (LRnnone _ ⨰ indep (Prob_to_Meas ∘ constant_stream coinflip) (Ret Zero)).
    rewrite <- (compose_id_right (LRnnone _)). rewrite (unit_uniq id tt).
    rewrite one_scale.
    rewrite Prob_Meas_indep. apply indep_Proper; try reflexivity.
    unfold Ret. rewrite compose_assoc, Prob_Meas_ret. reflexivity.
    apply compose_Proper; try reflexivity; apply pair_Proper; try reflexivity.
    apply sums_to_one.
  Qed. 

End PartialSamplers.
        