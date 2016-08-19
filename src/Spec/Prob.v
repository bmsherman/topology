Require Import Spec.Category.

Import Category.
Local Open Scope obj.
Local Open Scope morph.

Module Prob.
Section Prob.

  Arguments exist {A} {P} x _.
  
Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmcprops : CMC_Props U}.

Require Import Spec.Sierpinski Spec.Real Spec.Sum Spec.Pullback Spec.Stream Spec.Discrete
        Spec.SMonad Spec.Vec Spec.Power Spec.Sup Spec.OEmbedding Spec.Lift Fix.
Require Import Morphisms.
Import Sierp.
Import Power.
Import Real.
Import Sum Pullback.
Import Vec.
Import Stream.
Import Discrete.
Import Fix.
Import Sup.
Import Lift.
Import OEmbedding.

Context `{Σos : ΣOps U (ccat := ccat) (cmc := cmc)}.
Context {Σps : ΣProps (U:=U)}.
Context `{lrnnops : LRnnOps U (ccat := ccat) (cmc := cmc) 
  (Σ := Σ)}.
Context `{realops : ROps U (ccat := ccat) (cmc := cmc) 
  (Σ := Σ)}.
Context `{sumops : SumOps U (ccat := ccat)}{sumprops : SumProps}.
Context `{streamops : StreamOps U (ccat := ccat)}.
Context `{pos : PowOps (U:=U) (ccat:=ccat)}.
(* Context {Embedding : (forall {A B : U}, (A ~~> B) -> Prop)}. *)

(*Axiom inl_embedding : forall {A B : U}, Embedding _ _ (inl(A:=A)(B:=B)).
Axiom inr_embedding : forall {A B : U}, Embedding _ _ (inr(A:=A)(B:=B)).
Axiom id_embedding : forall {A : U}, Embedding _ _ (id (A:=A)).
Axiom compose_embedding : forall {A B C : U} {f : A ~~> B} {g : B ~~> C},
    Embedding _ _ f -> Embedding _ _ g -> Embedding _ _ (g ∘ f).
Axiom embedding_Proper : forall {A B} {f g : A ~~> B}, (f == g) -> Embedding _ _ f -> Embedding _ _ g.
Axiom zero_one_embedding : Embedding _ _ (tt (Γ:=False)).

Axiom emb_generic : forall {A B : U} {f : A ~~> B} {e : Embedding _ _ f}, Embedding _ _ f.*)

Context {Open : U -> U}.

Class OpenOps : Type :=
  { open_abstract : forall {Γ A : U}, Γ * A ~~> Σ -> Γ ~~> Open A
    ; open_sum_prod0 : forall {A B}, Open (A + B) ~~> Open A * Open B
    ; open_sum_prod1 : forall {A B}, Open A * Open B ~~> Open (A + B)}.

Context {oos : OpenOps}.
Context {Meas Prob SubProb : U -> U}.
Context {discrete : Type -> U}.
Context {DOps : DiscreteOps (U:=U) (ccat:=ccat)(cmc:=cmc) discrete}.
Context {DProps : (@DiscreteProps U ccat cmc discrete DOps)}.
Context {L : U -> U} {los : LiftOps(Lift:=L)(Σ:=Σ)(Stream:=Stream)}{lps : LiftProps}.

Require Import Spec.CCC.CCC.
Require Import Spec.CCC.Presheaf.
Require Import Prob.Language.ContPL.
Require Import Prob.Language.ContPLProps.

Import CCC.
Import Presheaf.

Existing Instances CCat_PSh CMC_Psh CMCProps_PSh CCCOps_PSh.


Class MeasOps : Type :=
  { MeasMonad : SMonad (ccat := ccat) (cmc := cmc) U Meas
  ; ProbMonad : SMonad  (ccat := ccat) (cmc := cmc) U Prob
  ; SubProbMonad : SMonad  (ccat := ccat) (cmc := cmc) U SubProb
  ; Prob_to_SubProb : forall {A}, Prob A ~~> SubProb A
  ; SubProb_to_Meas : forall {A}, SubProb A ~~> Meas A
  ; Prob_SubProb_strong : forall {A B}, strong (A:=A)(B:=B) ∘ (id ⊗ Prob_to_SubProb) == Prob_to_SubProb ∘ strong
  ; SubProb_Meas_strong : forall {A B}, strong (A:=A)(B:=B) ∘ (id ⊗ SubProb_to_Meas) == SubProb_to_Meas ∘ strong
  ; Prob_SubProb_map : forall {A B} (f : A ~~> B), (map f) ∘ Prob_to_SubProb == Prob_to_SubProb ∘ (map f)       
  ; SubProb_Meas_map : forall {A B} (f : A ~~> B), (map f) ∘ SubProb_to_Meas == SubProb_to_Meas ∘ (map f)
  ; Prob_SubProb_ret : forall {A}, Prob_to_SubProb ∘ ret (A:=A) == ret
  ; SubProb_Meas_ret : forall {A}, SubProb_to_Meas ∘ ret (A:=A) == ret
  ; Prob_SubProb_join : forall {A},
      Prob_to_SubProb ∘ join (A:=A) == join ∘ Prob_to_SubProb ∘ (map Prob_to_SubProb)
  ; SubProb_Meas_join : forall {A},
      SubProb_to_Meas ∘ join (A:=A) == join ∘ SubProb_to_Meas ∘ (map SubProb_to_Meas)
  ; zero : forall {Γ A}, Γ ~~> Meas A
  ; zero_ext : forall {Γ Γ' A} (x : Γ ~~> Γ'), zero ∘ x == zero (A:=A)
  ; zero_min : forall {Γ A}, isBot (Σ:=Σ)(@zero Γ A)
  ; MeasEval : forall {A}, Meas A * Open A ~~> LRnn
  (** A real number telling us the probability that we
      are in the left-hand side **)
  ; ClopenEval : forall {A B : U}, Prob (A + B) ~~> R
  ; Meas_Sum : forall {A B}, Meas A * Meas B ~~> Meas (A + B)
  ; coinflip : unit ~~> Prob (unit + unit)
  ; normal : unit ~~> Prob R
  ; pstream : forall {Γ A X}, Γ ~~> X -> Γ * X ~~> Prob (A * X)
                         -> Γ ~~> Prob (Stream A)
  ; pstream_Proper : forall Γ A X, Proper (eq ==> eq ==> eq) (@pstream Γ A X)
  ; pstream_ext1 : forall {Γ Δ A X} (g : Γ ~~> Δ) (x : Δ ~~> X) (f : Δ * X ~~> Prob (A * X)),
      (pstream x f) ∘ g == pstream (x ∘ g) (f ∘ (g ⊗ id))
  ; unit_Prob : (id (A := Prob unit)) == ret ∘ tt
  ; fst_strong : forall {A B}, (map fst) ∘ (strong (M:=Prob)(A:=A)(B:=B)) == ret ∘ fst
  ; Meas_Embed : forall {A B} (f : A ~~> B), OpenEmbedding (Σ:=Σ) f -> (Meas B) ~~> (Meas A)
  ; Meas_Embed_Proper0 : forall {A B} (f g : A ~~> B) (e : OpenEmbedding f) (p : (f == g)),
      Meas_Embed f e == Meas_Embed g (OpenEmbedding_Proper p e)
  ; Meas_Embed_Proper1 : forall {A B} (f : A ~~> B) (e e' : OpenEmbedding f),
      (forall (R : A ~~> Σ), dir_img (OpenMap:=(open_map (OpenEmbedding:=e))) R ==
                      dir_img (OpenMap:=(open_map (OpenEmbedding:=e'))) R) -> 
      Meas_Embed f e == Meas_Embed f e'
(*  ; Embed_irrel : forall {A B} (f : A ~~> B) (e e' : OpenEmbedding _ _ f), (Meas_Embed f e) ==
                                                                  (Meas_Embed f (emb_generic (e:=e')))*)
 ; Embed_nat : forall {A B C D} (e : A ~~> B) (f : B ~~> D) (g : A ~~> C) (h : C ~~> D)
      (ee : OpenEmbedding  e) (he : OpenEmbedding h), (Pullback e f g h) ->
      (Meas_Embed h he) ∘ (map f) == (map g) ∘ (Meas_Embed e ee)
  ; Pstream : forall {A X : U}, Const (Y X ==> (Y X ==> Y (Prob (A * X))) ==> Y (Prob (Stream A)))
  ; Coinflip : Const (Y (Prob (unit + unit)))
  ; Normal : Const (Y (Prob R))
  ; Prob_discrete : forall {A}, (Prob (discrete A)) ~~> power A LRnn
  ; Prob_discrete_mono : forall {A}, Mono (Prob_discrete (A:=A))
  ; Meas_unit : Meas unit ≅ LRnn
  ; Meas_scale : forall {A}, LRnn * Meas A ~~> Meas A
  ; Meas_add : forall {A}, Meas A * Meas A ~~> Meas A
  ; add_zero_right : forall {A}, Meas_add (A:=A) ∘ ⟨id, zero⟩ == id
  ; add_zero_left : forall {A}, Meas_add (A:=A) ∘ ⟨zero, id⟩ == id
  ; scale_zero : forall {Γ A f}, Meas_scale ∘ ⟨f, zero(Γ:=Γ)(A:=A)⟩ == zero
  ; scale_add : forall {Γ A f} {g h : Γ ~~> Meas A},
      Meas_scale ∘ ⟨f, Meas_add ∘ ⟨g, h⟩⟩ == Meas_add ∘ ⟨Meas_scale ∘ ⟨f, g⟩, Meas_scale ∘ ⟨f, h⟩⟩
  ; add_assoc : forall {Γ A} {f g h : Γ ~~> Meas A},
      Meas_add ∘ ⟨Meas_add ∘ ⟨f, g⟩, h⟩ == Meas_add ∘ ⟨f, Meas_add ∘ ⟨g, h⟩⟩
  ; add_commute : forall {Γ A} {f g : Γ ~~> Meas A},
      Meas_add ∘ ⟨f, g⟩ == Meas_add ∘ ⟨g, f⟩
  ; add_Proper : forall {Γ A}, Proper (eq ==> eq ==> eq) (fun g h : Γ ~~> Meas A => Meas_add ∘ ⟨g, h⟩)
  ; zero_scale : forall {Γ A} {f : Γ ~~> Meas A},
      Meas_scale ∘ ⟨LRnnzero _ ∘ tt, f⟩ == zero
  ; one_scale : forall {Γ A} {f : Γ ~~> Meas A},
      Meas_scale ∘ ⟨LRnnone _ ∘ tt, f⟩ == f
  ; add_scale : forall {Γ A f g} {h : Γ ~~> Meas A},
      Meas_scale ∘ ⟨(LRnnplus _) ∘ ⟨f, g⟩, h⟩ == Meas_add ∘ ⟨Meas_scale ∘ ⟨f, h⟩, Meas_scale ∘ ⟨g, h⟩⟩
  ; mult_scale : forall {Γ A f g} {h : Γ ~~> Meas A},
      Meas_scale ∘ ⟨(LRnnmult _) ∘ ⟨f, g⟩, h⟩ == Meas_scale ∘ ⟨f, Meas_scale ∘ ⟨g, h⟩⟩
  ; copair_add : forall {A B C : U} (f : A ~~> C) (g : B ~~> C),
      map (copair f g) ==
      Meas_add ∘ ⟨ map f ∘ Meas_Embed inl inl_open_embedding, map g ∘ Meas_Embed inr inr_open_embedding ⟩
  ; map_scale : forall {A B : U} {r : unit ~~> LRnn} {f : A ~~> B},
      (Meas_scale ∘ (r ⊗ id) ∘ add_unit_left) ∘ (map f) ==
      (map f) ∘ (Meas_scale ∘ (r ⊗ id) ∘ add_unit_left)
  ; Embed_scale : forall {A B : U} {r : unit ~~> LRnn} {f : A ~~> B} {e : OpenEmbedding f},
      (Meas_scale ∘ (r ⊗ id) ∘ add_unit_left) ∘ (Meas_Embed f e) ==
      (Meas_Embed f e) ∘ (Meas_scale ∘ (r ⊗ id) ∘ add_unit_left)
  ; Meas_false : Meas False ≅ unit             
  }.

Context {mops : MeasOps}.

Existing Instances ProbMonad SubProbMonad MeasMonad. 

Section Ev.

  Existing Instance OpenEmbedding_Proper.

  Definition MeasΣ : Meas Σ ~~> Meas unit. (* Restriction along true *)
  Proof. unshelve eapply Meas_Embed. apply true.
         unshelve eapply OpenEmbedding_Proper.
         exact (terminates ∘ strict).
         unfold terminates. rewrite lift_rec_strict.
         rewrite <- (compose_id_right true). remove_eq_left. apply unit_uniq.
         apply compose_open_embedding. apply strict_open_embedding.
         pose (Iso_OpenEmbedding (Σ:=Σ) (Iso_Sym Σ_cong_Lu)) as P. simpl in P.
         apply P.
  Defined.
   (* A direct proof of the above.
         unshelve esplit.
         unshelve esplit.
         - intros f.
           eapply compose. Focus 2.
           unshelve eapply Σ_to_Lift.
           exact L.
           unshelve eapply lift_rec.
           exact false. exact f. intros a; apply false_sleq_anything.
         - intros V V' H. simpl. apply sub_ext.
           apply sub_lift. rewrite !lift_rec_bottom. apply sub_reflexive.
           rewrite !lift_rec_strict. assumption.
         - intros V W. simpl. split.
           + intros H. unfold inv_img. apply (sub_ext true) in H.
             eapply sub_Proper. Focus 3. apply H.
             rewrite <- compose_assoc, -> true_to_Lift, -> lift_rec_strict.
             reflexivity. reflexivity.
           + intros H. unfold inv_img in H.
             apply sub_Σ.
             rewrite <- compose_assoc, -> false_to_Lift, -> lift_rec_bottom.
             eapply sub_Proper. Focus 3. eapply false_smallest.
             rewrite <- compose_id_right at 1. remove_eq_left. apply unit_uniq. reflexivity.
             rewrite <- compose_assoc, -> true_to_Lift, -> lift_rec_strict. assumption.
         - intros V. unfold inv_img, dir_img.
           rewrite <- compose_assoc, -> true_to_Lift, -> lift_rec_strict. apply sub_reflexive.
  Defined.
*)         
  
  Definition MEv : forall {Γ A}, (Γ ~~> Meas A) -> (A ~~> Σ) -> Γ ~~> LRnn :=
    fun _ _ f g => (to Meas_unit) ∘ MeasΣ ∘ (map g) ∘ f.

  Axiom MEv_determines : forall {Γ A} (mu nu : Γ ~~> Meas A),
      (forall V : A ~~> Σ, MEv mu V == MEv nu V) -> mu == nu.

  Axiom MEv_embed : forall {Γ A B} {f : A ~~> B} {e : OpenEmbedding f} (mu : Γ ~~> Meas B) (U : A ~~> Σ),
      MEv (Meas_Embed _ e ∘ mu) U == MEv mu (dir_img (OpenMap:=open_map(OpenEmbedding:=e)) U).
  
  Axiom MEv_scale : forall {Γ A} {mu : Γ ~~> Meas A} {V : A ~~> Σ} (r : unit ~~> LRnn),
      MEv (Meas_scale ∘ r ⊗ id ∘ add_unit_left ∘ mu) V == (LRnnmult _ ∘ r ⊗ MEv mu V ∘ add_unit_left).
  
  Context `{mps : SMonad_Props U Meas (ccat:=ccat)(smd:=MeasMonad) (cmc:=cmc)(cmcprops:=cmcprops)}.

  Lemma MEv_Proper : forall {Γ A}, Proper (eq ==> eq ==> eq) (MEv(Γ:=Γ)(A:=A)).
  Proof. intros Γ A. unfold Proper, respectful.
         intros x y H x0 y0 H0. unfold MEv.
         repeat (try apply compose_Proper; try assumption; try reflexivity).
         eapply map_Proper. assumption.
  Qed.

  Existing Instance MEv_Proper.

    Lemma MEv_scale' : forall {A} {mu : unit ~~> Meas A} {V : A ~~> Σ} (r : unit ~~> LRnn),
      MEv (Meas_scale ∘ ⟨r, mu⟩) V == (LRnnmult _ ∘ ⟨r, MEv mu V⟩).
  Proof. intros A mu V r.
         pose (MEv_scale (mu:=mu) (V:=V) r) as e. etransitivity. symmetry; etransitivity.
         symmetry; apply e; clear e.
         apply MEv_Proper. remove_eq_left.
         apply proj_eq; rewrite ?parallel_fst, ?parallel_snd, ?pair_fst, ?pair_snd.
         rewrite !compose_assoc. rewrite parallel_fst. rewrite <- (compose_id_right r) at 2.
         remove_eq_left. apply unit_uniq.
         rewrite !compose_assoc. rewrite parallel_snd. rewrite <- (compose_id_left mu) at 2.
         remove_eq_right. rewrite compose_id_left. unfold add_unit_left. rewrite pair_snd. reflexivity.
         reflexivity.
         remove_eq_left. apply proj_eq.
         rewrite pair_fst, compose_assoc, parallel_fst.
         rewrite <- compose_assoc. unfold add_unit_left. rewrite pair_fst.
         rewrite (unit_uniq tt id). rewrite compose_id_right. reflexivity.
         rewrite pair_snd, compose_assoc, parallel_snd.
         rewrite <- compose_assoc.
         unfold add_unit_left. rewrite pair_snd. rewrite compose_id_right. reflexivity.
  Qed.
  
  Lemma Embed_id : forall {A : U}, Meas_Embed (id(A:=A)) id_open_embedding == id.
  Proof. intros A.
         apply MEv_determines. intros V.
         rewrite <- (compose_id_right (Meas_Embed id _)).
         rewrite MEv_embed. apply MEv_Proper. reflexivity.
         reflexivity.
  Defined.

  Lemma Embed_compose : forall {A B C : U} {f : A ~~> B} {g : B ~~> C}
                          (e : OpenEmbedding f)(k : OpenEmbedding g),
      Meas_Embed f e ∘ Meas_Embed g k == Meas_Embed (g ∘ f) (compose_open_embedding e k).
  Proof. intros A B C f g e k.
         apply MEv_determines.
         intros V.
         rewrite MEv_embed.
         rewrite <- (compose_id_right (Meas_Embed g k)), <- (compose_id_right (Meas_Embed (compose g f) _)).
         rewrite !MEv_embed.
         apply MEv_Proper. reflexivity.
         destruct e, k. simpl. reflexivity.
  Qed.
  
  Lemma Embed_map : forall {A B} (f : A ~~> B) (e : OpenEmbedding f), (Meas_Embed f e) ∘ (map f) == id.
  Proof. intros A B f e. pose (Embed_nat id f id f id_open_embedding e).
         erewrite e0.
         rewrite map_id. rewrite compose_id_left. rewrite Embed_id. reflexivity.
         apply pb_Mono_iff. apply (Embedding_Mono e).
  Qed.

  Definition Prob_to_Meas {A} := SubProb_to_Meas (A:=A) ∘ Prob_to_SubProb.
  
  Theorem Prob_Meas_strong : forall {A B},
      strong (A:=A)(B:=B) ∘ (id ⊗ Prob_to_Meas) == Prob_to_Meas ∘ strong.
  Proof. intros A B. unfold Prob_to_Meas.
         rewrite <- !compose_assoc.
         rewrite <- Prob_SubProb_strong.
         rewrite (compose_assoc _ strong).
         rewrite <- SubProb_Meas_strong.
         remove_eq_left.
         rewrite <- (compose_id_left id) at 1.
         rewrite parallel_compose.
         reflexivity.
  Qed.

  Lemma Prob_Meas_map : forall {A B} (f : A ~~> B), (map f) ∘ Prob_to_Meas == Prob_to_Meas ∘ (map f).
  Proof. intros A B f.
         unfold Prob_to_Meas.
         rewrite compose_assoc.
         rewrite SubProb_Meas_map. remove_eq_left.
         apply Prob_SubProb_map.
  Qed.

  Lemma Prob_Meas_ret : forall {A}, Prob_to_Meas ∘ ret (A:=A) == ret.
  Proof. intros A.
         unfold Prob_to_Meas.
         rewrite <- !compose_assoc.
         rewrite Prob_SubProb_ret.
         rewrite SubProb_Meas_ret.
         reflexivity.
  Qed.

  Context {pps : SMonad_Props (smd:=ProbMonad)}.
  
  Lemma Prob_Meas_join :  forall {A},
      Prob_to_Meas ∘ join (A:=A) == join ∘ Prob_to_Meas ∘ (map Prob_to_Meas).
  Proof. intros A.
         unfold Prob_to_Meas.
         rewrite <- compose_assoc.
         rewrite Prob_SubProb_join.
         rewrite !compose_assoc.
         rewrite SubProb_Meas_join.
         remove_eq_left. rewrite !compose_assoc.
         rewrite (map_compose (M:=Prob)). remove_eq_right.
         apply Prob_SubProb_map.
  Qed.

  Lemma Prob_Meas_Bind : forall {Γ A B} (m : Γ ~~> Prob A) (f : Γ * A ~~> Prob B),
      Prob_to_Meas ∘ Bind m f == Bind (Prob_to_Meas ∘ m) (Prob_to_Meas ∘ f).
  Proof. intros Γ A B m f.
         unfold Bind, bind.
         rewrite !compose_assoc.
         rewrite Prob_Meas_join. remove_eq_left.
         rewrite pair_parallel_id. remove_eq_right.
         rewrite <- !compose_assoc. rewrite Prob_Meas_strong. remove_eq_right.
         rewrite Prob_Meas_map. remove_eq_left.
         rewrite map_compose. remove_eq_left.
  Qed.

  Lemma Prob_Meas_Ret : forall {Γ A} {f : Γ ~~> A}, Prob_to_Meas ∘ Ret f == Ret f.
  Proof. intros Γ A f. unfold Ret. remove_eq_right. apply Prob_Meas_ret.
  Defined.

  
  Definition Left : forall {Γ A B}, Γ ~~> Open (A + B).
  Proof. intros.
         unshelve eapply open_abstract.
         unshelve eapply sum_elim.
         - exact (true ∘ tt).
         - exact (false ∘ tt).
  Defined.

  Definition Right : forall {Γ A B}, Γ ~~> Open (A + B).
  Proof. intros.
         unshelve eapply open_abstract.
         unshelve eapply sum_elim.
         - exact (false ∘ tt).
         - exact (true ∘ tt).
  Defined.

  Axiom MEv_Bind_coprod : forall {Γ A B C} {mu : Γ ~~> Meas (A + B)} {f : Γ * (A + B) ~~> Meas C} (V : C ~~> Σ),
      MEv (Bind mu f) V == (LRnnplus LRnn
    ∘ ⟨ (*LRnnmult LRnn
        ∘ ⟨ MEv mu (copair (true ∘ tt) (false ∘ tt)),*)
          MEv (Bind (Meas_Embed inl inl_open_embedding ∘ mu) (f ∘ id ⊗ inl)) V (*⟩*),
      (*LRnnmult LRnn
      ∘ ⟨ MEv mu (copair (false ∘ tt) (true ∘ tt)),*)
        MEv (Bind (Meas_Embed inr inr_open_embedding ∘ mu) (f ∘ id ⊗ inr)) V (*⟩*) ⟩).
(* Maybe this is provable; maybe it's false. The intuition is, in order to see how much measure you assign to V, you see how much measure you assign to V that flows through A --- the first term --- and you see how much measure you assign to V that flows through B --- the second term. *)

    
  (* Axiom Bind_cancel : forall {Γ A B C} (mu : Γ ~~> Meas (A + B))
                        (f f' : Γ * A ~~> Meas C) (g g' : Γ * B ~~> Meas C),
      LRnnlt LRnn (LRnnzero LRnn ∘ tt) (MeasEval ∘ ⟨mu, Left⟩) ->
      LRnnlt LRnn (LRnnzero LRnn ∘ tt) (MeasEval ∘ ⟨mu, Right⟩)->
      ((Bind mu (sum_elim f g)) == (Bind mu (sum_elim f' g'))) ->
      (g == g') ->
      (f == f'). THIS IS FALSE *)
  
                         
End Ev.

Section Fixp.
  Context {Γ A : U}.
  Context {sps : SumProps}.
  Context {mu : Γ ~~> Meas A}.

  Definition F (x : Γ ~~> Meas A) : Γ ~~> Meas A.
  Proof. intros.
         unshelve eapply Bind. apply (unit + unit).
         - apply (Prob_to_Meas ∘ (coinflip ∘ tt)).
         - unshelve eapply sum_elim.
           + apply (mu ∘ fst).
           + apply (x ∘ fst).
  Defined.

  Definition sleq {A B} := sleq (A:=A) (B:=B) (Σ:=Σ).

  Axiom map_sleq : forall {P Q M0} {M : SMonad U M0}, Proper (sleq ==> sleq) (map (M:=M0) (A:=P)(B:=Q)).
  Axiom map_Cont : forall {P Q M0} {M : SMonad U M0}, Cont (map (M:=M0)(A:=P)(B:=Q)) map_sleq.
  
  
  Theorem Bind_sleq : forall {Δ C B : U} (nu : Δ ~~> Meas C), Proper (sleq ==> sleq) (Bind (B:=B) nu).
  Proof. intros Δ C B nmu f g H.
         unfold Proper, respectful.
         unfold Bind, bind.
         repeat (apply compose_sleq; try apply sleq_reflexive).
         apply map_sleq.
         assumption.
  Qed.

  Lemma Bind_Cont : forall {Δ B C : U} (f : Δ ~~> Meas B), Cont (Bind (B:=C) f) (Bind_sleq f).
  Proof. intros.
         unfold Cont. intros.
         unfold Bind, bind.
         rewrite map_Cont.
         simpl.
         etransitivity.
         apply compose_Proper. apply postcompose_Cont. reflexivity.
         rewrite precompose_Cont. simpl.
         apply sup_exacteq_sup. reflexivity.
  Qed.
         
  
  Existing Instance sleq_Proper.  
  
  Lemma F_Proper : Proper (sleq ==> sleq) F.
  Proof. unfold Proper, respectful.
         intros x y H.
         unfold F.
         apply Bind_sleq.
         apply sum_sleq.
         - rewrite !sum_elim_inl.
           apply sleq_reflexive.
         - rewrite !sum_elim_inr.
           apply sleq_ext.
           assumption.
  Qed.



  Context {msmp : SMonad_Props (M:=Meas)} {psmp : SMonad_Props (M:=Prob)}.
  
  Lemma F_Cont : Cont F F_Proper.
  Proof. unfold Cont.
         intros f.
         unfold F.

         etransitivity.

         eapply Bind_Proper. reflexivity.

         etransitivity.
         eapply sum_elim_Proper. reflexivity.
         apply precompose_Cont.          
         eapply sum_elim_Cont.

         rewrite Bind_Cont. apply sup_exacteq_sup.
         reflexivity.
  Qed.

  Theorem Bind_Prob_Meas : forall {Δ X Z} (nu : Δ ~~> Prob X) (y : Δ ~~> Meas Z),
               Bind (Prob_to_Meas ∘ nu) (y ∘ fst) == y.
  Proof.  intros Δ X Z nu y.
          unfold Bind, bind.
          rewrite map_compose.
          rewrite <- !compose_assoc.
          rewrite pair_parallel_id.
          rewrite (compose_assoc _ _ strong).
          rewrite Prob_Meas_strong.
          rewrite <- !compose_assoc.
          rewrite (compose_assoc _ Prob_to_Meas).
          rewrite Prob_Meas_map.
          rewrite <- !compose_assoc.
          rewrite (compose_assoc _ strong).           
          rewrite fst_strong.
          rewrite <- !compose_assoc.
          rewrite pair_fst, compose_id_right.
          rewrite (compose_assoc ret).
          rewrite Prob_Meas_map.
          rewrite <- !compose_assoc. rewrite <- ret_nat.
          rewrite <- (compose_id_left y) at 2.
          remove_eq_right. rewrite <- compose_assoc.
          rewrite Prob_Meas_ret.
          rewrite join_ret. reflexivity.
  Qed.

  Existing Instance LRnnlt_Proper.

  Theorem fix_F : forall {f : Γ ~~> Meas A}, (F f) == f -> f == mu.
  Proof. intros f Ff. assert (f ∘ fst (B:=unit) == mu ∘ fst). {
         unfold F in Ff. 
         rewrite <- (Bind_Prob_Meas (coinflip ∘ tt) f) in Ff at 2.
         rewrite <- sum_elim_duple in Ff.
         symmetry. Abort. (*
         unshelve eapply (Bind_cancel _ _ _ _ _ _ _ Ff).
         - (* This says, or should say (after some annoying stuff), that 1/2 > 0, qua LRnn's. This is 
clearly true. I will figure out the way to make that most clear later. *)
           rewrite SumEval. (* one could use x < y -> x < k + y here *)
           admit.
         - (* Ditto. *) admit.
         - reflexivity.
         }
         eapply fst_Epi.
         Focus 2. apply H.
         exact tt.
  Admitted.
*)
  Theorem fix_F' : (sfix F (ishas zero_min) F_Proper) == mu.
  Proof. (* apply fix_F.
         apply sfix_fix.
         apply F_Cont.
  Qed.        *) Abort.

    
  
End Fixp.


Lemma Prob_unit_Iso : Prob unit ≅ unit.
Proof. eapply Build_Iso. Unshelve.
       Focus 3. exact tt.
       Focus 3. exact ret.
       apply unit_uniq.
       symmetry. exact unit_Prob.
Defined.


Axiom pstream_unfold : forall (Γ A X : U) 
 (x : Γ ~~> X) (f : Γ * X ~~> Prob (A * X)),
      pstream x f == (
        y <-  (f ∘ ⟨ id , x ⟩);
        zs <- pstream (X := X) (snd ∘ y) (liftF f) ;
         Ret (cons (fst ∘ !y) zs) 
      ).

Definition Prob_Stream_eq_extended_type : forall {Γ A B} {s t : Γ ~~> Meas (Stream A * B)}, Prop.
Proof. intros.
       refine (Basics.impl _ (s == t)).
       refine (forall n, map (prefix n ⊗ id) ∘ s == map (prefix n ⊗ id) ∘ t).
Defined.

Definition Prob_Stream_eq_type : forall {Γ A} {s t : Γ ~~> Prob (Stream A)}, Prop.
(**    (forall n, (map (prefix n)) ∘ s == (map (prefix n)) ∘ t) -> (s == t). **)
Proof. intros.
       refine (Basics.impl _ (s == t)).
       refine (forall n, (map (prefix n)) ∘ s == (map (prefix n)) ∘ t).
       (** Show Proof. (It looks the same as the comment above, but just typing that didn't work for some reason.) **)
Defined.

Axiom Prob_Stream_eq_extended : forall {Γ A B} {s t : Γ ~~> Meas (Stream A * B)},
    @Prob_Stream_eq_extended_type Γ A B s t.
Axiom Prob_Stream_eq : forall {Γ A} {s t : Γ ~~> Prob (Stream A)},
    Prob_Stream_eq_type (Γ:=Γ) (A:=A) (s:=s) (t:=t).

Notation "'LAM'<< Γ | E >> x => f" := (makeFun1E (fun Γ E x => f))
                                        (at level 120, right associativity). 

Notation "x <- e ;<< Γ | E >> f" := (Bind e (makeFun1E (fun Γ E x => f))) 
                                      (at level 120, right associativity).

Axiom Fubini : forall {Γ A B C} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B) 
                 (f g : forall Δ (ext : Extend Γ Δ), (Δ ~~> A) -> (Δ ~~> B) -> (Δ ~~> Prob C)),
      (forall Δ ext a b, (f Δ ext a b) == (g Δ ext a b) )->
      (x <- mu;<< Δ | e >> y <- !nu;<< Δ' | e' >> (f Δ' (e∘e') (!x) y))
      == (y <- nu;<< Δ | e >> x <- !mu;<< Δ' | e' >> (g Δ' (e∘e') x (!y))).


  (* Maybe this should be elsewhere? *)
  
Theorem Fubini_pair : forall {Γ A B} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
    (x <- mu; y <- !nu; Ret ⟨!x, y⟩) == (y <- nu; x <- !mu; Ret ⟨x, !y⟩).
Proof. intros Γ A B mu nu.  
         unshelve eapply (Fubini mu nu (fun _ _ a b => Ret ⟨a, b⟩) (fun _ _ a b => Ret ⟨a, b⟩) _).
         intros. reflexivity.         
Qed.


Definition marg {A B : U} : Prob (A * B) ~~> (Prob A) * (Prob B) :=
  ⟨map fst , map snd⟩.
(** 'marg' for 'marginal' **)



End Prob.

End Prob. 