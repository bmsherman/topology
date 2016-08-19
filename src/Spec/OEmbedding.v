Require Import Spec.Category Spec.Sierpinski Spec.Sum Spec.Sup Spec.Stream Spec.Pullback Spec.Lift.
Import Morphisms Category Sierp Sum Sup Stream Pullback Lift.

Local Open Scope obj.
Local Open Scope morph.

Section OpenEmbeddings.
  
  Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmp : CMC_Props U}
          {Σ : U} {Σos : @ΣOps U ccat cmc Σ} {Σps : ΣProps}.

  Context {sts : SumTys (U:=U)} `{sps : SumProps (U:=U)(ccat:=ccat)(cmc:=cmc)(sts:=sts)}.
  
  Axiom sub_eq : forall {A} {U U' : A ~~> Σ}, sub U U' -> sub U' U -> U == U'.

  Axiom false_smallest : forall {A} {V : A ~~> Σ}, sub (false ∘ tt) V.

  Axiom sub_sum : forall {A B} {V V' : A + B ~~> Σ}, sub (V ∘ inl) (V' ∘ inl) -> sub (V ∘ inr) (V' ∘ inr) ->
                                                         sub V V'.

  Axiom sub_sum' : forall {A B C} {V V' : A * (B + C) ~~> Σ},
      sub (V ∘ id ⊗ inl) (V' ∘ id ⊗ inl) ->
      sub (V ∘ id ⊗ inr) (V' ∘ id ⊗ inr) -> sub V V'. (* probably sound. *)
  
  Axiom sub_or_L : forall {A} {V V' : A ~~> Σ}, sub V (or ∘ ⟨V, V'⟩).
  Axiom sub_or_R : forall {A} {V V' : A ~~> Σ}, sub V (or ∘ ⟨V', V⟩).
  Axiom sub_or_C : forall {A} {V V' W : A ~~> Σ}, sub V W -> sub V' W -> sub (or ∘ ⟨V, V'⟩) W.

  Definition inv_img {A B : U} (f : A ~~> B) : (B ~~> Σ) -> (A ~~> Σ) :=
    fun V => V ∘ f.

  Class OpenMap {A B : U} (f : A ~~> B) : Type :=
    {
      dir_img : (A ~~> Σ) -> (B ~~> Σ);
      dir_monotone : forall {V V' : A ~~> Σ}, sub V V' -> sub (dir_img V) (dir_img V');
      adjointness : forall {U : A ~~> Σ} {V : B ~~> Σ},
          sub (dir_img U) V <-> sub U (inv_img f V)
    }.

  (* The usual zigzags give sub (dir_img (inv_img V)) V and sub U (inv_img (dir_img U)). *)

  Lemma dir_img_unique : forall {A B} (f : A ~~> B) (e e' : OpenMap f) (V : A ~~> Σ),
      (dir_img (OpenMap:=e) V) == (dir_img (OpenMap:=e') V).
  Proof. intros A B f e e' V.
         apply sub_eq.
         rewrite adjointness. rewrite <- adjointness. apply sub_reflexive.
         rewrite adjointness. rewrite <- (adjointness(OpenMap:=e)). apply sub_reflexive.
  Defined.


  Class OpenEmbedding {A B : U} (f : A ~~> B) : Type :=
    {
      open_map : OpenMap f;
      embedding : forall {U : A ~~> Σ}, sub (inv_img f (dir_img U)) U (* We could equivalently say sub instead of eq, because the other direction is automatic. *)
    }.

  Section Zero.
    
    Lemma zero_open {A : U} : OpenMap (False_elim (A:=A)).
    Proof. unshelve esplit.
           - refine (fun _ => false ∘ tt).
           - intros V V' H. simpl. apply sub_reflexive.
           - intros V W. split.
             + intros H; clear H.
               eapply sub_Proper.
               apply (False_elim_unique _ False_elim).
               apply (False_elim_unique _ False_elim).
               apply sub_reflexive.
             + intros H; clear H.
               apply false_smallest.
    Defined.
    
    Lemma zero_open_embedding {A : U} : OpenEmbedding (False_elim (A:=A)).
    Proof. unshelve esplit. apply zero_open.
           intros V.
           eapply sub_Proper.
           apply (False_elim_unique _ False_elim).
           apply (False_elim_unique _ False_elim).
           apply sub_reflexive.
    Defined.

  End Zero.

  Section Sum_inj.

    Lemma inl_open_embedding : forall {A B : U}, OpenEmbedding (inl (A:=A) (B:=B)).
    Proof. intros A B.
           unshelve esplit.
           - unshelve esplit.
             + intros V. apply copair.
               * apply V.
               * apply (false ∘ tt).
             + intros V V' H. simpl.
               apply sub_sum. rewrite !copair_inl.
               assumption. rewrite !copair_inr. apply sub_reflexive.
             + intros V W. split.
               * intros H.
                 unfold inv_img.
                 apply (sub_ext inl) in H.
                 rewrite copair_inl in H.
                 apply H.
               * intros H.
                 unfold inv_img in H.
                 assert (W == copair (W ∘ inl) (W ∘ inr)) as K.
                 {
                   apply inj_eq.
                   - rewrite copair_inl. reflexivity.
                   - rewrite copair_inr. reflexivity.
                 }
                 rewrite K.
                 apply sub_sum. rewrite !copair_inl.
                 assumption. rewrite !copair_inr. apply false_smallest.
           - intros V.
             unfold inv_img, dir_img.
             rewrite copair_inl. apply sub_reflexive.
    Defined.

    
    Lemma inr_open_embedding : forall {A B : U}, OpenEmbedding (inr (A:=A) (B:=B)).
    Proof. intros A B.
           unshelve esplit.
           - unshelve esplit.
             + intros V. apply copair.
               * apply (false ∘ tt).
               * apply V.
             + intros V V' H. simpl.
               apply sub_sum. rewrite !copair_inl. apply sub_reflexive. rewrite !copair_inr. assumption.
             + intros V W. split.
               * intros H.
                 unfold inv_img.
                 apply (sub_ext inr) in H.
                 rewrite copair_inr in H.
                 apply H.
               * intros H.
                 unfold inv_img in H.
                 assert (W == copair (W ∘ inl) (W ∘ inr)) as K.
                 {
                   apply inj_eq.
                   - rewrite copair_inl. reflexivity.
                   - rewrite copair_inr. reflexivity.
                 }
                 rewrite K.
                 apply sub_sum. rewrite !copair_inl.
                 apply false_smallest. rewrite !copair_inr. assumption.
           - intros V.
             unfold inv_img, dir_img.
             rewrite copair_inr. apply sub_reflexive.
    Defined.

  End Sum_inj.

  Section Category.

    Lemma id_open_embedding : forall {A}, OpenEmbedding (id(A:=A)).
    Proof. intros A. unshelve esplit. unshelve esplit.
           - apply (fun V => V).
           - intros V V' H. simpl. assumption.
           - intros V W. simpl.
             unfold inv_img. rewrite compose_id_right.
             reflexivity.
           - intros V.
             unfold inv_img, dir_img. rewrite compose_id_right.
             apply sub_reflexive.
    Defined.

    Lemma compose_open_map : forall {A B C : U} {f : A ~~> B} {g : B ~~> C}, OpenMap f -> OpenMap g ->
                                                                    OpenMap (g ∘ f).
    Proof. intros A B C f g Of Og.
           unshelve esplit.
           - apply (fun V => (dir_img (dir_img V))).
           - intros V V' H. simpl. repeat apply dir_monotone. assumption.
           - intros V W. simpl.
             rewrite !adjointness.
             unfold inv_img. rewrite compose_assoc.
             reflexivity.
    Defined.

    Lemma compose_open_embedding :  forall {A B C : U} {f : A ~~> B} {g : B ~~> C}, OpenEmbedding f ->
                                                                           OpenEmbedding g ->
                                                                           OpenEmbedding (g ∘ f).
    Proof. intros A B C f g Ef Eg.
           destruct Ef as [Of Ef]. destruct Eg as [Og Eg].
           unshelve esplit.
           apply compose_open_map; assumption.
           - intros V.
             unfold dir_img. simpl.
             unfold inv_img in Ef. unfold inv_img in Eg.
             unfold inv_img. rewrite compose_assoc.
             
             eapply sub_transitive. eapply sub_ext.
             apply Eg. apply Ef.
    Defined.             

    Lemma OpenMap_Proper : forall {A B} {f f' : A ~~> B}, f == f' -> OpenMap f -> OpenMap f'.
    Proof. intros A B f f' H Of.
           destruct Of as [f0 f_monotone f_adjoint].
           unshelve esplit.
           - apply f0.
           - apply f_monotone.
           - intros V W. unfold inv_img. rewrite <- H. apply f_adjoint.
    Defined.

    Lemma OpenEmbedding_Proper : forall {A B} {f f' : A ~~> B}, f == f' -> OpenEmbedding f -> OpenEmbedding f'.
    Proof. intros A B f f' H Ef.
           destruct Ef as [Of Ef].
           unshelve esplit.
           - apply (OpenMap_Proper H Of).
           - intros V. specialize (Ef V).
             eapply sub_Proper. Focus 3.
             apply Ef.
             + unfold inv_img. apply compose_Proper.
               * destruct Of. reflexivity.
               * symmetry. apply H.
             + reflexivity.
    Defined.

    Lemma Iso_OpenEmbedding : forall {A B : U} (s : A ≅ B), OpenEmbedding (to s).
    Proof. intros A B s.
           unshelve esplit.
           unshelve esplit.
           - exact (fun V => V ∘ (from s)).
           - simpl. apply sub_ext.
           - unfold inv_img. simpl.
             intros V W. split.
             + intros H. apply (sub_ext (to s)) in H.
               eapply sub_Proper. Focus 3. apply H.
               * rewrite <- compose_assoc, -> (from_to s), -> compose_id_right. reflexivity.
               * reflexivity.
             + intros H. apply (sub_ext (from s)) in H.
               eapply sub_Proper. Focus 3. apply H.
               * reflexivity.
               * rewrite <- compose_assoc, -> (to_from s), -> compose_id_right. reflexivity.
           - unfold inv_img, dir_img.
             intros V.
             rewrite <- compose_assoc, -> (from_to s), -> compose_id_right.
             apply sub_reflexive.
    Defined.

    Lemma inv_dir_is_id : forall {A B} {f : A ~~> B} (e : OpenEmbedding f) {V : A ~~> Σ},
        ((dir_img (OpenMap:=open_map) V) ∘ f) == V.
    Proof. intros A B f Ef V.
           apply sub_eq.
           - apply embedding.
           - pose (fun V W => adjointness (OpenMap:=open_map)(U0:=V)(V:=W)) as a.
             unfold inv_img in a. apply a. clear a.
             apply sub_reflexive.
    Defined.
             


    Lemma Embedding_Mono : forall {A B} {f : A ~~> B}, OpenEmbedding f -> Mono f.
    Proof. intros A B f Ef. unfold Mono. intros X x y H.
           destruct Ef as [Of Ef]. unfold inv_img, dir_img in Ef.
           apply (sleq_eq(Σ:=Σ)).
           - unfold sleq. intros V.
             rewrite <- (inv_dir_is_id (f:=f)).
             rewrite <- !compose_assoc.
             rewrite H. apply sub_reflexive.
           - unfold sleq. intros V.
             rewrite <- (inv_dir_is_id (f:=f)).
             rewrite <- !compose_assoc.
             rewrite H. apply sub_reflexive.
             Grab Existential Variables.
             esplit. apply Ef. esplit. apply Ef.
    Defined.

    Lemma coparallel_open_map : forall {A B C D} (f : A ~~> B) (g : C ~~> D),
        OpenMap f -> OpenMap g -> OpenMap (coparallel f g).
    Proof. intros A B C D f g Of Og.
           unshelve esplit.
           - intros V.
             apply copair.
             apply (dir_img (V ∘ inl)).
             apply (dir_img (V ∘ inr)).
           - intros V V' H. simpl.
             apply sub_sum. rewrite !copair_inl.
             apply dir_monotone. apply sub_ext. assumption. rewrite !copair_inr.
             apply dir_monotone. apply sub_ext. assumption.
           - intros V W. simpl. split.
             + intros H. unfold inv_img.
               apply sub_sum.
               rewrite <- compose_assoc, -> coparallel_inl.
               apply (sub_ext inl) in H.
               rewrite copair_inl in H.
               apply adjointness in H. unfold inv_img in H.
               rewrite compose_assoc.
               apply H.
               rewrite <- compose_assoc, -> coparallel_inr, -> compose_assoc.
               apply (sub_ext inr) in H. rewrite copair_inr in H.
               apply adjointness in H. unfold inv_img in H. apply H.
             + intros H. unfold inv_img in H. apply sub_sum.
               rewrite copair_inl. apply (sub_ext inl) in H.
               rewrite <- compose_assoc, -> coparallel_inl, -> compose_assoc in H.
               apply adjointness. apply H.
               rewrite copair_inr. apply (sub_ext inr) in H.
               rewrite <- compose_assoc, -> coparallel_inr, -> compose_assoc in H.
               apply adjointness. apply H.
    Defined.

    Lemma coparallel_open_embedding : forall {A B C D} (f : A ~~> B) (g : C ~~> D),
        OpenEmbedding f -> OpenEmbedding g -> OpenEmbedding (coparallel f g).
    Proof. intros A B C D f g [Of Ef] [Og Eg].
           unshelve esplit.
           - apply coparallel_open_map. assumption. assumption.
           - intros V. specialize (Ef (V ∘ inl)). specialize (Eg (V ∘ inr)).
             apply sub_sum.
             + eapply sub_Proper. Focus 3. apply Ef.
               unfold inv_img. rewrite <- compose_assoc, -> coparallel_inl.
               remove_eq_right.
               unfold dir_img at 1. unfold coparallel_open_map.
               rewrite copair_inl. reflexivity. reflexivity.
             + eapply sub_Proper. Focus 3. apply Eg.
               unfold inv_img. rewrite <- compose_assoc, -> coparallel_inr.
               remove_eq_right.
               unfold dir_img at 1. unfold coparallel_open_map.
               rewrite copair_inr. reflexivity. reflexivity.
    Defined.

             
  End Category.

  Section Lift.

    Context `{lps : LiftProps(U:=U)(ccat:=ccat)(cmc:=cmc)(sts:=sts)(Σ:=Σ)}.

    Axiom sub_lift : forall {A} (f f' : Lift A ~~> Σ),
        sub (f ∘ bottom) (f' ∘ bottom) -> sub (f ∘ strict) (f' ∘ strict) -> sub f f'.

    Axiom sub_Σ : forall (f f' : Σ ~~> Σ),
        sub (f ∘ false) (f' ∘ false) -> sub (f ∘ true) (f' ∘ true) -> sub f f'.

    Lemma strict_open_embedding : forall {A}, OpenEmbedding (strict (A:=A)).
    Proof. intros A.
           unshelve esplit.
           unshelve esplit.
           - intros f. unshelve eapply lift_rec.
             exact false. exact f. intros a; apply false_sleq_anything.
           - intros V V' H. simpl.
             apply sub_lift.
             rewrite !lift_rec_bottom. apply sub_reflexive.
             rewrite !lift_rec_strict. assumption.
           - intros V W. simpl. split.
             + intros H. unfold inv_img.
               apply (sub_ext strict) in H.
               eapply sub_Proper. Focus 3. apply H.
               erewrite lift_rec_strict. reflexivity.
               reflexivity.
             + intros H. unfold inv_img.
               apply sub_lift.
               rewrite lift_rec_bottom.
               rewrite <- (compose_id_right) at 1.
               rewrite (unit_uniq id tt). apply false_smallest.
               rewrite lift_rec_strict. assumption.
           - intros V. unfold inv_img, dir_img. erewrite lift_rec_strict.
             apply sub_reflexive.
    Defined.
    
  End Lift.

  
  Section Cantor.

    Context `{stros : StreamOps (U:=U)(ccat:=ccat)}{strps : StreamProps}.
    
    Let Boole := unit + unit.
    Let Cantor := Stream Boole.

    Lemma Cons_Zero_OpenEmbedding :
        OpenEmbedding (cons (inl(B:=unit) ∘ tt) id).
    Proof. unshelve esplit.  unshelve esplit.
           - refine (fun V => _).
             refine (_ ∘ ⟨tl, hd⟩).
             unfold Boole. eapply sum_elim.
             apply (V ∘ fst).
             apply (false ∘ tt ∘ fst).
           - intros V V' H.
             simpl.
             apply sub_ext.
             apply sub_sum'.
             + rewrite !sum_elim_inl. apply sub_ext. assumption.
             + rewrite !sum_elim_inr. apply sub_reflexive.
           - intros V W.
             simpl. split.
             + intros H.
               unfold inv_img.
               apply (sub_ext (cons (inl ∘ tt) id)) in H.
               eapply sub_Proper. Focus 3. apply H.
               rewrite <- compose_assoc, -> pair_f.
               rewrite cons_hd, cons_tl'.
               rewrite pair_parallel_id, compose_assoc, sum_elim_inl.
               rewrite <- compose_assoc, -> pair_fst, -> compose_id_right.
               reflexivity.
               reflexivity.
             + intros H.
               unfold inv_img in H.
               assert (cons(A:=Boole) snd fst ∘ ⟨tl, hd⟩ == id).
               {
                 apply stream_bisim.
                 intros n. destruct n.
                 - simpl. rewrite compose_assoc.  rewrite cons_hd. rewrite pair_snd.
                   rewrite compose_id_right. reflexivity.
                 - simpl. rewrite <- compose_assoc, -> (compose_assoc _ (cons _ _)).
                   rewrite cons_tl', pair_fst, compose_id_right. reflexivity.
               } unfold Boole in H0.
               rewrite <- (compose_id_right W). rewrite <- H0. clear H0.
               rewrite !compose_assoc. apply sub_ext.
               apply sub_sum'.
               * rewrite sum_elim_inl.
                 rewrite <- compose_assoc, -> cons_ext.
                 eapply sub_Proper. reflexivity. etransitivity. 
                 apply compose_Proper. reflexivity. etransitivity. apply cons_Proper.
                 etransitivity. etransitivity. apply parallel_snd. apply compose_Proper.
                 reflexivity. apply (unit_uniq snd (tt ∘ fst)). apply compose_assoc.
                 apply parallel_fst.
                 symmetry. apply cons_ext. apply compose_assoc.
                 apply sub_ext. assumption.
               * rewrite sum_elim_inr.
                 eapply sub_Proper. Focus 3. eapply false_smallest.
                 remove_eq_left. apply unit_uniq.
                 reflexivity.
           - intros V. unfold inv_img, dir_img.
             eapply sub_Proper. Focus 3. apply (sub_reflexive V).
             rewrite <- compose_assoc. rewrite pair_f.
             rewrite cons_hd. rewrite cons_tl'.
             rewrite pair_parallel_id. rewrite compose_assoc.
             rewrite sum_elim_inl. rewrite <- compose_assoc. rewrite pair_fst.
             rewrite compose_id_right. reflexivity. reflexivity.
    Defined.
    
    Lemma Cons_One_OpenEmbedding :
        OpenEmbedding (cons (inr(A:=unit) ∘ tt) id).
    Proof. unshelve esplit.  unshelve esplit.
           - refine (fun V => _).
             refine (_ ∘ ⟨tl, hd⟩).
             unfold Boole. eapply sum_elim.
             apply (false ∘ tt ∘ fst).
             apply (V ∘ fst).
           - intros V V' H.
             simpl.
             apply sub_ext.
             apply sub_sum'.
             + rewrite !sum_elim_inl. apply sub_reflexive.
             + rewrite !sum_elim_inr. apply sub_ext. assumption.
           - intros V W.
             simpl. split.
             + intros H.
               unfold inv_img.
               apply (sub_ext (cons (inr ∘ tt) id)) in H.
               eapply sub_Proper. Focus 3. apply H.
               rewrite <- compose_assoc, -> pair_f.
               rewrite cons_hd, cons_tl'. 
               rewrite pair_parallel_id, compose_assoc, sum_elim_inr.
               rewrite <- compose_assoc, -> pair_fst, -> compose_id_right.
               reflexivity.
               reflexivity.
             + intros H.
               unfold inv_img in H.
               assert (cons(A:=Boole) snd fst ∘ ⟨tl, hd⟩ == id).
               {
                 apply stream_bisim.
                 intros n. destruct n.
                 - simpl. rewrite compose_assoc.  rewrite cons_hd. rewrite pair_snd.
                   rewrite compose_id_right. reflexivity.
                 - simpl. rewrite <- compose_assoc, -> (compose_assoc _ (cons _ _)).
                   rewrite cons_tl', pair_fst, compose_id_right. reflexivity.
               } unfold Boole in H0.
               rewrite <- (compose_id_right W). rewrite <- H0. clear H0.
               rewrite !compose_assoc. apply sub_ext.
               apply sub_sum'.
               * rewrite sum_elim_inl.
                 eapply sub_Proper. Focus 3. eapply false_smallest.
                 remove_eq_left. apply unit_uniq.
                 reflexivity.
               * rewrite sum_elim_inr.
                 rewrite <- compose_assoc, -> cons_ext.
                 eapply sub_Proper. reflexivity. etransitivity. 
                 apply compose_Proper. reflexivity. etransitivity. apply cons_Proper.
                 etransitivity. etransitivity. apply parallel_snd. apply compose_Proper.
                 reflexivity. apply (unit_uniq snd (tt ∘ fst)). apply compose_assoc.
                 apply parallel_fst.
                 symmetry. apply cons_ext. apply compose_assoc.
                 apply sub_ext. assumption.
           - intros V. unfold inv_img, dir_img.
             eapply sub_Proper. Focus 3. apply (sub_reflexive V).
             rewrite <- compose_assoc. rewrite pair_f.
             rewrite cons_hd. rewrite cons_tl'.
             rewrite pair_parallel_id. rewrite compose_assoc.
             rewrite sum_elim_inr. rewrite <- compose_assoc. rewrite pair_fst.
             rewrite compose_id_right. reflexivity. reflexivity.
    Defined.
    
  End Cantor.

  Section UTest.

    Local Definition f : unit + unit ~~> unit :=
      copair id id.

    Local Definition fopen : OpenMap f.
    Proof. unshelve esplit.
           - intros V.
             refine (or ∘ ⟨_, _⟩).
             + exact (V ∘ inl).
             + exact (V ∘ inr).
           - intros V V' H. simpl.
             apply sub_or_C.
             + eapply sub_transitive.
               apply sub_ext. apply H.
               apply sub_or_L.
             + eapply sub_transitive.
               apply sub_ext. apply H.
               apply sub_or_R.
           - intros V W. simpl.
             split.
             + intros H. unfold inv_img, f.
               assert (W ∘ copair id id == copair W W) as K.
               { apply inj_eq; rewrite <- compose_assoc; rewrite ?copair_inl, ?copair_inr;
                   rewrite compose_id_right; reflexivity. }
               rewrite K. clear K.
               assert (V == copair (V ∘ inl) (V ∘ inr)) as K'.
               { apply inj_eq; rewrite ?copair_inl, ?copair_inr; reflexivity. }
               rewrite K'. clear K'.
               apply sub_sum.
               * rewrite !copair_inl.
                 eapply sub_transitive.
                 eapply sub_or_L. apply H.
               * rewrite !copair_inr.
                 eapply sub_transitive.
                 eapply sub_or_R. apply H.
             + intros H. unfold inv_img, f in H.
               apply sub_or_C.
               * apply (sub_ext inl) in H.
                 rewrite <- compose_assoc, copair_inl, compose_id_right in H.
                 apply H.
               * apply (sub_ext inr) in H.
                 rewrite <- compose_assoc, copair_inr, compose_id_right in H.
                 apply H.
    Defined.

    
    (* This is actually a non-example. *)    
    Local Definition fopenemb : OpenEmbedding f.
    Proof. unshelve esplit. apply fopen.
           assert (~(forall U0, sub (inv_img f (dir_img (OpenMap:=fopen) U0)) U0)).
           { (* ie we're proving the negation of the current goal *)
             unfold Logic.not. intros.
             specialize (H (copair true false)). (* an open not in the image of `inv_img f` *)
             unfold inv_img, f, dir_img in H. simpl in H.
             rewrite copair_inr in H.
             apply (sub_ext inr) in H. (* we pick a point that reveals the sets are different *)
             rewrite <- compose_assoc, !copair_inr, copair_inl, compose_id_right in H.
             pose (fun Γ => or_true(Γ:=Γ)) as K.
             unfold ap2, ap0 in K.
             rewrite <- (compose_id_right true), -> (unit_uniq id tt) in H.
             rewrite K in H; clear K.
             rewrite (unit_uniq tt id), compose_id_right in H.
             (* Now we have that true is a subset of false 
                (ie the top open of Σ is contained in the bottom open). 
                This is clearly a contradiction. *)
             admit. }
    Abort.
    
  End UTest.

  Section Equiv.

    Context `{lps : LiftProps(U:=U)(ccat:=ccat)(cmc:=cmc)(sts:=sts)(Σ:=Σ)}.
    
    Definition Equiv_to_obj : forall {A}, (A ~~> Σ) -> U.
    Proof. intros A V. eapply pb.
           apply V.
           apply true.
    Defined.

    Definition Equiv_to_mor : forall {A} (f : A ~~> Σ), (Equiv_to_obj f) ~~> A.
    Proof. intros A f. unfold Equiv_to_obj. apply pb_fst.
    Defined.

    Axiom semi_if : forall {A} (f : A ~~> Σ), A ~~> Lift (Equiv_to_obj f).
    (* Sends the points such that f(x) == true to strict x, sends the other points to bottom. *)
    Axiom semi_if_in : forall {A} (f : A ~~> Σ), semi_if f ∘ Equiv_to_mor f == strict.

    Definition Equiv_to_emb : forall {A} (f : A ~~> Σ), OpenEmbedding (Equiv_to_mor f).
    Proof. intros A f. unshelve esplit. unshelve esplit.
           - intros g.
             refine (_ ∘ semi_if f).
             unshelve eapply lift_rec. exact false.
             exact g. intros a; apply false_sleq_anything.
           - intros V V' H. simpl.
             apply sub_ext.
             apply sub_lift.
             rewrite !lift_rec_bottom. apply sub_reflexive.
             rewrite !lift_rec_strict. assumption.
           - intros V W. simpl. split.
             + intros H. unfold inv_img.
               apply (sub_ext (Equiv_to_mor f)) in H.
               eapply sub_Proper. Focus 3. apply H.
               rewrite <- compose_assoc, -> semi_if_in.
               erewrite lift_rec_strict. reflexivity.
               reflexivity.
             + intros H. unfold inv_img in H.
               admit. (* The proof of this seems too excluded-middle-y.
                         basically if you have x, you compute f(x). if it is true the goal 
                         reduces to H via semi_if_in, if it is false then you are done because false is  
                         smallest. *)
           - intros V. unfold inv_img, dir_img.
             eapply sub_Proper.
             rewrite <- compose_assoc. rewrite semi_if_in. rewrite lift_rec_strict. reflexivity.
             reflexivity. apply sub_reflexive.
    Admitted.

    Definition Equiv_from : forall {A B} {f : B ~~> A}, OpenEmbedding f -> A ~~> Σ.
    Proof. intros A B f e.
           unshelve eapply dir_img. eapply B. eapply f. eapply e.
           apply (true ∘ tt).
    Defined.

    Definition to_from_obj : forall {A B} {f : B ~~> A} {e : OpenEmbedding f},
        (Equiv_to_obj (Equiv_from e)) ≅ B.
    Proof. intros A B f [o e]. unshelve eapply Build_Iso.
           admit.
           unfold Equiv_from, Equiv_to_obj. unshelve eapply pb_Exists.
           apply f. apply tt. etransitivity. Focus 2. eapply inv_dir_is_id.
           reflexivity.
           admit.
           admit.
    Admitted.    
        
  End Equiv.
  
  
End OpenEmbeddings.