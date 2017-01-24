Require Import Spec.Category Spec.Sum.

Import Morphisms Category Sum.
Local Open Scope obj.
Local Open Scope morph.

Module Pullback.
  Section Pullback.

    Context {U : Type} {ccat : CCat U} {cmc : CMC U} {cmp : CMC_Props U}.
    
    Definition Pullback {A B C D} (e : A ~~> B) (f : B ~~> D) (g : A ~~> C) (h : C ~~> D) : Type :=
      Datatypes.prod
        (Datatypes.prod (f ∘ e == h ∘ g) (Mono ⟨e, g⟩)) (* The monomorphism condition is 
      supposed to be equivalent to requiring that the morphism i below is unique. 
      It may be stronger, but I don't think so. *)
      (forall {X} (j : X ~~> B) (k : X ~~> C), f ∘ j == h ∘ k ->
                                      {i : X ~~> A | e ∘ i == j /\ g ∘ i == k}).

    Definition Pullback_Comm : forall  {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h ->
        f ∘ e == h ∘ g :=
      fun _ _ _ _ _ _ _ _ H => (Datatypes.fst (Datatypes.fst H)).
    Definition Pullback_Uniq : forall  {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h ->
        Mono ⟨e, g⟩ :=
      fun _ _ _ _ _ _ _ _ H => (Datatypes.snd (Datatypes.fst H)).
    Definition Pullback_Exists : forall  {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h ->
        forall {X : U} (j : X ~~> B) (k : X ~~> C), f ∘ j == h ∘ k -> X ~~> A :=
      fun _ _ _ _ _ _ _ _ H _ j k K => (proj1_sig ((Datatypes.snd H) _ j k K)).
    Definition Pullback_Exists_left : forall  {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        forall (H : Pullback e f g h),
        forall {X : U} (j : X ~~> B) (k : X ~~> C) (K : f ∘ j == h ∘ k),
          e ∘ (Pullback_Exists H j k K) == j :=
      fun _ _ _ _ _ _ _ _  H X j k K => proj1 (proj2_sig (Datatypes.snd H X j k K)).
    Definition Pullback_Exists_right : forall  {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        forall (H : Pullback e f g h),
        forall {X : U} (j : X ~~> B) (k : X ~~> C) (K : f ∘ j == h ∘ k),
          g ∘ (Pullback_Exists H j k K) == k :=
      fun _ _ _ _ _ _ _ _  H X j k K => proj2 (proj2_sig (Datatypes.snd H X j k K)).
    Definition Pullback_Corner : forall {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h -> U
      := fun A _ _ _ _ _ _ _ _ => A.

    Axiom pb : forall {B C D} (f : B ~~> D) (h : C ~~> D), U.
    Axiom pb_fst : forall {B C D} (f : B ~~> D) (h : C ~~> D), (pb f h) ~~> B.
    Axiom pb_snd : forall {B C D} (f : B ~~> D) (h : C ~~> D), (pb f h) ~~> C.
    Axiom pb_Comm : forall {B C D} (f : B ~~> D) (h : C ~~> D), f ∘ (pb_fst f h) == h ∘ (pb_snd f h).
    Axiom pb_Uniq : forall {B C D} (f : B ~~> D) (h : C ~~> D), Mono ⟨pb_fst f h, pb_snd f h⟩.
    Axiom pb_Exists : forall {B C D} (f : B ~~> D) (h : C ~~> D),
        forall {X : U} (j : X ~~> B) (k : X ~~> C), f ∘ j == h ∘ k -> X ~~> pb f h.
    Arguments pb_Exists {B} {C} {D} {f} {h} {X} j k.
    Axiom pb_Exists_left : forall  {B C D} (f : B ~~> D) (h : C ~~> D),
        forall {X : U} (j : X ~~> B) (k : X ~~> C) (H : f ∘ j == h ∘ k),
        (pb_fst f h) ∘ (pb_Exists j k H) == j.
    Axiom pb_Exists_right : forall  {B C D} (f : B ~~> D) (h : C ~~> D),
        forall {X : U} (j : X ~~> B) (k : X ~~> C) (H : f ∘ j == h ∘ k),
        (pb_snd f h) ∘ (pb_Exists j k H) == k.
    Lemma pb_is_Pullback : forall {B C D} (f : B ~~> D) (h : C ~~> D),
        Pullback (pb_fst f h) f (pb_snd f h) h.
    Proof. intros B C D f h.
           unfold Pullback. repeat (try split; try unshelve eexists).
           - apply pb_Comm.
           - apply pb_Uniq.
           - apply (pb_Exists j k H).
           - apply (pb_Exists_left f h j k H).
           - apply (pb_Exists_right f h j k H).
    Qed.
             
    Lemma Pullback_unique : forall {A B C D} (e : A ~~> B) (f : B ~~> D) (g : A ~~> C) (h : C ~~> D),
        Pullback e f g h -> A ≅ pb f h.
    Proof. intros A B C D e f g h H.
           unshelve eapply Build_Iso.
           - unshelve eapply pb_Exists.
             + apply e.
             + apply g.
             + apply (Pullback_Comm H).
           - unshelve eapply (Pullback_Exists H).
             + apply pb_fst.
             + apply pb_snd.
             + apply pb_Comm.
           - unshelve eapply pb_Uniq.
             rewrite !pair_f.
             rewrite !compose_assoc.
             rewrite pb_Exists_left, pb_Exists_right.
             rewrite (Pullback_Exists_left H), (Pullback_Exists_right H).
             rewrite !compose_id_right. reflexivity.
           - unshelve eapply (Pullback_Uniq H).
             rewrite !pair_f.
             rewrite !compose_assoc.
             rewrite (Pullback_Exists_left H), (Pullback_Exists_right H).
             rewrite pb_Exists_left, pb_Exists_right.             
             rewrite !compose_id_right. reflexivity.
    Defined.

    Existing Instance Mono_Proper.
    
    Lemma Pullback_unique_converse : forall {A B C D} (f : B ~~> D) (h : C ~~> D) (s : A ≅ pb f h),
        Pullback ((pb_fst f h) ∘ to s) f (pb_snd f h ∘ to s) h.
    Proof. intros A B C D f h s.
           split; try split.
           - remove_eq_right.
             apply pb_Comm.
           - rewrite <- pair_f. apply Mono_Compose.
             + apply Iso_Mono.
             + apply pb_Uniq.
           - intros. exists ((from s) ∘ (pb_Exists j k H)).
             split.
             + rewrite <- !compose_assoc; rewrite (compose_assoc _ (from s)).
               rewrite (to_from s), compose_id_left.
               rewrite pb_Exists_left. reflexivity.
             + rewrite <- !compose_assoc; rewrite (compose_assoc _ (from s)).
               rewrite (to_from s), compose_id_left.
               rewrite pb_Exists_right. reflexivity.
    Qed.

    Lemma Pullback_Proper : forall {A B C D}
                              {e0 e1 : A ~~> B} {f0 f1 : B ~~> D} {g0 g1 : A ~~> C} {h0 h1 : C ~~> D},
        e0 == e1 -> f0 == f1 -> g0 == g1 -> h0 == h1 ->
        Pullback e1 f1 g1 h1 ->
        Pullback e0 f0 g0 h0.
    Proof. intros A B C D e0 e1 f0 f1 g0 g1 h0 h1 e f g h H.
           split; try split.
           - rewrite e, f, g, h. apply (Pullback_Comm H).
           - eapply Mono_Proper. try eapply pair_Proper.
             exact e. exact g. apply (Pullback_Uniq H).
           - intros. rewrite f, h in H0. exists (Pullback_Exists H j k H0).
             split.
             + rewrite e. apply (Pullback_Exists_left H).
             + rewrite g. apply (Pullback_Exists_right H).
    Qed.


        
    
    Context {sts : SumTys (U:=U)}{sos : SumOps}{sps : SumProps}.

    Lemma pb_Proper : forall {A B C} (f0 f1 : A ~~> C) (g0 g1 : B ~~> C),
        (f0 == f1) -> (g0 == g1) -> (pb f0 g0) ≅ (pb f1 g1).
    Proof. intros A B C f0 f1 g0 g1 f g.
           unshelve eapply Build_Iso.
           - unshelve eapply pb_Exists.
             + apply pb_fst.
             + apply pb_snd.
             + rewrite <- f, <- g. apply pb_Comm.
           - unshelve eapply pb_Exists.
             + apply pb_fst.
             + apply pb_snd.
             + rewrite -> f, -> g. apply pb_Comm.
           - apply pb_Uniq.
             rewrite !pair_f.
             rewrite !compose_assoc.
             rewrite !pb_Exists_left, !pb_Exists_right.
             rewrite !compose_id_right. reflexivity.
           - apply pb_Uniq.
             rewrite !pair_f.
             rewrite !compose_assoc.
             rewrite !pb_Exists_left, !pb_Exists_right.
             rewrite !compose_id_right. reflexivity.
    Defined.

    Lemma pb_sum : forall {A A' B C} (f : A ~~> C) (f' : A' ~~> C) (g : B ~~> C),
        pb f g + pb f' g ~~> pb (copair f f') g.
    Proof. intros A B B' C f f' g.
           unshelve eapply pb_Exists.
           - apply (coparallel (pb_fst f g) (pb_fst f' g)).
           - apply (copair (pb_snd f g) (pb_snd f' g)).
           - apply inj_eq.
             + rewrite <- !compose_assoc.
               rewrite coparallel_inl.
               rewrite (compose_assoc _ inl).
               rewrite !copair_inl.
               apply pb_Comm.
             + rewrite <- !compose_assoc.
               rewrite coparallel_inr.
               rewrite (compose_assoc _ inr).
               rewrite !copair_inr.
               apply pb_Comm.
    Defined.

    Axiom sum_pb : forall {A A' B C} (f : A ~~> C) (f' : A' ~~> C) (g : B ~~> C),
        pb (copair f f') g ~~> pb f g + pb f' g.
    Axiom sum_pb_sum : forall {A A' B C} (f : A ~~> C) (f' : A' ~~> C) (g : B ~~> C),
        (pb_sum f f' g) ∘ (sum_pb f f' g) == id.
    Axiom pb_sum_pb : forall {A A' B C} (f : A ~~> C) (f' : A' ~~> C) (g : B ~~> C),
        (sum_pb f f' g) ∘ (pb_sum f f' g) == id.
    Definition pb_sum_Iso : forall {A A' B C} (f : A ~~> C) (f' : A' ~~> C) (g : B ~~> C),
        pb f g + pb f' g ≅ pb (copair f f') g.
    Proof. intros A B B' C f f' g.
           unshelve eapply Build_Iso.
           apply pb_sum. apply sum_pb. apply sum_pb_sum. apply pb_sum_pb.
    Defined.

    Lemma Pullback_sum : forall {A A' B B' C D}
                           {e : A ~~> B} {e' : A' ~~> B'}
                           {f : B ~~> D} {f' : B' ~~> D}
                           {g : A ~~> C} {g' : A' ~~> C}
                           {h : C ~~> D},
        Pullback e f g h -> Pullback e' f' g' h ->
        Pullback (coparallel e e') (copair f f') (copair g g') h.
    Proof.
      intros A A' B B' C D e e' f f' g g' h H H'.
      pose (Pullback_unique e f g h H) as P.
      pose (Pullback_unique e' f' g' h H') as P'.
      pose (pb_sum_Iso f f' h) as i.
      pose (Iso_Sum P P') as i'.
      pose (Iso_Trans i' i) as j.
      pose (Pullback_unique_converse _ _ j).
      unshelve eapply (Pullback_Proper _ _ _ _ p).
      - unfold j. simpl.
        apply inj_eq.
        + rewrite <- !compose_assoc.
          rewrite !coparallel_inl.
          rewrite !compose_assoc.
          unfold pb_sum; rewrite pb_Exists_left.
          rewrite coparallel_inl.
          remove_eq_left.
          rewrite pb_Exists_left. reflexivity.
        + rewrite <- !compose_assoc.
          rewrite !coparallel_inr.
          rewrite !compose_assoc.
          unfold pb_sum; rewrite pb_Exists_left.
          rewrite coparallel_inr.
          remove_eq_left.
          rewrite pb_Exists_left. reflexivity.
      - reflexivity.
      - unfold j. simpl.
        apply inj_eq.
        + rewrite <- !compose_assoc.
          rewrite !coparallel_inl.
          rewrite !compose_assoc.
          unfold pb_sum; rewrite pb_Exists_right.
          rewrite !copair_inl.
          rewrite pb_Exists_right. reflexivity.
        + rewrite <- !compose_assoc.
          rewrite !coparallel_inr.
          rewrite !compose_assoc.
          unfold pb_sum; rewrite pb_Exists_right.
          rewrite !copair_inr.
          rewrite pb_Exists_right. reflexivity.
      - reflexivity.
    Qed.      

    Lemma pb_Mono_iff : forall {A B} (f : A ~~> B),
        Datatypes.prod (Mono f -> (Pullback id f id f)) ((Pullback id f id f) -> Mono f).
    Proof. intros A B f.
           split.
           - intros M.
             split.
             unfold Pullback. split.
             + reflexivity.
             + unfold Mono. intros.
               rewrite <- (compose_id_left g1), <- (compose_id_left g2).
               rewrite <- !diagonal_fst. unfold diagonal.
               rewrite <- !compose_assoc, -> !H. reflexivity.
             + intros. specialize (M _ _ _ H).
               exists j. split. apply compose_id_left. rewrite M; apply compose_id_left.
           - intros H.
             unfold Mono. intros.
             pose (g := Pullback_Exists H _ _ H0).
             transitivity g.
             + symmetry. rewrite <- (compose_id_left g). apply (Pullback_Exists_left H _ _ H0).
             + rewrite <- (compose_id_left g). apply (Pullback_Exists_right H _ _ H0).
    Qed.



    Lemma coparallel_Mono : forall {A B C D} {f : A ~~> B} {g : C ~~> D},
        Mono f -> Mono g -> Mono (coparallel f g).
    Proof. intros.
           apply pb_Mono_iff. split.
    Abort.

    Lemma pullback_Mono : forall {A B C} (f : A ~~> C) (m : B ~~> C),
        Mono m -> Mono (pb_snd m f).
    Proof. intros A B C f m H.
           unfold Mono. unfold Mono in H. intros X g1 g2 K.
           apply pb_Uniq. rewrite !pair_f. apply proj_eq; rewrite ?pair_fst, ?pair_snd.
           - apply H. rewrite !compose_assoc. rewrite !pb_Comm.
             rewrite <- !compose_assoc. apply compose_Proper. reflexivity. apply K.
           - apply K.
    Qed.

    Lemma Pullback_A_Iso : forall {A0 A1 B C D}
                             (s : A0 ≅ A1)
                             {e : A0 ~~> B} {f : B ~~> D} {g : A0 ~~> C} {h : C ~~> D},
        Pullback e f g h -> Pullback (e ∘ (from s)) f (g ∘ (from s)) h.
    Proof. intros A0 A1 B C D s e f g h P.
           split; try split; try unshelve eexists.
           - remove_eq_right.
             apply (Pullback_Comm P).
           - unshelve eapply Mono_Proper.
             + apply (⟨e, g⟩ ∘ (from s)).
             + rewrite pair_f. reflexivity.
             + apply Mono_Compose.
               * apply (Iso_Mono (Iso_Sym s)).
               * apply (Pullback_Uniq P).
           - refine ((to s) ∘ _).
             unshelve eapply (Pullback_Exists P).
             + apply j.
             + apply k.
             + apply H.
           - split.
             + rewrite <- compose_assoc, -> (compose_assoc _ (to s)).
               rewrite (from_to s), compose_id_left.
               rewrite (Pullback_Exists_left P).
               reflexivity.
             + rewrite <- compose_assoc, -> (compose_assoc _ (to s)).
               rewrite (from_to s), compose_id_left.
               rewrite (Pullback_Exists_right P).
               reflexivity.
    Qed.

    Lemma Pullback_B_Iso : forall {A B0 B1 C D}
                             (s : B0 ≅ B1)
                             {e : A ~~> B0} {f : B0 ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h -> Pullback ((to s) ∘ e) (f ∘ (from s)) g h.
    Proof. intros A B0 B1 C D s e f g h P.
           split; try split; try unshelve eexists.
           - rewrite <- (compose_assoc _ (from s)), -> (compose_assoc _ (to s)).
             rewrite (from_to s), compose_id_left.
             apply (Pullback_Comm P).
           - unshelve eapply Mono_Proper.
             + apply ((to s) ⊗ id ∘ ⟨e, g⟩).
             + apply proj_eq;
                 rewrite -> !compose_assoc; rewrite ?parallel_fst, ?parallel_snd;
                   rewrite <- !compose_assoc; rewrite ?pair_fst, ?pair_snd;
                     rewrite ?compose_id_left; try reflexivity.
             + apply Mono_Compose.
               * apply (Pullback_Uniq P).
               * apply (Iso_Mono (Iso_Prod s (Iso_Refl (A:=C)))).
           - unshelve eapply (Pullback_Exists P).
             + apply ((from s) ∘ j).
             + apply k.
             + rewrite compose_assoc. apply H.
           - split.
             + rewrite <- compose_assoc.
               rewrite (Pullback_Exists_left P).
               rewrite -> compose_assoc.
               rewrite (to_from s), compose_id_left.
               reflexivity.
             + rewrite (Pullback_Exists_right P).
               reflexivity.
    Qed.
                 

    Lemma Pasting_Small_to_Big : forall
        {A00 A01 A02 A10 A11 A12 : U}
        {f00 : A00 ~~> A01} {f01 : A01 ~~> A02} {f10 : A10 ~~> A11} {f11 : A11 ~~> A12}
        {g0 : A00 ~~> A10} {g1 : A01 ~~> A11} {g2 : A02 ~~> A12},
        (Pullback g1 f11 f01 g2) -> (Pullback g0 f10 f00 g1) ->
        (Pullback g0 (f11 ∘ f10) (f01 ∘ f00) g2).
    Proof. intros A00 A01 A02 A10 A11 A12 f00 f01 f10 f11 g0 g1 g2 P1 P0.
           split; try split; try unshelve eexists.
           - rewrite <- (compose_assoc _ f10), (Pullback_Comm P0).
             remove_eq_right. apply (Pullback_Comm P1).
           - unfold Mono; intros X h0 h1 H.
             rewrite !pair_f in H.
             assert (forall {A B C} (f f' : A ~~> B) (g g' : A ~~> C),
                        ⟨f, g⟩ == ⟨f', g'⟩ -> f == f' /\ g == g') as lemma.
             { split. etransitivity. symmetry. eapply pair_fst.
               rewrite H0. rewrite pair_fst. reflexivity.
               etransitivity. symmetry. eapply pair_snd.
               rewrite H0. rewrite pair_snd. reflexivity. }
             apply lemma in H; clear lemma; destruct H as [H0 H1].
             apply (Pullback_Uniq P0).
             rewrite !pair_f; apply proj_eq; rewrite ?pair_fst, ?pair_snd.
             assumption. apply (Pullback_Uniq P1).
             rewrite !pair_f; apply proj_eq; rewrite ?pair_fst, ?pair_snd.
             rewrite !compose_assoc. rewrite <- !(Pullback_Comm P0).
             rewrite <- !compose_assoc. apply compose_Proper; try reflexivity; assumption.
             rewrite !compose_assoc. assumption.
           - unshelve eapply (Pullback_Exists P0).
             + exact j.
             +  unshelve eapply (Pullback_Exists P1).
                * exact (f10 ∘ j).
                * exact k.
                * rewrite compose_assoc; assumption.
             + rewrite (Pullback_Exists_left P1). reflexivity.
           - split.
             + rewrite (Pullback_Exists_left P0). reflexivity.
             + rewrite <- compose_assoc.
               rewrite (Pullback_Exists_right P0).
               rewrite (Pullback_Exists_right P1). reflexivity.
    Defined.


    Lemma Pasting_Big_to_Small : forall
        {A00 A01 A02 A10 A11 A12 : U}
        {f00 : A00 ~~> A01} {f01 : A01 ~~> A02} {f10 : A10 ~~> A11} {f11 : A11 ~~> A12}
        {g0 : A00 ~~> A10} {g1 : A01 ~~> A11} {g2 : A02 ~~> A12},
        (Pullback g1 f11 f01 g2)  -> f10 ∘ g0 == g1 ∘ f00 -> 
        (Pullback g0 (f11 ∘ f10) (f01 ∘ f00) g2) -> (Pullback g0 f10 f00 g1).
    Proof. intros A00 A01 A02 A10 A11 A12 f00 f01 f10 f11 g0 g1 g2 P1 C P0.
           split; try split; try unshelve eexists.
           - assumption.
           - unfold Mono; intros X h0 h1 H.
             assert (forall {A B C} (f f' : A ~~> B) (g g' : A ~~> C),
                        ⟨f, g⟩ == ⟨f', g'⟩ -> f == f' /\ g == g') as lemma.
             { split. etransitivity. symmetry. eapply pair_fst.
               rewrite H0. rewrite pair_fst. reflexivity.
               etransitivity. symmetry. eapply pair_snd.
               rewrite H0. rewrite pair_snd. reflexivity. }
             rewrite !pair_f in H; apply lemma in H; clear lemma; destruct H as [H0 H1].
             apply (Pullback_Uniq P0).
             rewrite !pair_f; apply proj_eq; rewrite ?pair_fst, ?pair_snd.
             + assumption.
             + rewrite <- compose_assoc; rewrite H1. apply compose_assoc.
           - unshelve eapply (Pullback_Exists P0).
             + exact j.
             + exact (f01 ∘ k).
             + rewrite <- compose_assoc, -> H. remove_eq_right.
               apply (Pullback_Comm P1).
           - split.
             + rewrite (Pullback_Exists_left P0). reflexivity.
             + apply (Pullback_Uniq P1).
               rewrite !pair_f; apply proj_eq; rewrite ?pair_fst, ?pair_snd.
               * rewrite !compose_assoc. rewrite <- C. rewrite <- !compose_assoc.
                 rewrite (Pullback_Exists_left P0). assumption.
               * rewrite !compose_assoc. rewrite (Pullback_Exists_right P0). reflexivity.
    Defined.

    Lemma Pullback_Commutes : forall {A B C D} {e : A ~~> B} {f : B ~~> D} {g : A ~~> C} {h : C ~~> D},
        Pullback e f g h -> Pullback g h e f.
    Proof. intros A B C D e f g h P.
           split; try split; try unshelve eexists.
           - symmetry. apply (Pullback_Comm P).
           - assert (⟨g, e⟩ == swap ∘ ⟨e, g⟩) as H.
             { unfold swap. rewrite pair_f, pair_fst, pair_snd. reflexivity. }
             rewrite H; clear H.
             apply Mono_Compose.
             + apply (Pullback_Uniq P).
             + pose (Iso_Mono (Iso_Prod_Symm(A:=B)(B:=C))) as M.
               apply M.
           - unshelve eapply (Pullback_Exists P).
             + exact k.
             + exact j.
             + symmetry. assumption.
           - split.
             + apply (Pullback_Exists_right P).
             + apply (Pullback_Exists_left P).
    Defined.
    
    (* Putting this here because when it is implemented, pullbacks will be necessary.  *)
    (* The "obvious" implementation of it is not provable given current axioms;
       we need some version of "pullbacks commute with coproducts". *)
    (* Axiom split_obj_L : forall {A B C} (f : A ~~> B + C), U.
    Axiom split_obj_R : forall {A B C} (f : A ~~> B + C), U.
    Axiom split_mor_L : forall {A B C} (f : A ~~> B + C), (split_obj_L f ~~> B).
    Axiom split_mor_R : forall {A B C} (f : A ~~> B + C), (split_obj_R f ~~> C).
    Axiom split_decompose : forall {A B C} (f : A ~~> B + C), A ≅ (split_obj_L f) + (split_obj_R f).
    Definition split_inj_L : forall {A B C} (f : A ~~> B + C), (split_obj_L f) ~~> A :=
      fun _ _ _ f => (from (split_decompose f)) ∘ inl.
    Definition split_inj_R : forall {A B C} (f : A ~~> B + C), (split_obj_R f) ~~> A :=
          fun _ _ _ f => (from (split_decompose f)) ∘ inr.
    Axiom split_reassemble_L : forall {A B C} (f : A ~~> B + C),
        f ∘ split_inj_L f == inl ∘ split_mor_L f.
    Axiom split_reassemble_R : forall {A B C} (f : A ~~> B + C),
        f ∘ split_inj_R f == inr ∘ split_mor_R f.
    Lemma split_reassemble : forall {A B C} (f : A ~~> B + C),
        f == (coparallel (split_mor_L f) (split_mor_R f)) ∘ (to (split_decompose f)).
    Proof. intros A B C f.
           apply (Iso_Epi (Iso_Sym (split_decompose f))).
           rewrite <- compose_assoc. unfold Iso_Sym; simpl.
           rewrite (to_from (split_decompose f)). rewrite compose_id_right.
           apply inj_eq.
           rewrite <- compose_assoc. rewrite split_reassemble_L.
           rewrite coparallel_inl. reflexivity.
           rewrite <- compose_assoc. rewrite split_reassemble_R.
           rewrite coparallel_inr. reflexivity.
    Qed. *)
    
  End Pullback.
End Pullback.


