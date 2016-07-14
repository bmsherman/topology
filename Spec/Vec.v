Require Import Spec.Category Spec.Stream Spec.Discrete Spec.Sum.
Import Category. Import Stream. Import Discrete. Import Sum.
Local Open Scope obj.
Local Open Scope morph.

Module Vec.
  Section vec.
    
    Context {U : Type} {disc : Type -> U} {pow : Type -> U -> U} {ccat : CCat U} {cmc : CMC U}.
    Context `{sos : StreamOps (U:=U) (ccat:=ccat)}.
    Context {cmp : CMC_Props U}.
    Context {dos : DiscreteOps disc pow}.
    Context {sps : StreamProps}.
    Context {dps : DiscreteProps disc pow}.
    Context `{suos : SumOps (U:=U) (ccat:=ccat)}.
    Context {sups : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc)}.
    
    Notation "A ~> B" := (pow A B) (at level 40).
    
    Arguments pow_app1 {U} {ccat} {cmc} {D} {power} {_} {X} {A} x.
    Arguments pow_app2 {U} {ccat} {cmc} {D} {power} {_} {A} {B}.
    Arguments pmap {U} {ccat} {cmc} {D} {power} {_} {X} {Y} {A} {B} f g.
    Arguments pow_app1' {U} {ccat} {cmc} {D} {power} {_} {A} {X} {B} f x.
    Arguments pow_app2' {U} {ccat} {cmc} {D} {power} {_} {X} {A} {B} f.
    Arguments app12 {U} {ccat} {cmc} {D} {power} {H} {_} {A} {X} {B} f x.
    Arguments app21 {U} {ccat} {cmc} {D} {power} {H} {_} {A} {X} {B} f.
    Arguments pmap_Proper' {U} {ccat} {cmc} {D} {power} {H} {_} {X} {A} {B} {C} {D0}  _ _ y0 x0  _ _.
    Arguments pow_app2'_pre {U} {ccat} {cmc} {D} {power} {H} {_} {X} {A} {A'} {B} {f} {g}.

    Notation "'dλ' x => h" := (pow_app2' (power:=pow) (fun x => h)) (at level 20).
    
    Section Stream'.
      
      Definition Stream' : U -> U :=
        fun A => nat ~> A.
      
      Definition idx' {A : U} : nat -> Stream' A ~~> A :=
        pow_app1.
      
      Definition hd' {A : U} : Stream' A ~~> A :=
        idx' 0.

      Definition tl' {A : U} : Stream' A ~~> Stream' A :=
        dλ n => idx' (S n).
      
      Definition Stream'Stream {A : U} : (Stream' A) ~~> (Stream A) :=
        stream id ⟨hd', tl'⟩. (* X := Stream' A. *)
      
      Definition StreamStream' {A : U} : (Stream A) ~~> (Stream' A) :=
        dλ n => idx n.
      
      Notation "A === B" := (pb_eq A B) (at level 60).
      
      Lemma idx'_dλ : forall {A B : U} (f : nat -> (A ~~> B)), (fun n : nat => idx' n ∘ dλ m => f m) === f.
      Proof. intros A B f.
           apply app12.
      Defined.
      
      Theorem idx'_eval :  forall {A B : U} (f : nat -> (A ~~> B)) (n : nat), idx' n ∘ dλ m => f m == f n.
      Proof.
        intros A B f n.
        pose proof (idx'_dλ f) as H.
        apply (H n).
      Defined.
      
      
      Theorem hd'_hd : forall {A : U}, hd' ∘ StreamStream' (A:=A)  == hd.
      Proof.
        intros A.
        unfold hd', StreamStream'.
        apply (idx'_eval (fun n => idx n) 0).
      Defined.
      
      Theorem hd_hd' : forall {A : U}, hd ∘ Stream'Stream (A:=A) == hd'.
      Proof.
        intros A.
        unfold Stream'Stream.
        rewrite stream_hd. rewrite pair_fst.
        rewrite compose_id_right.
        reflexivity.
      Defined.
      
      Theorem  tl_tl' : forall {A : U}, tl ∘ Stream'Stream (A:=A) == Stream'Stream ∘ tl'.
      Proof.
        intros A.
        unfold Stream'Stream.
        rewrite stream_tl.
        etransitivity. apply stream_Proper.
        rewrite pair_snd. rewrite compose_id_right, <- compose_id_left. reflexivity. reflexivity.
        apply stream_ext1.
      Defined.
      
      Theorem idx_idx' : forall {A : U} {n}, idx n ∘ Stream'Stream (A:=A) == idx' n.
      Proof. intros A n.
             induction n.
             - simpl. rewrite hd_hd'. reflexivity.
             - simpl.
               rewrite <- compose_assoc, tl_tl'.
               rewrite compose_assoc, IHn.
               unfold tl'. rewrite idx'_eval.
               reflexivity.
      Defined.
      
      Theorem idx'_idx : forall {A : U} {n}, idx' n ∘ StreamStream' (A:=A) == idx n.
      Proof.
        intros A n.
        unfold StreamStream'.
        rewrite idx'_eval.
        reflexivity.
      Defined.
      
      Theorem StreamStream : forall {A : U}, Stream'Stream ∘ StreamStream' == id (A:=Stream A).
      Proof.
        intros A.
        apply stream_bisim.
        intros n.
        rewrite compose_assoc, idx_idx'.
        rewrite compose_id_right, idx'_idx.
        reflexivity.
      Qed.
      
      Theorem stream'_bisim {Γ A : U} : forall x y : Γ ~~> Stream' A,
          (forall n : nat, idx' n ∘ x == idx' n ∘ y) -> x == y.
      Proof.
        intros x y H.
        rewrite <- (app21 x), <- (app21 y).
        unfold idx' in H. unfold pow_app1'.
        unfold pow_app2'.
        apply compose_Proper; try reflexivity.
        apply pmap_Proper'; try reflexivity.
        unfold pb_eq. intros.
        apply (H x0).
      Qed.
      
      Theorem Stream'Stream' : forall {A : U}, StreamStream' ∘ Stream'Stream == id (A:=Stream' A).
      Proof.
        intros A.
        apply stream'_bisim.
        intros n.
        rewrite compose_assoc, idx'_idx.
        rewrite compose_id_right, idx_idx'.
        reflexivity.
      Qed.
      
    End Stream'.
    
    Section Fin.
      Require Types.Finite.
      Import Finite.
            
      Fixpoint Vec (n : nat) : U -> U :=
        fun A => match n with | 0 => unit | (S m) => A * Vec m A end.
      (* fun n A => (Fin n) ~> A. *)

      Definition to_nat : forall {n : nat}, (Fin n) -> nat.
      Proof. intros. induction n.
             - inversion H.
             - simpl in H. destruct H as [r | l].
               + exact 0.
               + exact (S (IHn l)).
      Defined.

      
      Definition vdx (n : nat) (i : Fin n) : forall {A}, Vec n A ~~> A.
      Proof. intros A. induction n. induction i. induction i. induction a.
             exact fst.
             exact ((IHn b) ∘ snd).
      Defined.

      Theorem Vec0_unit : forall {A}, Vec 0 A ≅ unit.
      Proof. intros A. apply Iso_Refl.
      Defined.
      
      (*  Definition prefix' {A : U} : forall (n : nat),  Stream' A ~~> Vec n A :=
        fun (n : nat) => pmap to_nat id. *) 

      (* Definition prefix0 {A : U} : forall (n : nat), Stream A ~~> Vec n A :=
        fun n => prefix' n ∘ StreamStream'. *)

      Definition prefix {A : U} : forall (n : nat), Stream A ~~> Vec n A.
      Proof. intros n. induction n as [| n Pn].
             exact tt.
             exact ⟨hd, Pn ∘ tl⟩.
      Defined.

      Definition vsqueeze {A B} {n} : Vec n A * Vec n B ~~> Vec n (A * B).
      Proof. induction n.
             - exact tt.
             - exact ⟨fst ⊗ fst, IHn ∘ (snd ⊗ snd)⟩.
      Defined.

      Theorem squeeze_vsqueeze  : forall {A B} (n : nat),
          (prefix n) ∘ squeeze(A:=A)(B:=B) == vsqueeze ∘ ((prefix n) ⊗ (prefix n)).
      Proof. intros A B n.
             induction n.
             - (* 0 *) simpl.  rewrite !unit_uniq. symmetry. apply unit_uniq.
             - (* S _ *) simpl.
                         rewrite !pair_f.
                         rewrite <- (compose_assoc _ _ vsqueeze).
                         rewrite !parallel_compose.
                         rewrite !pair_fst.
                         rewrite !pair_snd.
                         apply pair_Proper.
                         apply squeeze_hd.
                         rewrite <- parallel_compose.
                         rewrite compose_assoc.
                         rewrite <- IHn.
                         remove_eq_left.
                         apply squeeze_tl.
      Qed.

      Fixpoint vnzip {n} {A} : Vec (n * 2) A ~~> Vec n A * Vec n A :=
        match n with
        | O => ⟨tt, tt⟩
        | (S m) =>   let a := fst in
                    let b := fst ∘ snd in
                    let v := snd ∘ snd in
                    ⟨ ⟨a, fst ∘ vnzip ∘ v⟩, ⟨b, snd ∘ vnzip ∘ v⟩ ⟩ end.

      (*      Proof. induction n.
               exact ⟨nil, nil⟩.
               unfold Vec.
               simpl.
               remember (pow_app1 (A:=A) (@inl _ (True + Fin (n * 2)) I)) as a.
               remember (pow_app1 (A:=A) (@inr True (True + Fin (n * 2)) (inl I))) as b.
               remember (dλ f => pow_app1 (A:=A) (@inr True (True + Fin (n * 2)) (inr f))) as v.
               exact ⟨cons a (fst ∘ IHn ∘ v), cons b (snd ∘ IHn ∘ v)⟩.
               Show Proof. *)

      Lemma vnzip_step : forall {n} {Γ A} (a b : Γ ~~> A) (v : Γ ~~> Vec (n * 2) A),
          vnzip(n:=(S n)) ∘ ⟨a, ⟨b, v⟩⟩ == ⟨⟨a, fst ∘ vnzip ∘ v⟩, ⟨b, snd ∘ vnzip ∘ v⟩⟩.
      Proof.
        intros. (*
        apply proj_eq. *)
        simpl.
        rewrite !pair_f. rewrite !pair_fst. rewrite <- !compose_assoc, !pair_snd.
        rewrite !pair_fst. reflexivity.
      Qed.            

      Theorem unzip_vnzip : forall {A} {n}, (prefix n ⊗ prefix n) ∘ unzip(A:=A) == vnzip ∘ prefix (n * 2).
      Proof. intros A n.
             induction n.
             - (* 0  *)
               simpl.
               apply proj_eq; rewrite !compose_assoc;
                 try rewrite parallel_fst, pair_fst;
                 try rewrite parallel_snd, pair_snd;
                 rewrite unit_uniq; symmetry; apply unit_uniq.
             - (* S _ *)
               simpl prefix at 3. rewrite !pair_f. rewrite vnzip_step.
               simpl prefix. rewrite !(compose_assoc tl).
               rewrite <- !(compose_assoc _ vnzip).
               rewrite <- !IHn.               
               repeat (apply proj_eq; rewrite !compose_assoc;
                 try rewrite parallel_fst, pair_fst;
                 try rewrite parallel_snd, pair_snd).
               rewrite pair_fst. unfold unzip.
               rewrite compose_assoc. rewrite <- (compose_assoc _ fst). rewrite pair_fst.
               unfold unspool. unfold smap.
               rewrite stream_hd. rewrite pair_fst. rewrite compose_id_right.
               rewrite <- compose_assoc. rewrite stream_hd.
               rewrite pair_fst, compose_id_right, pair_fst. reflexivity.
               rewrite !pair_snd. rewrite parallel_fst.
               unfold unzip. rewrite !compose_assoc. rewrite <- !(compose_assoc _ fst).
               rewrite !pair_fst.
               unfold smap. rewrite <- !(compose_assoc _ tl). rewrite stream_tl.
               
               assert (stream (A:=A) (snd ∘ ⟨ fst (B:=A) ∘ hd, tl ⟩ ∘ id) ⟨ fst ∘ hd, tl ⟩ ==
                       stream id ⟨ fst ∘ hd, tl ⟩ ∘ tl).
               { rewrite <- stream_ext1. apply stream_Proper.
                 rewrite pair_snd, compose_id_left, compose_id_right. reflexivity.
                 reflexivity. }
               rewrite H. remove_eq_left. eapply unspool_tl.
               rewrite !pair_fst.
               unfold unzip. rewrite compose_assoc.
               rewrite <- (compose_assoc _ snd).
               rewrite pair_snd.
               unfold smap. rewrite stream_hd.
               rewrite pair_fst, compose_id_right.
               assert (hd ∘ unspool (A:=A) == ⟨hd, hd ∘ tl⟩).
               { eapply unspool_hd. }
               rewrite <- compose_assoc. rewrite H.
               rewrite pair_snd. reflexivity.
               rewrite pair_snd. unfold unzip.
               rewrite <- !(compose_assoc _ snd).
               rewrite !(compose_assoc _ _ snd).
               rewrite !pair_snd.
               unfold smap. rewrite <- !compose_assoc.
               rewrite (compose_assoc _ _ tl).
               rewrite stream_tl.
               assert
                 (forall x, stream (A:=A) (snd ∘ ⟨ snd (A:=x) ∘ hd, tl ⟩ ∘ id) ⟨ snd ∘ hd, tl ⟩ ==
                       stream id ⟨ snd ∘ hd, tl ⟩ ∘ tl).
               { intros x. rewrite <- stream_ext1. apply stream_Proper.
                 rewrite pair_snd. rewrite compose_id_left, compose_id_right. reflexivity.
                 reflexivity. }
               rewrite H. remove_eq_left. eapply unspool_tl.
      Qed.                     
                                                   
    End Fin.
    
  End vec.

End Vec.