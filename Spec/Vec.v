Require Import Spec.Category Spec.Stream Spec.Discrete.
Import Category. Import Stream. Import Discrete.
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
    
    Notation "A ~> B" := (pow A B) (at level 40).
    
    Arguments pow_app1 {U} {ccat} {cmc} {D} {power} {_} {X} {A} x.
    Arguments pow_app2 {U} {ccat} {cmc} {D} {power} {_} {A} {B}.
    Arguments pmap {U} {ccat} {cmc} {D} {power} {_} {X} {Y} {A} {B} f g.
    Arguments pow_app1' {U} {ccat} {cmc} {D} {power} {_} {A} {X} {B} f x.
    Arguments pow_app2' {U} {ccat} {cmc} {D} {power} {_} {X} {A} {B} f.
    Arguments app12 {U} {ccat} {cmc} {D} {power} {H} {_} {A} {X} {B} f x.
    Arguments app21 {U} {ccat} {cmc} {D} {power} {H} {_} {A} {X} {B} f.
    Arguments pmap_Proper' {U} {ccat} {cmc} {D} {power} {H} {_} {X} {A} {B} {C} {D0}  _ _ y0 x0  _ _.

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
            
      Definition Vec : nat -> U -> U :=
        fun n A => (Fin n) ~> A.

      Definition to_nat : forall {n : nat}, (Fin n) -> nat.
      Proof. intros. induction n.
             - inversion H.
             - simpl in H. destruct H as [r | l].
               + exact 0.
               + exact (S (IHn l)).
      Defined.

      Definition vdx : forall {A} {n : nat}, (Fin n) -> Vec n A ~~> A :=
        fun _ n (i : Fin n) => pow_app1 i.

      Definition prefix' {A : U} : forall (n : nat),  Stream' A ~~> Vec n A :=
        fun (n : nat) => pmap to_nat id.

      Definition prefix {A : U} : forall (n : nat), Stream A ~~> Vec n A :=
        fun n => prefix' n ∘ StreamStream'.
      
    End Fin.
    
  End vec.

End Vec.