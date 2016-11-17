(* Spaces whose points are compact sets
   i.e., some version of Smyth power domains
   See Vickers' *Topology via Logic*
   
   We should have

   pt : A ~~> P+(A)
   OR : P+(A) * P+(A) ~~> P+(A)

   approx : Approximator A X -> Approximator P+(A) X

   which behaves by arbitrarily choosing an option
   in the powerdomain. *)

(* It appears that there is a formulation of the Smyth powerdomain
   in formal topology in Vickers' 2005
   "Some constructive roads to Tychonoff"
*)

Require Import 
  FormTopC.FormTop
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.Join
  FormTopC.Cont.

Set Asymmetric Patterns.
Set Universe Polymorphism.
Local Open Scope Subset.

Module Compact.
Section Defn.

Context {S : PreISpace.t}
        {POS : PreO.t (le S)}.

Definition le := JoinTop.leL (le := le S).

Instance PO : PreO.t le := JoinTop.joinPreO.

Require Import Coq.Lists.List Types.List.
Import ListNotations.

Inductive Splits : list S -> list S -> list S -> Type :=
  | SplitNil : Splits nil nil nil
  | SplitL : forall a {xs ys zs}, Splits xs ys zs 
           -> Splits (a :: xs) ys (a :: zs)
  | SplitR : forall b {xs ys zs}, Splits xs ys zs
           -> Splits xs (b :: ys) (b :: zs).

Definition IxS := PreISpace.Ix S.

Inductive Ix {xs : list S} : Type :=
  | MkIx : forall a s : list S, Each IxS a 
   -> Splits a s xs -> Ix.

Arguments Ix : clear implicits.

Definition Ixnil : Ix nil.
Proof.
econstructor. apply Each_nil.
apply SplitNil.
Defined.

Inductive KFinite {U : S -> Type} : list S -> Type :=
  | KNil : KFinite nil
  | KCons : forall x, U x -> forall {xs}, KFinite xs -> KFinite (x :: xs).

Arguments KFinite : clear implicits.

Require Import CMorphisms.
Lemma KFinite_Proper_impl : Proper (Same_set ==> eq ==> arrow)
  KFinite.
Proof.
unfold Proper, respectful, arrow. intros.
subst. induction X0. apply KNil.
apply KCons. apply X. assumption. assumption.
Qed.

Instance KFinite_Proper : Proper (Same_set ==> eq ==> iffT)
  KFinite.
Proof.
unfold Proper, respectful. intros. split; intros.
- eapply KFinite_Proper_impl; eassumption.
- eapply KFinite_Proper_impl. symmetry. eassumption.
  symmetry. eassumption. assumption.
Qed.

Definition Each_get {A B} {xs : list A} {x : A}
  (e : Each B xs)
  (mem : member x xs) : B x.
Proof.
induction e.
- inv mem.
- inv mem. assumption. apply IHe. assumption.
Defined.

Definition CS := PreISpace.C S.

Inductive axunion {a : list S} {axioms : Each IxS a}
  : Subset S :=
  | Mkaxunion : forall (s : S) x (el : member x a),
  CS _ (Each_get axioms el) s -> axunion s.

Arguments axunion {a} axioms _.

Lemma axunion_nil_false : forall s, 
  axunion Each_nil s -> False.
Proof.
intros. induction X.
inv el.
Qed.

Lemma axunion_nil : axunion Each_nil === fun _ => False.
Proof.
apply Same_set_iff. intros. split; intros.
- eapply axunion_nil_false; eassumption.
- contradiction.
Qed.

Inductive Covering {a s : list S} {axioms : Each IxS a}
  {s' : list S} : Type :=
  | MkCovering : forall t, Splits t s s' -> 
    forall u, KFinite (axunion axioms) u -> le t u -> Covering.

Arguments Covering : clear implicits.

Definition C (xs : list S) (split : Ix xs) : Subset (list S) :=
  match split with
  | MkIx a s axioms mem => Covering a s axioms
  end.

Definition CompactPreO : FormTop.PreOrder :=
  {| PO_car := list S
   ; FormTop.le := le |}.

Definition Compact : PreISpace.t :=
  {| PreISpace.S := CompactPreO
   ; PreISpace.Ix := Ix
   ; PreISpace.C := C |}.

Lemma member_le : forall a b, member a b -> [a] <=[Compact] b.
Proof.
intros. simpl. unfold le, JoinTop.leL. intros.
inv X0. Focus 2. inv X1.
exists a. split. reflexivity. assumption.
Qed.

Lemma leS_le : forall a b, a <=[S] b -> [a] <=[Compact] [b].
Proof.
intros. simpl. unfold le, JoinTop.leL. intros.
inv X0. Focus 2. inv X1. exists b. split. assumption.
constructor.
Qed.

Lemma SplitsR_All xs : Splits nil xs xs.
Proof.
induction xs. constructor. constructor. assumption.
Qed.

Lemma Splits_KFinite {U xs ys zs} :
  Splits xs ys zs -> KFinite U xs -> KFinite U ys
  -> KFinite U zs.
Proof.
intros. induction X.
- assumption.
- inv X0. apply KCons. assumption. apply IHX; assumption.
- inv X1. apply KCons. assumption. apply IHX; assumption.
Qed.

Lemma KFinite_nil {xs} :
  KFinite (fun _ : S => False) xs -> xs = nil.
Proof.
intros H. induction H. reflexivity.
contradiction.
Qed.

Lemma le_nil {xs} : le xs [] -> xs = [].
Proof.
intros. induction xs.
- reflexivity.
- unfold le, JoinTop.leL in X.
  destruct (X a here). destruct p. inv m.
Qed.

Lemma Splits_length {xs ys zs} : Splits xs ys zs
  -> length xs + length ys = length zs.
Proof.
intros H. induction H.
- reflexivity. 
- simpl. rewrite IHSplits. reflexivity.
- simpl. rewrite <- plus_n_Sm. rewrite IHSplits.
  reflexivity.
Qed.

Lemma Splits_nil {xs} : Splits [] [] xs
  -> xs = [].
Proof.
intros H. apply Splits_length in H. simpl in H.
apply length_zero_iff_nil. symmetry. assumption.
Qed.

Lemma C_nil {xs} : C [] Ixnil xs -> xs = [].
Proof.
simpl. intros.
induction X.
eapply KFinite_Proper in k.
2: symmetry. 2: apply axunion_nil.
2: reflexivity. pose proof (KFinite_nil k).
subst. pose proof (le_nil l). subst.
apply Splits_nil in s. subst.
reflexivity.
Qed.

Hypothesis locS : FormTop.localized S.

Lemma Splits_nil_opp {xs ys} : Splits xs ys []
  -> xs = [] /\ ys = [].
Proof.
intros H. inv H. auto.
Qed.

Require Import Coq.Logic.Eqdep_dec.

Inductive Empty {A} : list A -> Prop :=
  | IsEmpty : Empty [].

Lemma Each_nil_unique_helper {A B} {xs : list A}
  (e : @Each A B xs) :
  match xs as xs' return @Each A B xs' -> Type with
  | [] => fun e => e = Each_nil
  | _ => fun _ => True
  end e.
Proof.
induction e. reflexivity. auto.
Qed.

Lemma Each_nil_unique {A B}
  (e : @Each A B []) : e = Each_nil.
Proof.
apply (Each_nil_unique_helper e).
Qed.

Lemma SplitNil_unique_helper {xs ys zs : list S}
  (s : Splits xs ys zs) :
  (match zs with
  | [] => match xs with
    | [] => match ys with
      | [] => fun e => e = SplitNil
      | _ => fun _ => True
      end
    | _ => fun _ => True
    end
  | _ => fun _ => True
  end) s.
Proof.
induction s; (reflexivity || auto).
Qed.

Lemma SplitNil_unique
  (s : Splits [] [] []) : s = SplitNil.
Proof.
apply (SplitNil_unique_helper s).
Qed.

Lemma Ixnil_unique : forall (i : Ix []), i = Ixnil.
Proof.
intros. induction i. unfold Ixnil. 
destruct (Splits_nil_opp s0). subst.
pose proof (Each_nil_unique e). subst.
pose proof (SplitNil_unique s0). subst.
reflexivity.
Qed.


Lemma loc : FormTop.localized Compact.
Proof.
unfold FormTop.localized.
intros.
unfold FormTop.localized in locS.
generalize dependent a.
induction c.
- intros. apply le_nil in X. subst. 
  exists Ixnil. intros.
  pose proof (C_nil X). subst.
  exists []. split.
  Focus 2. split; reflexivity.
  pose proof (Ixnil_unique i). subst.
  assumption.
- intros. induction i. simpl.
Abort.

Definition inj : Cont.map S Compact := fun xs x => [x] <=[Compact] xs.

Definition inj_cont : IGCont.t S Compact inj.
Proof.
constructor; intros.
- apply FormTop.grefl. exists [a]. unfold SetsC.In. constructor.
  unfold inj. reflexivity.
- unfold inj in *. apply FormTop.grefl.
  exists [a]. 2: reflexivity. split; assumption.
- unfold inj in *. etransitivity. apply leS_le.
  eassumption. eassumption.
- unfold inj in *. etransitivity; eassumption.
- induction j. simpl. induction a0.
  + apply FormTop.grefl. unfold inj in *.
    exists (a :: s). 2: apply member_le; constructor.
    simpl in X.
    econstructor. apply SplitL. apply SplitsR_All.
    2: eassumption. apply (Splits_KFinite s0).
    apply KNil. 
unfold inj in *.
Admitted.  

Definition Ix_singleton {a} (i : IxS a) : Ix [a].
Proof.
econstructor. 2: eapply SplitL. 2: econstructor.
econstructor. assumption. econstructor.
Defined.

Axiom undefined : forall A, A.

Require Import CRelationClasses.
Lemma lift_Cov_Ax : forall a (i : IxS a) u,
  CS a i u -> C [a] (Ix_singleton i) [u].
Proof.
intros. simpl. econstructor. apply SplitL. econstructor.
  2: reflexivity. econstructor.
  constructor 1 with a here. apply X.
  constructor.
Qed.

Local Open Scope FT.

Lemma Cov_nil {U} : [] <|[Compact] U.
Proof.
apply FormTop.ginfinity with Ixnil.
simpl. intros. induction X. 
  eapply KFinite_Proper in k.
  2: symmetry. 2: apply axunion_nil.
  2: reflexivity. pose proof (KFinite_nil k).
  subst. pose proof (le_nil l). subst.
  apply Splits_nil in s. subst.
Abort.

Lemma Cov_each : forall U (xs : list S),
  (forall x : S, member x xs -> [x] <|[Compact] U)
  -> xs <|[Compact] U.
Proof.
intros. induction xs.
- apply FormTop.ginfinity with Ixnil. 
  simpl. intros. induction X0.
  eapply KFinite_Proper in k.
  2: symmetry. 2: apply axunion_nil.
  2: reflexivity. pose proof (KFinite_nil k).
  subst. pose proof (le_nil l). subst.
  apply Splits_nil in s. subst.
Abort.
 
Lemma lift_Cov : forall a U, a <|[S] U
  -> [a] <|[Compact] Each U.
Proof.
intros.
induction X.
- apply FormTop.grefl. constructor. assumption.
  constructor.
- simpl in *. eapply FormTop.gle_left. 2: eassumption.
  apply leS_le. assumption.
- unshelve eapply FormTop.ginfinity.
  apply Ix_singleton. assumption.
  simpl. intros. 
  induction X0. 
econstructor.
Abort.

(** This actually doesn't work, because the
    empty compact set is a valid point of the space. *)
Definition nondet_run : forall a U, FormTop.GCov S a U
  -> forall (F : Subset (list S)), IGCont.pt Compact F
  -> SetsC.In F [a] -> { b : S & SetsC.In U b }.
Proof.
intros.
induction X.
- exists a. assumption.
- apply IHX. unfold SetsC.In.
  eapply (IGCont.pt_le_right (T := Compact) (F := F) X0).
  eassumption. apply leS_le. assumption.
- pose proof (IGCont.pt_cov X0 X1 (Ix_singleton i)) as H.
  induction H.
Abort.


End Defn.
End Compact.