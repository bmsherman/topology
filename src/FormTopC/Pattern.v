Require Import 
  FormTopC.Cont
  FormTopC.FormTop
  FormTopC.FormalSpace
  Algebra.SetsC
  Algebra.OrderC
  FormTopC.Subspace.

Set Universe Polymorphism.
Local Open Scope Subset.
Local Open Scope FT.

Section Patterns.

Context {S T : FormalSpace.t}.

(** Construct a continuous map by pasting together local
    continuous maps in a sheaf-like manner.

    This will be useful, for instance, for definining
    multiplication of real numbers, where I have a family
    of functions which do bounded multiplication which is
    valid only on a subset of the whole space.

    For now, I am assuming that the map is given for every open
    set. That's valid at least for multiplication, and simplifies things. *)
Section SheafMap.

Variable (f : S -> Cont.map S T).

Inductive f_pasted {t : T} {s : S} : Type :=
  Mkf_pasted : forall s', s <= s' -> f s' t s -> f_pasted.

Arguments f_pasted : clear implicits.

Hypothesis f_cont : forall a, Cont.t S T (f a).
(* Not sure if the following is too strong. *)
Hypothesis f_intersect : forall (a : S) (b c : T),
 f_pasted b a -> f_pasted c a ->
  { t : T & (f_pasted t a * (eq b ↓ eq c) t)%type }.

Existing Instances FormalSpace.FT FormalSpace.PreO
  FormalSpace.Cov_Proper FormalSpace.Cov_Proper2
  FormalSpace.Cov_Proper3.

Lemma Cov_intersect : forall a U, a <|[S] U ->
  a <|[S] ⇓ (eq a) ∩ ⇓ U.
Proof.
intros.
apply FormTop.le_right. apply FormTop.refl. reflexivity. assumption.
Qed.

Theorem cont_f_pasted : Cont.t _ _ f_pasted.
Proof.
constructor; intros.
- pose proof (Cont.here (f_cont a)).
  specialize (X a). apply Cov_intersect in X.
  eapply (FormTop.trans X); clear X; intros.
  destruct X. destruct d, d0. unfold In in i. subst.
  destruct i0. destruct i.
  pose proof (Cont.le_left (f_cont a1)).
  eapply FormTop.le_left. Focus 2.
  apply FormTop.refl. econstructor.
  Focus 2.
  econstructor. 2: eapply X. eassumption. eassumption. eassumption.
  constructor. reflexivity.
- induction X0. pose proof (Cont.le_left (f_cont s')).
   apply (X0 _ _ _ X) in f0. 
  econstructor. 2: eassumption. etransitivity; eassumption.
- pose proof (f_intersect a b c X X0).
  destruct X1. destruct p. 
  apply FormTop.refl. exists x; eassumption. 
- destruct X.
  pose proof (Cont.cov (f_cont s') V f0 X0).
  apply Cov_intersect in X.
  eapply (FormTop.trans X); clear X; intros. destruct X.
  destruct d, d0. unfold In in i. subst. destruct i0.
  apply FormTop.refl. exists a. assumption.
  econstructor. 2: eapply (Cont.le_left (f_cont s')).
  transitivity a1; eassumption. 2: eassumption. eassumption.
Qed.

End SheafMap.

Section Pattern.

Variable Ix : Type.
Variable U : Ix -> Open S.
Variable UPos : forall i : Ix, FormTop.tPos (OpenPS (U i)).
Variable f : forall i : Ix, Cont.map (OpenSub (U i) (UPos i)) T.
Variable f_cont : forall i : Ix, Cont.t _ _ (f i).

Inductive union_f : Cont.map S T :=
  mk_union_f : forall (i : Ix) s t, f i t s -> union_f t s.

Variable covering : forall a : S, a <|[S] union (fun _ => True) union_f.

(* This is all not exactly right. Need to make sure I saturate
  before taking intersections, saturate before taking
  inclusions of open maps... *)
Variable UPos_int : forall i j, FormTop.tPos (OpenPS (U i ∩ U j)).
Variable glue_maps : forall i j : Ix, 
  Cont.map (OpenSub (U i ∩ U j) (UPos_int i j)) T.
  
Hypothesis gluing : forall i j : Ix,
  PreO.max (le := RelIncl) (f i) (f j) (glue_maps i j).
  

End Pattern.

End Patterns.