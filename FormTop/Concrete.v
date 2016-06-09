Require Import Frame FormTop.FormTop FormTop.Cont Algebra.Sets.

Set Asymmetric Patterns.

(** A definition of concrete topological spaces. These are formal topologies
    which are related to a type of points in the expected way, through a
    relation which I call [In]. See Definition 1.2 in [1]. Their relation
    which I call [In] looks like [||-], and they read as "lies in" or
    "forces".
*)
Module Concrete. 
Section Concrete.

Variable X S : Type.
Variable In : X -> Ensemble S.

Definition le := (map_op (fun (s : S) (x : X) => In x s)
            (pointwise_op (fun (_ : X) (P Q : Prop) => P -> Q))).

Instance SPO : @PO.t S le _ := PO.map (fun s x => In x s) (PO.subset X).

Instance SubsetFrameOps : Frame.Ops (X -> Prop) := Frame.subset_ops X.

Record t : Type :=
  { here : forall x, { s | In x s }
  ; local : forall (a b : S) x, In x a -> In x b 
          -> { c | In x c /\ FormTop.down (map_op (fun s x => In x s) L.le) a b c }
  }.

(** Every concrete topological space can be presented as an
    inductively generated formal topology. See Section 4.4
    of [1]. *)
Definition Ix (a : S) : Type := sig (fun (g : forall (x : X), In x a -> S) 
  => forall (x : X) (prf : In x a), In x (g x prf)).

Definition C (a : S) (i : Ix a) : Ensemble S := match i with
  | exist g _ => fun s => exists (x : X) (prf : In x a), s = g x prf
  end.

Theorem loc : t -> FormTop.localized (map_op (fun s x => In x s) L.le) C.
Proof.
intros conc. destruct conc.
unfold FormTop.localized. simpl.
intros. unfold Ix in *. destruct i as [g Pg].
assert (forall x prf, In x (g x (H x prf))) as Pg'.
intros. apply Pg.
pose (fun x xina => local0 a (g x (H x xina)) x xina
  (Pg' x xina)) as g'.
assert (forall x prf, In x (proj1_sig (g' x prf))) as Pg''.
intros. destruct (g' x prf).
simpl. destruct a0. assumption.
exists (exist _ (fun x prf => proj1_sig (g' x prf)) Pg''). 

unfold C. intros.
destruct H0 as [x [prf img]].
exists (g x (H x prf)). split. exists x. exists (H x prf).
reflexivity.
destruct (g' x prf). simpl in *. destruct a0. subst.
assumption. 
Qed.

End Concrete.
End Concrete.



Module ConcFunc.
Section ConcFunc.
Generalizable All Variables.
Context {S} `{Conc1 : Concrete.t A S In1}.
Context {T} `{Conc2 : Concrete.t B T In2}.

Let leS := Concrete.le A S In1.
Let CovS := @FormTop.GCov S leS
   (Concrete.Ix A S In1) (Concrete.C A S In1).

Let leT := Concrete.le B T In2.
Let CovT := @FormTop.GCov T leT
   (Concrete.Ix B T In2) (Concrete.C B T In2).

Definition cmap (f : A -> B) (g : Cont.map S T) := 
  forall (t : T) (a : A), In2 (f a) t <-> (exists s, g t s /\ In1 a s).

Theorem cont : forall f g, cmap f g
  -> Cont.t leS leT CovS CovT g.
Proof.
intros. unfold cmap in H. constructor; intros.
Abort.

End ConcFunc.
End ConcFunc.
