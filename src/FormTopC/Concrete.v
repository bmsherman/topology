Require Import Algebra.FrameC FormTopC.FormTop FormTopC.Cont Algebra.SetsC.

Set Universe Polymorphism.
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
Variable In : X -> Subset S.

Definition le (s t : S) : Type := 
  forall x : X, In x s -> In x t.

Instance SPO : @PO.t S le _ := PO.map (fun s x => In x s) (PO.subset X).

Record t : Type :=
  { here : forall x, { s : S & In x s }
  ; local : forall (a b : S) x, In x a -> In x b 
          -> { c : S & (In x c * FormTop.down le a b c)%type }
  }.

(** Every concrete topological space can be presented as an
    inductively generated formal topology. See Section 4.4
    of [1]. *)
Definition Ix {a : S} : Type := (forall (x : X), In x a -> {s : S & In x s}).

Arguments Ix : clear implicits.

Inductive C {a : S} {g : Ix a} {s : S} : Type :=
  MkC : (forall (x : X) (prf : In x a), le (projT1 (g x prf)) s) -> C.

Arguments C : clear implicits.

Theorem loc : t -> FormTop.localized le C.
Proof.
intros conc. destruct conc.
unfold FormTop.localized.
intros a c X0 g.
exists (fun (x : X) (xina : In x a) => g x (X0 x xina)).
intros. induction X1.
exists s.
split. econstructor. intros.
Abort.

End Concrete.
End Concrete.

Arguments Concrete.Ix : clear implicits.
Arguments Concrete.C : clear implicits.

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

Require Import CRelationClasses.
Definition cmap (f : A -> B) (g : Cont.map S T) := 
  forall (t : T) (a : A), iffT (In2 (f a) t) { s : S & (g t s * In1 a s)%type}.

Theorem cont : forall f g, cmap f g
  -> Cont.t leS leT CovS CovT g.
Proof.
intros. unfold cmap in X. constructor; intros.
Abort.

End ConcFunc.
End ConcFunc.
