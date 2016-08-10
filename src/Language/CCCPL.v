Set Universe Polymorphism.
Set Asymmetric Patterns.

(** Largely taken from CPDT
  http://adam.chlipala.net/cpdt/html/ProgLang.html
*)

Require Import Spec.Category
  Spec.CCC.CCC Types.List.
Import Category.
Import CCC. 

Section STLC. 

Context {U : Type} {ccat : CCat U}
  {cmc : CMC U} `{CCCOps U (ccat := ccat)}.

Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope obj.
Local Open Scope morph.

Fixpoint nprodT (xs : list U) : U := match xs with
 | nil => unit
 | x :: xs' => nprodT xs' * x
 end.

Inductive termDB : list U -> U -> Type :=
  | VarDB : forall G t, member t G -> termDB G t
  | ConstDB : forall G (A : U), (nprodT G ~~> A) -> termDB G A
  | AbsDB : forall G dom ran, termDB (dom :: G) ran -> termDB G (Func dom ran)
  | AppDB : forall G dom ran, termDB G (Func dom ran) -> termDB G dom -> termDB G ran.

  Arguments ConstDB {G} _ _.

Definition compile_DB {Γ : list U} (A : U) 
  (e : termDB Γ A) : nprodT Γ ~~> A.
Proof.
induction e.
- induction m; simpl. apply snd.
  apply (IHm ∘ fst). 
- assumption.
- apply abstract. simpl in IHe. apply IHe.
- eapply ap; eassumption.
Defined.

Section Var.
  Context {var : U -> Type}.

    Inductive term : U -> Type :=
    | Var : forall {t}, var t -> term t
    | Const : forall {A : U}, (unit ~~> A) -> term A
    | Abs  : forall {dom ran}, (var dom -> term ran) -> term (Func dom ran)
    | App  : forall {dom ran}, term (Func dom ran) -> term dom -> term ran.
  End Var.

  Arguments term : clear implicits.

  Definition Term t := forall var, term var t.

  Definition stupidT {A} : Term (A ==> A).
  Proof. unfold Term. intros. apply Abs.
  intros. apply Var. assumption.
  Defined.

Section wf.
    Context {var1 var2 : U -> Type}.

    Record varEntry := {
      Ty : U;
      First : var1 Ty;
      Second : var2 Ty
    }.

 Inductive wf : list varEntry -> forall {t}, term var1 t -> term var2 t -> Type :=
    | WfVar : forall G t x x', member {| Ty := t; First := x; Second := x' |} G
      -> wf G (Var x) (Var x')
    | WfConst : forall G A (e e' : unit ~~> A), e == e' ->  wf G (Const e) (Const e')
    | WfAbs : forall G dom ran (e1 : _ dom -> term _ ran) e1',
      (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e1 x1) (e1' x2))
      -> wf G (Abs e1) (Abs e1')
    | WfApp : forall G dom ran (e1 : term _ (Func dom ran)) (e2 : term _ dom) e1' e2',
      wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (App e1 e2) (App e1' e2').
  End wf.

  Definition Wf {t} (E : Term t) := forall var1 var2, wf nil (E var1) (E var2).

  Definition phoas_to_DB_helper {A}
   (e1 : term (fun _ => True) A) (e2 : term (fun _ => True) A) Γ
  (wellformed : wf Γ e1 e2)
  : termDB (List.map Ty Γ) A.
  Proof.
  induction wellformed.
  - apply VarDB. apply (member_map Ty) in m. apply m.
  - apply ConstDB. exact (e ∘ tt).
  - simpl in *. apply AbsDB. apply X; auto. 
  - eapply AppDB; eauto.
  Defined.

  Record WfTerm {A} :=
    { WfT_Term : forall var, term var A
    ; WfT_Wf : Wf WfT_Term
    }.

  Arguments WfTerm : clear implicits.

  Definition phoas_to_DB {A} (E : WfTerm A) : termDB nil A.
  Proof.
  destruct E as [E wellformed].
  pose proof (phoas_to_DB_helper (E (fun _ => True)) (E (fun _ => True)) nil).
  simpl in X. apply X. apply wellformed.
  Defined.

  Definition compile_phoas {A} (E : WfTerm A) 
    : unit ~~> A := compile_DB _ (phoas_to_DB E).

End STLC.

Hint Constructors member : member_db.

Arguments WfTerm {U ccat cmc H} A.
Arguments Build_WfTerm {U ccat cmc H A} _ _.

Ltac proveWF := red; 
  intros; repeat match goal with
  | [ |- wf _ _ _ ] => constructor; intros
  | [ |- member _ _ ] => eauto with member_db
  end; intuition.

  Delimit Scope stlc_scope with stlc.

  Notation "!" := Var : stlc_scope.
  Notation "#" := Const : stlc_scope.
  Infix "@" := App (left associativity, at level 19) : stlc_scope.
  Notation "'λ' x .. y => t " := (Abs (fun x => .. (Abs (fun y => t)) .. ))
        (x binder, y binder, at level 200, right associativity)
        : stlc_scope.

  Notation "[ e ]" := (fun _ => e)%stlc (at level 0) : stlc_scope.

  Notation "[ e | pf ]" := (Build_WfTerm [ e ]%stlc pf)
    (at level 0) : stlc_scope.

  Notation "[ e $ pf ]" := (compile_phoas [ e | pf ]%stlc)
    (at level 0) : stlc_scope.

  Notation "[ e |]" := (Build_WfTerm e _)
    (at level 0) : stlc_scope.

  Notation "[ e $]" := (compile_phoas [ e |]%stlc)
    (at level 0) : stlc_scope.

Section Test.
Context {U : Type} {ccat : CCat U}
  {cmc : CMC U} {cmcprops : CMC_Props U} `{CCCOps U (ccat := ccat)}.
  Local Open Scope obj.

  Definition comp {A B C : U} (g : unit ~~> B ==> C)
  (f : unit ~~> A ==> B) : unit ~~> A ==> C
  := [ λ x => #g @ (#f @ !x) $ ltac:(proveWF) ]%stlc.

  Lemma app_lem {A B} (f : unit ~~> A ==> B) (x : unit ~~> A) :
  ([ # f @ # x $ ltac:(proveWF) ]%stlc == f @ x)%morph.
  Proof.
  unfold compile_phoas. simpl. rewrite <- !(unit_uniq id).
  rewrite !compose_id_right. reflexivity.
  Qed.

  Lemma comp_id {A B} (f : unit ~~> A ==> B) :
    (comp [ λ x => !x $ ltac:(proveWF) ]%stlc f == f)%morph.
  Proof.
  unfold comp. unfold compile_phoas. simpl compile_DB at 2.
  Abort.

  Definition const {A B : U} : WfTerm (A ==> B ==> A) :=
   [ λ x y => !x | ltac:(proveWF) ]%stlc.

  Definition constS {A B} : unit ~~> A ==> B ==> A :=
     compile_phoas const.

  Axiom M : U -> U.

  Axiom undefined : forall A, A.

  Definition Bind {A B} : unit ~~> (M A ==> (A ==> M B) ==> M B)
    := undefined _.

  Definition Ret {A} : unit ~~> (A ==> M A) := undefined _.

  Axiom Bool Real : U.

  Definition coinflip : unit ~~> M Bool := undefined _.
  Definition normal : unit ~~> (Bool ==> M Real) := undefined _.

  Definition pair {A B} : unit ~~> (A ==> B ==> A * B) := undefined _.

  Definition testExp : unit ~~> M (Bool * Real) :=
    [ #Bind @ #coinflip @ (λ x => #Bind @ (#normal @ !x) @
      (λ y => #Ret @ (#pair @ !x @ !y) )) $ ltac:(proveWF) ]%stlc.

End Test.
  