Require Import Spec.Category Spec.Discrete.

Import Category. Import Discrete.
Local Open Scope obj.
Local Open Scope morph.

Module Power.
Section Defn.

  Context `{dos : DiscreteOps}.
  Variable power : Type -> U -> U. (* CF https://ncatlab.org/nlab/show/power *)
  Infix "~>" := power (at level 30).
  Notation "| A |" := (unit ~~> A) (at level 90).
  
  (* To minimize confusion: Γ, A, B, etc = objects; X, Y, Z etc = types. *)
  
  Class PowOps : Type :=
    {
      pow_app1 : forall {X A}, X -> ((X ~> A) ~~> A)
      ; pow_app2 : forall {A B}, A ~~> ((A ~~> B) ~> B)
      ; pmap : forall {X Y} {A B}, (X -> Y) -> (A ~~> B) -> (Y ~> A) ~~> (X ~> B)
    }.
  
  (* One ought to have Γ ~~> (X ~> B) ≃ X -> (Γ ~~> B).
 In case Γ = unit this says precisely that unit ~~> (A ~> B) ≃ A -> (unit ~~> B), and this latter ≃
 D A ~~> B by properties of discrete. *)
  
  Context `{PowOps}.

  Definition pow_app1' : forall {A X B}, A ~~> (X ~> B) -> (X -> (A ~~> B)) :=
    fun _ _ _ f x => (pow_app1 x) ∘ f.
  
  Definition pow_app2' : forall {X A B}, (X -> (A ~~> B)) -> A ~~> (X ~> B) :=
    fun _ _ _ f => (pmap f id) ∘ pow_app2.
  
  Definition dfs_to : forall {X A}, |X ~> A| -> (D X ~~> A) :=
    (fun X A (F : |X ~> A|) =>
       let  F' := pow_app1' F : X -> |A|
       in   discrete_func' F').
  
  Definition dfs_fro : forall {X A}, (D X ~~> A) -> |X ~> A| :=
    (fun X A (F : D X ~~> A) =>
       let  F' := discrete_pt' F : X -> |A|
       in   pow_app2' F').
  
  
  Definition pb_eq {X : Type} {A B : U} : (X -> (A ~~> B)) -> (X -> (A ~~> B)) -> Prop :=
    fun f g => forall (x : X), (f x) == (g x).
  
  
  Notation "A === B" := (pb_eq A B) (at level 60).
  
  Require Import Morphisms.
  Class PowProps : Type :=
    {
      pmap_Proper : forall X Y A B, Proper (Logic.eq ==> eq ==> eq) (pmap (X:=X) (Y:=Y) (A:=A) (B:=B))
      ; pmap_Proper' : forall X A B C D, Proper (pb_eq ==> eq ==> eq) (pmap (X:=X) (Y:=(C ~~> D)) (A:=A) (B:=B))
      (* Useful for proving equality of dλ-terms. *)
      (*  ; func_pt : forall {X A} {f : D X ~~> A}, (discrete_func' (discrete_pt' f)) == f
  ; pt_func : forall {X A} {f : X -> |A| }, (discrete_pt' (discrete_func' f)) = f *)
      ; app21 : forall {A X B} (f : A ~~> (X ~> B)), pow_app2' (pow_app1' f) == f 
      ; app12 : forall {A X B} (f : X  -> (A ~~> B)), pow_app1' (pow_app2' f) === f (*
  ; dpt_nat : forall {X Y} {h : X -> Y} {x : X}, discrete_pt (h x) == (dmap h) ∘ discrete_pt x 
   Axioms that might come in handy later but I don't know if are useful now ^*)
      ; pow_app1_nat1 : forall {X X'} {A} (x : X) (h : X -> X'), (pow_app1 x) ∘ (pmap h id(A:=A)) == (pow_app1 (h x))
      ; pow_app2'_Proper : forall {X} {A B}, Proper (pb_eq ==> eq) (pow_app2' (A:=A) (B:=B) (X:=X))
      ; pow_app2'_pre : forall {X} {A A' B} (f : A ~~> A') (g : X -> (A' ~~> B)),
          (pow_app2' g) ∘ f == (pow_app2' (fun x => (g x) ∘ f))
      ; pmap_compose1 : forall {A} {X Y Z} (f : X -> Y) (g : Y -> Z),
          (pmap f id) ∘ (pmap g id) == pmap (fun x => (g (f x))) (id(A:=A))
      ; pmap_id : forall {A} {X}, pmap (fun x : X => x) (id(A:=A)) == id                                        
    }.

  Notation "'pλ' x => f" := (pow_app2' (fun x => f)) (at level 80).
  Context {cmp : CMC_Props U}. Context {pps : PowProps}.
  
  Lemma pow_False : forall A, False ~> A ≅ unit.
  Proof. intros A.
         refine (Build_Iso _ _ _ _ _ _ _ _ _).
         Unshelve.
         Focus 3. exact tt.
         Focus 3. refine (pλ wish => _). inversion wish.
         - apply unit_uniq.
         - simpl.
           rewrite <- (app21 id).
           rewrite pow_app2'_pre.
           apply pow_app2'_Proper.
           unfold pb_eq. intros wish.
           inversion wish.
  Defined.
  
  Lemma pow_Iso : forall {X Y} {A} (f : X -> Y) (g : Y -> X),
      (fun x => g (f x)) = (fun x => x) -> (fun y => f (g y)) = (fun y => y) -> X ~> A ≅ Y ~> A.
  Proof. intros X Y A f g gf fg.
         eapply Build_Iso.
         Unshelve.
         Focus 3. exact (pmap g id).
         Focus 3. exact (pmap f id).
         rewrite pmap_compose1.
         rewrite fg. rewrite pmap_id.
         reflexivity.
         rewrite pmap_compose1.
         rewrite gf. rewrite pmap_id.
         reflexivity.
  Defined.
End Defn.

Arguments pow_app1 {U} {ccat} {power} {_} {X} {A} x.
Arguments pow_app2 {U} {ccat} {power} {_} {A} {B}.
Arguments pmap {U} {ccat} {power} {_} {X} {Y} {A} {B} f g.

Arguments pow_app1' {U} {ccat} {cmc} {power} {_} {A} {X} {B} f x.
Arguments pow_app2' {U} {ccat} {cmc} {power} {_} {X} {A} {B} f.
Arguments app12 {U} {ccat} {cmc} {power} {H} {_} {A} {X} {B} f x.
Arguments app21 {U} {ccat} {cmc} {power} {H} {_} {A} {X} {B} f.
Arguments pmap_Proper' {U} {ccat} {cmc} {power} {H} {_} {X} {A} {B} {C} {D}  _ _ y0 x0  _ _.
Arguments pow_app2'_pre {U} {ccat} {cmc} {power} {H} {_} {X} {A} {A'} {B} {f} {g}.

Arguments dfs_to {U} {ccat} {cmc} {D} {_} {power} {_} {X} {A} f.


End Power.