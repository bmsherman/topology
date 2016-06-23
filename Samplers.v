Require Import Coq.Lists.List.
Import ListNotations.
Require Import ContPL.
Require Import Morphisms.
Require Import Spec.Category.
Require Import Spec.Prob.
Require Import Spec.Real Spec.Sierpinski Spec.Sum Spec.Lift Spec.Discrete Spec.Stream.
Import Category.
Import ContPL.
Import Prob.
Import Real.
Import Sierp.
Import Sum.
Import Lift.
Import Stream.
Import Discrete.
Local Open Scope morph.
Local Open Scope obj.

Section Samplers.

  Context {U : Type}.
  Context `{sigmaops : ΣOps (U := U)}.
  Context `{rops : ROps U (ccat := ccat) (cmc := cmc) (Σ := Σ)}.
  Context `{lrnnops : LRnnOps (ccat := ccat) (cmc := cmc) (Σ := Σ) U}.
  Context `{sumops : SumOps (U:=U) (ccat := ccat)}.
  Context `{sumprops : SumProps (U:=U) (ccat:=ccat) (cmc:=cmc) (sts:=sts)(H:=sumops)}.
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{Streamprops : StreamProps (U:= U)(ccat:=ccat) (Stream:=Stream)(cmc:=cmc) (sps:=Streamops)}.
  Context `{mops : MeasOps U
(ccat := ccat) (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc) (smd := ProbMonad)}.

  Existing Instance ProbMonad.

 (*

Candidates for below I'm not sure about:
 (@to_from _ _ _ _ _ _), (@from_to _ _ _ _ _ _ _)

There's an argument to be made for adding parallel_pair, but I don't think I want it.

  *)
 
  Hint Rewrite
       (@compose_id_left _ _ _ _) (@compose_id_right _ _ _ _)
       (@pair_fst _ _ _ _) (@pair_snd _ _ _ _)
       (@parallel_fst _ _ _ _) (@parallel_snd _ _ _ _)
       (@unit_uniq _ _ _ _)
       (@map_id _ Prob _ _ _ _)
       (@join_map_ret _ _ _ _ _ _) (@join_ret  _ _ _ _ _ _)
       (@strength_ret _ _ _ _ _ _)
       (@fst_strong _ _ _) (@snd_strong _ _ _ _ _ _)
       (@stream_hd _ _ _) (@stream_tl _ _ _)
    : cat_db.
  
  Definition swap {A B : U} : A * B ~~> B * A :=
    ⟨snd, fst⟩.
  
  Definition indep {Γ A B : U} (DA : Γ ~~> Prob A) (DB : Γ ~~> Prob B) : (Γ ~~> Prob (A * B)) :=
      ( a <- DA;
        b <- !DB;
        Ret ⟨!a, b⟩).

  Definition inner_indep {A B : U} : (Prob A) * (Prob B) ~~> Prob (A * B) :=
    indep (Γ := Prob A * Prob B) fst snd.

   Definition marg {A B : U} : Prob (A * B) ~~> (Prob A) * (Prob B) :=
    ⟨map fst , map snd⟩.
  (* 'marg' for 'marginal' *)

(*   Definition cond_choice {Γ A B : U} (D : Γ ~~> Prob (A * B *)

   
  Lemma emap_fst_pair : forall {Γ A B C : U} (f : Γ ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B),
      (emap (f ∘ fst)) ∘ ⟨h , k⟩ == ret ∘ f ∘ h.
  Proof. intros Γ A B C f h k. unfold emap. rewrite map_compose.
         rewrite <- (compose_assoc strong).
         rewrite fst_strong. rewrite -> compose_assoc.
         rewrite ret_nat. rewrite <- (compose_assoc _ fst). rewrite pair_fst.
         reflexivity.
  Defined.

  Lemma emap_snd_pair : forall {Γ A B C : U} (f : B ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B),
      (emap (f ∘ snd)) ∘ ⟨h , k⟩ == (map f) ∘ k.
  Proof. intros Γ A B C f h k. unfold emap. rewrite map_compose.
         rewrite <- (compose_assoc _ (map snd)).
         rewrite snd_strong. rewrite <- (compose_assoc _ snd). rewrite pair_snd. reflexivity.
  Defined.

  Theorem map_Ret : forall {Γ A B : U} (f : Γ ~~> A) (h : A ~~> B),
      (map h) ∘ (Ret f) == Ret (h ∘ f).
  Proof. intros Γ A B f h.
         unfold Ret. rewrite compose_assoc. rewrite <- ret_nat. rewrite compose_assoc.
         reflexivity.
  Defined.

  Theorem map_Bind : forall {Γ A B C} (f : Γ * A ~~> Prob B) (m : Γ ~~> Prob A) (g : B ~~> C),
      (map g) ∘ (Bind m f) == Bind m ((map g) ∘ f).
  Proof.
    intros Γ A B C f m g.
    unfold Bind. unfold bind. rewrite (compose_assoc _ (join ∘ map f)). rewrite (compose_assoc _ join).
    rewrite join_nat. rewrite <- (compose_assoc _ (map (map g))). rewrite map_compose. reflexivity.
  Defined.
  
  Theorem map_Bind' : forall {Γ A B C}
      (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> Prob B) (e : Γ ~~> Prob A) (g : B ~~> C),
      (map g) ∘ Bind e (makeFun1E f) == Bind e (map g ∘ makeFun1E f).
    intros Γ A B C f e g.
    apply map_Bind.
  Defined.
  
  Theorem Bind_emap : forall {Γ A B} (m : Γ ~~> Prob A)(f : Γ * A ~~> Prob B),
      (Bind m f) == join ∘ (emap f) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m f.
         unfold Bind, bind, emap. rewrite compose_assoc, compose_assoc. reflexivity.
  Defined.

  Definition jmap {Γ A B} (f : Γ * A ~~> Prob B) : Γ * Prob A ~~> Prob B :=
    join ∘ (emap f).
  
  Theorem Bind_push : forall {Γ Δ A B} (m : Γ ~~> Prob A) (f : Γ * A ~~> Prob B) (g : Δ ~~> Γ),
      (Bind m f) ∘ g == (jmap f) ∘ ⟨g, m ∘ g⟩.
  Proof. intros Γ Δ A B m f g.
         unfold Bind, bind, jmap, emap. rewrite compose_assoc, compose_assoc.
         rewrite <- (compose_assoc g). rewrite pair_f, compose_id_left.
         reflexivity.
  Defined.
 
  Theorem Bind_m_Ret : forall {Γ A B} (m : Γ ~~> Prob A) (x : Γ * A ~~> B),
      (Bind m (Ret x)) == (emap x) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m x.
         unfold Bind, Ret, emap, bind. rewrite map_compose. rewrite (compose_assoc (map x)).
         rewrite join_map_ret, compose_id_left. rewrite compose_assoc. reflexivity.
  Defined.

  Theorem Bind_Ret_f : forall {Γ A B} (x : Γ ~~> A) (f : Γ * A ~~> Prob B),
      (Bind (Ret x) f) == f ∘ ⟨id, x⟩.
  Proof. intros Γ A B x f.
         unfold Bind, Ret, bind.
         rewrite <- (compose_id_left id).
         rewrite <- (parallel_pair id x id ret).
         rewrite (compose_assoc _ _ strong).
         autorewrite with cat_db.
         rewrite compose_assoc.
         rewrite <- (compose_assoc ret).
         rewrite <- ret_nat, compose_assoc.
         autorewrite with cat_db.
         reflexivity.
  Defined.

  Axiom whatever : forall {A}, A.
    

  Theorem Bind'_m_Ret : forall {Γ A B}  (m : Γ ~~> Prob A) (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> B),
      Bind m (Ret (makeFun1E f)) ==  (emap (makeFun1E f)) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m f.
         apply Bind_m_Ret.
  Defined.


  Theorem Bind'_Ret_f : forall {Γ A B} (x : Γ ~~> A) 
  (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> Prob B),
      Bind (Ret x) (makeFun1E f) == (makeFun1E f) ∘ ⟨id, x⟩.
  Proof. intros Γ A B x f. apply Bind_Ret_f.
  Defined.

  Ltac remove_eq_left :=
    repeat rewrite <- compose_assoc; repeat (apply compose_Proper; try reflexivity).
  Ltac remove_eq_right :=
    repeat rewrite compose_assoc; repeat (apply compose_Proper; try reflexivity).

  
  Theorem Bind_Bind : forall {Γ A B C : U} (m : Γ ~~> Prob A) (f : Γ * A ~~> Prob B) (g : Γ * B ~~> Prob C),
      Bind (Bind m f) g == Bind m (Bind f (g ∘ (fst ⊗ id))).
  Proof. intros Γ A B C m f g.
         unfold Bind, bind.
         rewrite !map_compose.
         rewrite !compose_assoc.
         rewrite join_join.
         remove_eq_left. rewrite !compose_assoc.
         rewrite <- join_nat. remove_eq_left.
         rewrite !compose_assoc.
         rewrite pair_parallel_diagonal at 1. rewrite compose_assoc.
         assert (forall {Q X Y Z : U} (f : X ~~> Y) (g : Y ~~> Z), id (A:=Q) ⊗ (g ∘ f) == id ⊗ g ∘ id ⊗ f) as H.
         {
           intros Q X Y Z F G. apply proj_eq.
           - rewrite compose_assoc. repeat (rewrite parallel_fst; autorewrite with cat_db).
             reflexivity.
           - rewrite compose_assoc. rewrite !parallel_snd. rewrite <- !compose_assoc.
             rewrite parallel_snd. reflexivity.
         }
         rewrite !H.
         rewrite !compose_assoc. rewrite strength_join. remove_eq_left.
         rewrite !compose_assoc.
         rewrite <- map_compose.
         rewrite <- strong_nat, map_compose. remove_eq_left.
         rewrite !compose_assoc. rewrite <- map_compose.
         rewrite parallel_pair.
         autorewrite with cat_db.
         rewrite strong_nat.
         rewrite <- (compose_assoc _ _ (map (id ⊗ f))).
         rewrite strength_compose.
         rewrite pair_parallel_diagonal at 2. 
         assert (id ⊗ ⟨id, m⟩ ∘ diagonal == ⟨fst, id⟩ ∘ (id ⊗ m) ∘ diagonal) as Δ1.
         { apply proj_eq.
           - autorewrite with cat_db.
             rewrite !compose_assoc.
             autorewrite with cat_db.
             reflexivity.
           - autorewrite with cat_db.
             rewrite !compose_assoc.
             autorewrite with cat_db. unfold parallel.
             apply proj_eq.
             + autorewrite with cat_db.
               rewrite !compose_assoc.
               autorewrite with cat_db.
               rewrite diagonal_snd, diagonal_fst. reflexivity.
             + autorewrite with cat_db.
               rewrite !compose_assoc.
               autorewrite with cat_db. reflexivity.
         }
         rewrite <- !compose_assoc. rewrite Δ1 at 1.
         remove_eq_right.
         assert (prod_assoc_left ∘ ⟨fst, id⟩ == diagonal (A:=Γ) ⊗ id(A:=Prob A)) as Δ2.
         {
           unfold prod_assoc_left, parallel, diagonal.
           rewrite !pair_f. autorewrite with cat_db.
           rewrite <- !compose_assoc. autorewrite with cat_db.
           reflexivity.
         }
         rewrite <- !compose_assoc. rewrite Δ2.
         rewrite <- map_id at 1. rewrite strong_nat.
         remove_eq_right.
         rewrite <- !map_compose; apply map_Proper.
         apply proj_eq.
         - rewrite !compose_assoc; unfold prod_assoc_right, diagonal; autorewrite with cat_db.
           rewrite <- compose_assoc; autorewrite with cat_db.
           rewrite compose_assoc; autorewrite with cat_db. reflexivity.
         - rewrite !compose_assoc; unfold prod_assoc_right, diagonal; autorewrite with cat_db.
           rewrite <- !compose_assoc; autorewrite with cat_db.
           rewrite <- (compose_id_right f) at 2; remove_eq_left.
           rewrite compose_assoc; autorewrite with cat_db.
           apply proj_eq.
           + rewrite !compose_assoc; autorewrite with cat_db.
             rewrite <- compose_assoc; autorewrite with cat_db.
             rewrite compose_assoc; autorewrite with cat_db. reflexivity.
           + rewrite !compose_assoc; autorewrite with cat_db. reflexivity.
  Qed.
         
    
  Theorem Bind_map_f : forall {Γ A B C} (m : Γ ~~> Prob A) (g : A ~~> B) (f : Γ * B ~~> Prob C),
      (Bind ((map g) ∘ m) f) == (Bind m (f ∘ (id ⊗ g))).
  Proof. intros Γ A B C m g f.
         unfold Bind, bind.
         rewrite map_compose.
         rewrite <- (compose_assoc (strong ∘ ⟨id, m ⟩)).
         rewrite (compose_assoc ⟨id, m⟩).
         rewrite <- (compose_assoc _ _ (map f)).
         rewrite <- strong_nat.
         rewrite <- (compose_assoc _ _ (map f)).
         rewrite <- (compose_assoc _ _ strong).
         rewrite parallel_pair.
         autorewrite with cat_db.
         rewrite !compose_assoc; reflexivity.
  Qed.
  
(*
  Theorem Bind'_map_f : forall {Γ A B C} (m : Γ ~~> Prob A) (g : A ~~> B) (f : Γ * B ~~> B -> Γ * B ~~> Prob C),
      (x <- (map g) ∘ m; (f x)) == (x <- m; (f snd) ∘ (id ⊗ g)).
  Proof. intros Γ A B C m g f.
         apply  Bind_map_f. 
  Qed.
*)
  

(* This should be true, but I don't think it's useful enough to bother proving. Maybe if I need it later I will.
Theorem strength_indep : forall {A B : U}, (strong (A:=A)(B:=B)) == inner_indep ∘ (ret ⊗ id).
Proof. Abort.
 *)

  Lemma ret_Ret : forall {Γ A} (x : Γ ~~> A), (Ret x) == ret ∘ x.  (*TODO is there a non-stupid way to do this? *)
  Proof. unfold Ret. reflexivity.
  Defined.

  Lemma Ret_ext : forall {Γ Δ A} (g : Γ ~~> Δ) (f : Δ ~~> A), (Ret f) ∘ g == Ret (f ∘ g).
  Proof. intros A B C x f.
         unfold Ret; rewrite compose_assoc; reflexivity.
  Defined.


  Require Import Morphisms.

  Instance indep_ext1 {Γ A B} : Proper (eq ==> eq ==> eq) (@indep Γ A B).
  Proof.
  unfold Proper, respectful. intros. unfold indep. apply Bind_Proper.
  assumption. apply lam_extensional. intros. 
  apply Bind_Proper. unfold Lift, Extend_Prod. apply compose_Proper. 
  assumption. reflexivity.  reflexivity.
  Qed.

  Lemma Bind_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> Prob A)
    (f : Δ * A ~~> Prob B), Bind x f ∘ g == Bind (x ∘ g) (f ∘ (g ⊗ id)).
  Proof.
  intros. unfold Bind. unfold bind. rewrite <- !(compose_assoc _ _ join).
  apply compose_Proper. reflexivity. rewrite map_compose.
  rewrite <- !(compose_assoc _ _ (map f)). 
  apply compose_Proper. reflexivity.
  rewrite compose_assoc. rewrite <- strong_nat. 
  rewrite <- !(compose_assoc _ _ strong).
  apply compose_Proper. reflexivity.
  rewrite map_id. 
  rewrite parallel_pair. autorewrite with cat_db.
  rewrite pair_f. autorewrite with cat_db. reflexivity.
  Qed.

(*
  Theorem Bind'_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> Prob A)
    (f : Δ * A ~~> A -> Δ * A ~~> Prob B), (a <- x; f a) ∘ g == (b <- x ∘ g; (f snd) ∘ ⟨g ∘ fst, b⟩).
  Proof.
    intros.
    rewrite Bind_ext. apply Bind_Proper; try reflexivity.
    unfold makeFun1E. apply compose_Proper; try reflexivity.
    apply proj_eq.
    - rewrite parallel_fst. autorewrite with cat_db. reflexivity.
    - rewrite parallel_snd. autorewrite with cat_db. reflexivity.
  Qed.
*)


  Theorem call_inv {A B C : U} (f : forall Δ, Δ ~~> A -> Δ ~~> B -> Δ ~~> C)
  (f_ext1 : forall Δ, Proper (eq ==> eq ==> eq) (f Δ))
  (f_ext : forall Γ Δ (g : Γ ~~> Δ) (x : Δ ~~> A) (y : Δ ~~> B),
     f Δ x y ∘ g == f Γ (x ∘ g) (y ∘ g))
  {Γ : U} (x : Γ ~~> A) (y : Γ ~~> B)
  : Call (makeFun [A; B] f) x y == f Γ x y.
  Proof. 
  unfold Call, makeFun, prodsplay. simpl.
  rewrite f_ext. autorewrite with cat_db. rewrite <- compose_assoc.
  autorewrite with cat_db. reflexivity.
  Qed.

  Theorem indep_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> Prob A)
    (y : Δ ~~> Prob B), indep x y ∘ g == indep (x ∘ g) (y ∘ g).
  Proof.
  intros. unfold indep. rewrite Bind_ext. apply Bind_Proper. 
  reflexivity. unfold makeFun1E. 
  rewrite Bind_ext.
  apply Bind_Proper. unfold Lift, Extend_Prod, Extend_Refl.
  autorewrite with cat_db. 
  rewrite <- !(compose_assoc _ _ y). 
  apply compose_Proper. reflexivity.
  unfold parallel, extend. autorewrite with cat_db. reflexivity.
  rewrite Ret_ext. apply Ret_Proper.
  rewrite pair_f. apply pair_Proper.
  unfold Lift, Extend_Prod, Extend_Refl; simpl.
  unfold parallel, extend.
  autorewrite with cat_db.
  rewrite <- compose_assoc. autorewrite with cat_db.
  rewrite compose_assoc. autorewrite with cat_db. reflexivity.
  unfold parallel. autorewrite with cat_db. reflexivity.
  Qed.

  Theorem call_indep : forall Γ A B (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
    Call (makeFun [Prob A; Prob B] (fun _ => indep)) mu nu == indep mu nu.
  Proof.
  intros. apply (call_inv (fun _ => indep)).
  - intros. typeclasses eauto.
  - intros. apply indep_ext.
  Qed.


  Theorem marg_inner_indep : forall {A B : U}, (marg (A:=A)(B:=B)) ∘ inner_indep == id.
  Proof. intros A B.
         unfold marg. apply proj_eq.
         - rewrite compose_assoc. autorewrite with cat_db.
           unfold inner_indep.  unfold indep.
           setoid_rewrite map_Bind'.
           setoid_rewrite map_Bind'.
           setoid_rewrite map_Ret.
           rewrite Bind_m_Ret.
           unfold Lift, Extend_Refl, Extend_Prod, extend. (* I should automate this maybe? *)
           autorewrite with cat_db.
           rewrite emap_fst_pair.
           autorewrite with cat_db.
           rewrite <- ret_Ret.
           (* NB at this point we've reduced one Bind ... Ret ... to a Ret ... *)
           rewrite Bind_m_Ret.
           rewrite <- (compose_id_left snd). (* A bit silly, maybe make this special later? *)
           rewrite emap_snd_pair.
           autorewrite with cat_db.
           reflexivity.
           
         - rewrite compose_assoc.
           autorewrite with cat_db.
           unfold inner_indep. unfold indep.
           setoid_rewrite map_Bind'. 
           setoid_rewrite map_Bind'.
           setoid_rewrite map_Ret.
           rewrite Bind_m_Ret.
           unfold Lift, Extend_Refl, Extend_Prod, extend.
           autorewrite with cat_db.
           rewrite <- (compose_id_left snd).
           rewrite emap_snd_pair.
           autorewrite with cat_db.
           rewrite Bind_emap.
           rewrite <- (compose_assoc _ _ join).
           rewrite emap_fst_pair. rewrite compose_assoc, compose_assoc.
           autorewrite with cat_db.
           reflexivity.
           
  Defined.

  Definition Map {Γ A B : U} (f : Γ * A ~~> B) (mu : Γ ~~> Prob A)
    : Γ ~~> Prob B := emap f ∘ ⟨ id , mu ⟩.
  
  Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : indep DS DA == Map sample DS
      }.

      Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.
  
    
    Definition const_sampler {Δ A S : U} {D : Δ ~~> Prob S} {x : Δ ~~> A} :
      Sampler (Δ := Δ) (A := A) (S := S) D (Ret x).
    Proof. refine (sampler ⟨snd, x ∘ fst⟩ _).       
           unfold indep. 
           unfold Lift, Extend_Prod, Extend_Refl. simpl.
           rewrite bind_extensional. Focus 2.
           intros a.
           setoid_rewrite Ret_ext.
           Check Bind'_Ret_f.
           setoid_rewrite Bind'_Ret_f.
           unfold makeFun1E. intros.
           rewrite Ret_ext.
           rewrite pair_f. 
           reflexivity.
           simpl.
           setoid_rewrite Ret_ext. setoid_rewrite pair_f.
           unfold extend, Extend_Prod, Extend_Refl.
           autorewrite with cat_db.
           rewrite <- (compose_assoc _ fst snd). autorewrite with cat_db.
           rewrite Bind_m_Ret.
           reflexivity.
Defined.
 
  
  
  Definition Boole := unit + unit.
  Definition Cantor := Stream Boole.
  
  Definition constant_stream {Γ A : U} (mu : Γ ~~> Prob A) :
    Γ ~~> Prob (Stream A) := 
    pstream (MeasOps := mops) (Γ := Γ) tt (LAM _ => map add_unit_right ∘ !mu).

  Theorem constant_stream_ext1 : forall {Γ Δ A : U} (mu : Δ ~~> Prob A) (f : Γ ~~> Δ),
      constant_stream (mu ∘ f) == (constant_stream mu) ∘ f.
  Proof. intros Γ Δ A mu f.
         unfold constant_stream.
         rewrite pstream_ext1.
         apply pstream_Proper.
         - symmetry. apply unit_uniq.
         - unfold makeFun1E, Lift, Extend_Prod, Extend_Refl, extend.
           autorewrite with cat_db.
           rewrite <- !compose_assoc.
           rewrite parallel_fst. reflexivity.
Qed.
           

  
  Definition infinite_coinflips : unit ~~> Prob Cantor := 
    constant_stream coinflip.
  
  Definition constant_unfold_prog : forall {Γ A : U} (mu : Γ ~~> Prob A), Γ ~~> Prob (Stream A).
  Proof. intros. Check (constant_stream mu).
         refine (y <- mu; (zs <- constant_stream (!mu); _)).
         refine (Ret (cons (!y) zs)).
         Show Proof.
  Defined.

  Existing Instance pstream_Proper.


Lemma Bind_iso {Γ A A' B : U} (p : A ~~> A') 
  (mu : Γ ~~> Prob A) (mu' : Γ ~~> Prob A')
  (f : Γ * A ~~> Prob B) (f' : Γ * A' ~~> Prob B)
  : map p ∘ mu == mu'
  -> f == f' ∘ (id ⊗ p)
  -> Bind mu f == Bind mu' f'.
Proof.
intros. unfold Bind, bind.
rewrite <- H, H0. rewrite map_compose.
remove_eq_left.
rewrite compose_assoc.
rewrite <- strong_nat.
remove_eq_left.
rewrite <- pair_parallel_id. reflexivity.
Qed.


(** Some "parametricity" properties. Not necessarily true,
    but will hold if we're not evil. *)

Lemma lam_eval {Γ Γ' A B : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  (x : Γ' ~~> A) (g : Γ' ~~> Γ) :
  makeFun1E f ∘ ⟨ g , x ⟩ == f _ g x.
Proof.
Admitted.

Lemma lam_Proper {Γ A B : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  : forall Δ, Proper (eq ==> eq ==> eq) (f Δ).
Admitted.

(** We'll prove the rest from these. *)

Ltac simpl_ext := unfold liftF, Lift, Extend_Prod, Extend_Refl, extend;
  repeat rewrite compose_id_right.

Lemma lam_eval_ext {Γ Γ' A' A B : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  (x : A' ~~> A) (ext : Γ' ~~> Γ)
 : makeFun1E f ∘ ext ⊗ x == makeFun1E (fun Δ e z => f _ (ext ∘ e) (! (x ∘ z))).
Proof.
unfold parallel. rewrite lam_eval. unfold makeFun1E.
simpl_ext. apply lam_Proper; autorewrite with cat_db; reflexivity.
Qed.

Lemma lam_eval_par {Γ A' A B : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  (x : A' ~~> A)
 : makeFun1E f ∘ id ⊗ x == makeFun1E (fun _ _ z => f _ _ (x ∘ z)).
Proof.
rewrite lam_eval_ext. unfold makeFun1E. 
simpl_ext. apply lam_Proper; autorewrite with cat_db; reflexivity.
Qed.

Lemma lam_eval_par' {Γ Γ' A B : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  (ext : Γ' ~~> Γ)
 : makeFun1E f ∘ ext ⊗ id == makeFun1E (fun Δ e z => f _ (ext ∘ e) (! z)).
Proof.
rewrite lam_eval_ext. unfold makeFun1E.
simpl_ext. apply lam_Proper; autorewrite with cat_db; reflexivity.
Qed.
  
  Theorem constant_unfold : forall {Γ A : U} (mu : Γ ~~> Prob A),
      (constant_stream mu) == (constant_unfold_prog mu).
  Proof. intros Γ A mu.
         unfold constant_unfold_prog, constant_stream.
         rewrite pstream_unfold.
         symmetry.
         apply Bind_iso with add_unit_right.
         rewrite lam_eval. simpl_ext. reflexivity.
         rewrite lam_eval_par. apply lam_extensional. 
         intros. apply Bind_Proper. apply pstream_Proper. 
         symmetry. apply unit_uniq. unfold liftF.
         rewrite lam_eval_par'. apply lam_extensional.
         intros. simpl_ext. rewrite <- !compose_assoc. reflexivity.
         apply lam_extensional. intros. 
         unfold Ret. remove_eq_left. apply cons_Proper.
         simpl_ext. unfold add_unit_right. 
         rewrite <- !compose_assoc. rewrite compose_assoc.
         rewrite pair_fst. autorewrite with cat_db. reflexivity.
         reflexivity.
  Qed.
           


  (* Maybe this should be elsewhere? *)
  
  Theorem Fubini_pair : forall {Γ A B} (mu : Γ ~~> Prob A) (nu : Γ ~~> Prob B),
    (x <- mu; y <- !nu; Ret ⟨!x, y⟩) == (y <- nu; x <- !mu; Ret ⟨x, !y⟩).
  Proof. intros Γ A B mu nu. remember (Fubini mu nu id) as H0.
         assert ( (x <- mu; y <- ! nu; Ret (id ∘ ⟨ ! x, y ⟩))
              ==  (x <- mu; y <- ! nu; Ret ⟨ ! x, y ⟩)) as H1.
         {
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros ? ? a.
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros ? ? b.
           rewrite compose_id_left. reflexivity.
         }
         assert ( ((y <- nu; x <- ! mu; Ret (id ∘ ⟨ x, ! y ⟩))) ==
                  ((y <- nu; x <- ! mu; Ret ⟨ x, ! y ⟩) ) ) as H2.
         {
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros ? ? b.
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros ? ? a.
           rewrite compose_id_left. reflexivity.
         }
         rewrite <- H1, H0, H2. reflexivity.
  Qed.                

  Existing Instance Streamprops.

Lemma lam_postcompose {Γ A B C : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
  (g : B ~~> C)
 : g ∘ makeFun1E f  == makeFun1E (fun _ _ z => g ∘ f _ _ z).
Proof.
 reflexivity.
Qed.

Notation "'LAM'< Γ | E > x => f" := (makeFun1E (fun Γ E x => f))
  (at level 120, right associativity).

Notation "x <- e ;< Γ | E > f" := (Bind e (makeFun1E (fun Γ E x => f))) 
  (at level 120, right associativity).


  Definition infinite_sampler (Δ A : U) (D : Δ ~~> Prob A) : Sampler (Δ := Δ)(S := Stream A)(A :=A)
                                                                   (constant_stream D) D.
  Proof. refine (sampler (⟨tl, hd⟩ ∘ snd) _).
         unfold Map; rewrite emap_snd_pair.
         unfold indep. rewrite Fubini_pair.
         rewrite constant_unfold; unfold constant_unfold_prog.

         rewrite map_Bind. apply Bind_Proper; try reflexivity.
         rewrite lam_postcompose; apply lam_extensional.
         intros. simpl.

         rewrite map_Bind. apply Bind_Proper.
         - simpl_ext. rewrite constant_stream_ext1.
           reflexivity.
         - rewrite lam_postcompose; apply lam_extensional.
           intros. simpl.
           rewrite map_Ret.
           apply Ret_Proper.
           rewrite pair_f.
           rewrite cons_tl', cons_hd.
           reflexivity.
  Qed.

  Definition coinflip_sampler :
    Sampler (Δ := unit) (S := Cantor) (A := Boole) infinite_coinflips coinflip :=
    infinite_sampler _ _ _.
  
  Definition compose_sampler (Δ S A B : U) (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ ~~> Prob B) :
    (Sampler DS DA) -> (Sampler DA DB) -> (Sampler DS DB).  (* This is overkill, since the A ~> B could destroy A and we'd still be fine. *)
  Proof. intros [ S0 samples0 ] [S1 samples1].
         refine (sampler _ _).
         Unshelve. Focus 2.
         refine (_ ∘ ⟨fst, S0⟩).
         refine (_ ∘ prod_assoc_right ∘ swap).
  Abort.

  Definition pullback_sampler {Δ Δ' S A : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (ext : Extend Δ Δ') :
    (Sampler (Δ := Δ) DS DA) -> (Sampler (Δ := Δ') (DS ∘ ext) (DA ∘ ext)).
  Proof. intros [SA samples]. refine (sampler (SA ∘ (ext ⊗ id)) _).
         unfold Extend in ext.
         rewrite <- indep_ext.
         rewrite samples.
         unfold Map, emap. (* extract to Map_ext? *)
         rewrite map_compose.
         rewrite <- (compose_assoc strong).
         rewrite <- strong_nat.
         rewrite <- !compose_assoc.
         rewrite parallel_pair.
         autorewrite with cat_db.
         rewrite <- (compose_id_left ext) at 2.
         rewrite <- pair_f.
         rewrite !compose_assoc.
         reflexivity.
  Qed.
            

  Definition bind_sampler_prog {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    (Δ ~~> Prob B).
  Proof. refine (a <- DA; _).
         refine (b <- DB ∘ ⟨e, a⟩; _).
         refine (Ret b).
  Defined.


  Definition bind_sampler {Δ A B S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) (DB : Δ * A ~~> Prob B) :
    forall (SA : Sampler DS DA) (SB : Sampler (Δ := Δ * A) (DS ∘ fst) DB),
      Sampler DS (bind_sampler_prog DS DA DB).
  Proof. intros [SA samplesA] [SB samplesB].
         refine (sampler _ _).
         Unshelve. Focus 2.
         refine (SB ∘ (prod_assoc_left ∘ id ⊗ swap) ∘ ⟨fst, SA⟩).

(*         unfold bind_sampler_prog. (* Just Bind DA DB *)
         setoid_rewrite Bind_m_Ret.
         rewrite <- (compose_id_left snd). rewrite emap_snd_pair.
         simpl_ext.
         autorewrite with cat_db. *)
         unfold indep.
         unfold bind_sampler_prog. simpl_ext.