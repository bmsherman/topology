Require Import Coq.Lists.List.
Import ListNotations.
Require Import ContPL.
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
  Context `{CMCprops : CMC_Props (U := U) (ccat := ccat) (cmc := cmc)}.
  Context `{Streamops : StreamOps (U := U) (ccat := ccat)}.
  Context `{mops : MeasOps U
(ccat := ccat) (Stream := Stream) (R := R) (LRnn := LRnn) (cmc := cmc) (sts := sts)}.
  Context `{SMDprops : SMonad_Props (U := U) (M := Prob) (ccat := ccat) (cmc := cmc) (smd := ProbMonad)}.

  Local Instance SMD : SMonad U Prob := ProbMonad.

 (*

Candidates for below I'm not sure about:
 (@to_from _ _ _ _ _ _), (@from_to _ _ _ _ _ _ _)

There's an argument to be made for adding parallel_pair, but I don't think I want it.

  *)
 
  Hint Rewrite
       (@compose_id_left _ _ _ _) (@compose_id_right _ _ _ _)
       (@pair_fst _ _ _ _) (@pair_snd _ _ _ _)
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

  Lemma emap_fst_pair : forall {Γ A B C : U} (f : Γ ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B),
      (emap (f ∘ fst)) ∘ ⟨h , k⟩ == ret ∘ f ∘ h.
  Proof. intros Γ A B C f h k. unfold emap. rewrite <- map_compose.
         rewrite <- (compose_assoc strong). unfold SMD. (* I'm slightly sad that unfold has to be there. *)
         rewrite fst_strong. rewrite -> compose_assoc.
         rewrite ret_nat. rewrite <- (compose_assoc _ fst). rewrite pair_fst.
         reflexivity.
  Defined.

  Lemma emap_snd_pair : forall {Γ A B C : U} (f : B ~~> C) (h : A ~~> Γ) (k : A ~~> Prob B),
      (emap (f ∘ snd)) ∘ ⟨h , k⟩ == (map f) ∘ k.
  Proof. intros Γ A B C f h k. unfold emap. rewrite <- map_compose.
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
  
  Theorem map_Bind' : forall {Γ A B C} (f : (Γ * A ~~> A) -> (Γ * A ~~> Prob B)) (e : Γ ~~> Prob A)(g : B ~~> C),
      ((map g) ∘ (x <- e; (f x))) == (x <- e; ((map g) ∘ (f x))).
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

  Theorem Bind'_push : forall {Γ Δ A B} (e : Γ ~~> Prob A) (f : Γ * A ~~> A -> Γ * A ~~> Prob B) (g : Δ ~~> Γ),
      (x <- e; f x) ∘ g == jmap (f snd) ∘ ⟨ g, e ∘ g ⟩.
  Proof. intros Γ Δ A B e f g.
         apply Bind_push.
  Defined.
  
  Theorem jmap_Bind_push : forall {Γ Δ A B C} (m : Γ * C ~~> Prob A) (f : (Γ * C) * A ~~> Prob B) (g : Δ ~~> Γ * Prob C),
      (jmap (Bind m f)) ∘ g == ( (jmap (f ∘ prod_assoc_left)) ∘ (id ⊗ inner_indep) ∘ prod_assoc_right ∘ ⟨g, (jmap m) ∘ g⟩).
  Proof. intros Γ Δ A B C m f g.
         unfold Bind, bind, jmap, emap.
  Abort.      

 
  Theorem Bind_m_Ret : forall {Γ A B} (m : Γ ~~> Prob A) (x : Γ * A ~~> B),
      (Bind m (Ret x)) == (emap x) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m x.
         unfold Bind, Ret, emap, bind. rewrite <- map_compose. rewrite (compose_assoc (map x)).
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
    
  Theorem Bind'_m_Ret : forall {Γ A B}  (m : Γ ~~> Prob A) (f : (Γ * A ~~> A) -> (Γ * A ~~> B)),
      (x <- m; Ret (f x)) == (emap (f snd)) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m f. apply Bind_m_Ret.
  Defined.

  Theorem Bind'_Ret_f : forall {Γ A B} (x : Γ ~~> A) (f : Γ * A ~~> A -> Γ * A ~~> Prob B),
      (y <- (Ret x); (f y)) == (f snd) ∘ ⟨id, x⟩.
  Proof. intros Γ A B x f. apply Bind_Ret_f.
  Defined.


(* This should be true, but I don't think it's useful enough to bother proving. Maybe if I need it later I will.
Theorem strength_indep : forall {A B : U}, (strong (A:=A)(B:=B)) == inner_indep ∘ (ret ⊗ id).
Proof. Abort.
 *)

  Lemma ret_Ret : forall {Γ A} (x : Γ ~~> A), (Ret x) == ret ∘ x.  (*TODO is there a non-stupid way to do this? *)
  Proof. unfold Ret. reflexivity.
  Defined.

  Lemma Ret_f : forall {A B C} (x : A ~~> B) (f : B ~~> C), (Ret f) ∘ x == Ret (f ∘ x).
  Proof. intros A B C x f.
         unfold Ret; rewrite compose_assoc; reflexivity.
  Defined.


  Require Import Morphisms.

  Instance indep_ext1 {Γ A B} : Proper (eq ==> eq ==> eq) (@indep Γ A B).
  Proof.
  unfold Proper, respectful. intros. unfold indep. apply Bind_Proper.
  assumption. apply lam_extensional. intros. 
  apply Bind_Proper. rewrite <- H1. reflexivity. reflexivity.
  Qed.

  Lemma Bind_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> Prob A)
    (f : Δ * A ~~> Prob B), Bind x f ∘ g == Bind (x ∘ g) (f ∘ (g ⊗ id)).
  Proof.
  intros. unfold Bind. unfold bind. rewrite <- !(compose_assoc _ _ join).
  apply compose_Proper. reflexivity. rewrite <- map_compose.
  rewrite <- !(compose_assoc _ _ (map f)). 
  apply compose_Proper. reflexivity.
  rewrite compose_assoc. rewrite <- strong_nat. 
  rewrite <- !(compose_assoc _ _ strong).
  apply compose_Proper. reflexivity.
  rewrite map_id. 
  rewrite parallel_pair. autorewrite with cat_db.
  rewrite pair_f. autorewrite with cat_db. reflexivity.
  Qed.



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
  unfold parallel. autorewrite with cat_db. reflexivity.
  rewrite Ret_f. apply Ret_Proper.
  rewrite pair_f. apply pair_Proper.
  unfold Lift, Extend_Prod, Extend_Refl; simpl.
  unfold parallel.
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
           unfold Lift, Extend_Refl, Extend_Prod. (* I should automate this maybe? *)
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
           unfold Lift, Extend_Refl, Extend_Prod.
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
  
  Record Sampler {Δ A S : U} (DS : Δ ~~> Prob S) (DA : Δ ~~> Prob A) : Type :=
    sampler
      {
        sample : Δ * S ~~> S * A;
        sampling_cond : (indep DS DA) == (emap sample) ∘ ⟨id, DS⟩
                                                       (* Maybe replace RHS with something more program-y??? EG: (s <- DS; Ret sample). (that one looks weird because it draws s but appears to never use it.)  *) 
      }.

      Arguments sampler {Δ} {A} {S} {DS} {DA} sample sampling_cond.
  
  
  Section Constant_Sampler.
    
    Definition const_sampler {Δ A S : U} {D : Δ ~~> Prob S} {x : Δ ~~> A} :
      Sampler (Δ := Δ) (A := A) (S := S) D (Ret x).
    Proof. refine (sampler ⟨snd, x ∘ fst⟩ _).       
           unfold indep. 
           unfold Lift, Extend_Prod, Extend_Refl. simpl.
           rewrite bind_extensional. Focus 2.
           intros a.
           setoid_rewrite Ret_f.
           setoid_rewrite Bind'_Ret_f.
           rewrite Ret_f.
           rewrite pair_f. 
           reflexivity.
           simpl.
           setoid_rewrite Ret_f. setoid_rewrite pair_f.
           autorewrite with cat_db.
           rewrite <- (compose_assoc _ fst snd). autorewrite with cat_db.
           rewrite Bind_m_Ret.
           (* rewrite Bind'_m_Ret. // If the RHS of the sampling condition becomes a program. *)
           reflexivity.
Defined.
    
    
  End Constant_Sampler.
  
  Section Coinflip_Sampler.
    
    Definition Boole := unit + unit.
    Definition Cantor := Stream Boole.
    
    Definition infinite_coinflips : unit ~~> Prob Cantor := pstream (MeasOps := mops) coinflip (coinflip ∘ tt).
    
    Definition coinflip_sampler {Δ : U} :
      Sampler (Δ := Δ) (S := Cantor) (A := Boole) (infinite_coinflips ∘ tt) (coinflip ∘ tt).
    Proof.
      refine (sampler (⟨tl, hd⟩ ∘ snd) _).
      rewrite emap_snd_pair.
      unfold indep, Lift, Extend_Prod, Extend_Refl. simpl.
      
    Abort.
    
  End Coinflip_Sampler.
  