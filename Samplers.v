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
      (f : Γ * A ~~> A -> Γ * A ~~> Prob B) (e : Γ ~~> Prob A) (g : B ~~> C),
      (map g) ∘ (x <- e; (f x)) == (x <- e; ((map g) ∘ (f x))).
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
    
  Theorem Bind'_m_Ret : forall {Γ A B}  (m : Γ ~~> Prob A) (f : forall (m : U), Γ * m ~~> A -> Γ * m ~~> B),
      (x <- m; Ret (f _ x)) ==  (emap (makeFun1E (f A)) ∘ ⟨id, m⟩).
  Proof. intros Γ A B m f.
         apply Bind_m_Ret.
  Defined.

  Theorem Bind'_Ret_f : forall {Γ A B} (x : Γ ~~> A) (f : Γ * A ~~> A -> Γ * A ~~> Prob B),
      (y <- (Ret x); (f y)) == (makeFun1E f) ∘ ⟨id, x⟩.
  Proof. intros Γ A B x f. apply Bind_Ret_f.
  Defined.
  
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
  
  Theorem Bind'_map_f : forall {Γ A B C} (m : Γ ~~> Prob A) (g : A ~~> B) (f : Γ * B ~~> B -> Γ * B ~~> Prob C),
      (x <- (map g) ∘ m; (f x)) == (x <- m; (f snd) ∘ (id ⊗ g)).
  Proof. intros Γ A B C m g f.
         apply  Bind_map_f. 
  Qed.
  

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
  apply Bind_Proper. unfold Lift, Extend_Prod. rewrite <- H0. reflexivity. reflexivity.
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
  rewrite Ret_ext. apply Ret_Proper.
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
           unfold makeFun1E.
           rewrite Ret_ext.
           rewrite pair_f. 
           reflexivity.
           simpl.
           setoid_rewrite Ret_ext. setoid_rewrite pair_f.
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
         - unfold makeFun1E, Lift, Extend_Prod, Extend_Refl.
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
  
  Theorem constant_unfold : forall {Γ A : U} (mu : Γ ~~> Prob A),
      (constant_stream mu) == (constant_unfold_prog mu).
  Proof. intros Γ A mu.
         unfold constant_unfold_prog, constant_stream.
         rewrite pstream_unfold.
         unfold makeFun1E at 1.
         unfold Lift, Extend_Prod, Extend_Refl.
         rewrite <- compose_assoc, <- compose_assoc.
         unfold liftF.
         autorewrite with cat_db.
         rewrite Bind'_map_f.
         apply Bind_Proper.
         { reflexivity. }
         unfold makeFun1E at 1.
         unfold makeFun1E at 3.
         unfold makeFun1E at 3.
         unfold makeFun1E at 1.
         rewrite (unit_uniq (snd ∘ snd)).
         rewrite Bind_ext.
         autorewrite with cat_db.
         apply Bind_Proper.
         - rewrite pstream_ext1. autorewrite with cat_db.
           apply pstream_Proper; try reflexivity.
           rewrite <- !(compose_assoc _ _ (map add_unit_right)).
           apply compose_Proper; try reflexivity.
           rewrite <- !(compose_assoc _ _ mu).
           apply compose_Proper; try reflexivity.
           (* This is the sort of goal that hopefully one day we can automate. *)
           rewrite parallel_fst.
           rewrite <- compose_assoc.
           rewrite parallel_fst.
           rewrite compose_assoc.
           rewrite parallel_fst.
           rewrite compose_id_left.
           reflexivity.
         - (* Maybe there's a lam_ext for such situations? *)
           unfold makeFun1E. 
           rewrite Ret_ext. apply Ret_Proper.
           rewrite cons_ext.
           apply cons_Proper.
         +  autorewrite with cat_db.
            rewrite <- !compose_assoc.
            rewrite !parallel_fst.
            rewrite (compose_assoc fst).
            rewrite parallel_snd.
            rewrite !compose_assoc.
            unfold add_unit_right.
            autorewrite with cat_db.
            reflexivity.
         + rewrite parallel_snd. rewrite compose_id_left.
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
           apply lam_extensional; intros a.
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros b.
           rewrite compose_id_left. reflexivity.
         }
         assert ( ((y <- nu; x <- ! mu; Ret (id ∘ ⟨ x, ! y ⟩))) ==
                  ((y <- nu; x <- ! mu; Ret ⟨ x, ! y ⟩) ) ) as H2.
         {
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros b.
           apply Bind_Proper; try reflexivity.
           apply lam_extensional; intros a.
           rewrite compose_id_left. reflexivity.
         }
         rewrite <- H1, H0, H2. reflexivity.
  Qed.                

  Existing Instance Streamprops.
  
  Definition coinflip_sampler {Δ : U} :
      Sampler (Δ := Δ) (S := Cantor) (A := Boole) (infinite_coinflips ∘ tt) (coinflip ∘ tt).
  Proof.
    refine (sampler (⟨tl, hd⟩ ∘ snd) _). unfold Map.
    rewrite emap_snd_pair.
    unfold indep.
    rewrite Fubini_pair.
    unfold infinite_coinflips at 2.
    rewrite constant_unfold.
    unfold constant_unfold_prog.
    rewrite Bind'_ext.
    setoid_rewrite Bind'_ext.
    setoid_rewrite Ret_ext.
    rewrite map_Bind.
    setoid_rewrite map_Bind.
    setoid_rewrite map_Ret.
    setoid_rewrite pair_f.
    rewrite compose_assoc.
    rewrite cons_tl'.
    rewrite compose_assoc. rewrite cons_hd.
    autorewrite with cat_db.
    unfold Lift at 4, Extend_Prod, Extend_Refl.
    rewrite <- (compose_assoc _ _ snd).
    rewrite <- (compose_assoc _ _ id).
    autorewrite with cat_db.
    rewrite !compose_assoc.
    autorewrite with cat_db.
    apply Bind_Proper; try reflexivity.
    unfold makeFun1E.
    unfold Lift, Extend_Prod, Extend_Refl.
    unfold infinite_coinflips.
    apply Bind_Proper.
    - rewrite constant_stream_ext1.
      autorewrite with cat_db.
      rewrite <- !compose_assoc.
      autorewrite with cat_db. reflexivity.
    - autorewrite with cat_db. reflexivity.
  Qed.