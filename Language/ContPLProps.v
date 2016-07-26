Require Import Coq.Lists.List.
Import ListNotations.
Require Import Morphisms.
Require Import Spec.Category.
Require Import Spec.SMonad.
Require Import Language.ContPL.
Import Category.
Import ContPL.

Local Open Scope morph.
Local Open Scope obj.

Section ContPLProps.
  
  Context {U : Type}.
  Context `{CMCprops : CMC_Props (U := U)}.
  (* Context `{mops : MeasOps U (ccat := ccat) (cmc := cmc) (cmcprops := CMCprops) }. *)
  Context `{SMDProps : SMonad_Props (U := U) (ccat := ccat) (cmc := cmc)
     (cmcprops := CMCprops)
     }.
  
  
  Existing Instance smd.
  
  Hint Rewrite
       (@compose_id_left _ _ _ _) (@compose_id_right _ _ _ _)
       (@pair_fst _ _ _ _) (@pair_snd _ _ _ _)
       (@parallel_fst _ _ _ _) (@parallel_snd _ _ _ _)
       (@unit_uniq _ _ _ _)
       (@map_id _ M _ _ _ _ _)
       (@join_map_ret _ _ _ _ _ _ _) (@join_ret  _ _ _ _ _ _ _)
       (@strength_ret _ _ _ _ _ _ _)
       (*@fst_strong _ _ _ _*) (@snd_strong _ _ _ _ _ _ _)
    : cat_db.
  
  
  Notation "'LAM'<< Γ | E >> x => f" := (makeFun1E (fun Γ E x => f))
                                          (at level 120, right associativity). 
  
  Notation "x <- e ;<< Γ | E >> f" := (Bind e (makeFun1E (fun Γ E x => f))) 
                                        (at level 120, right associativity).
  
  Ltac simpl_ext := unfold liftF, Lift, Extend_Prod, Extend_Refl, extend;
                    repeat rewrite compose_id_right.
  
  
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
  
  Lemma lam_id : forall {P Q : U}, ('LAM'<< _ | _ >> x => x) == snd (A:=P)(B:=Q).
  Proof. intros P Q. unfold makeFun1E. reflexivity.
  Defined.
  
  Definition swap' {A B : U} : A * B ~~> B * A :=
    ('LAM'<< _ | _ >> x =>
                 let a := fst ∘ x in let b := snd ∘ x in ⟨b, a⟩) ∘ add_unit_left.
  
  Definition indep {Γ A B : U} (DA : Γ ~~> M A) (DB : Γ ~~> M B) : (Γ ~~> M (A * B)) :=
      ( a <-  DA;<< _ | _ >>
                         b <- !DB;<< _ | _ >>
                                          Ret ⟨!a, b⟩).
  
  Definition inner_indep {A B : U} : (M A) * (M B) ~~> M (A * B) :=
    indep (Γ := M A * M B) fst snd.
  Lemma emap_fst_pair : forall {Γ A B C : U} (f : Γ ~~> C) (h : A ~~> Γ) (k : A ~~> M B),
      (emap (f ∘ fst)) ∘ ⟨h , k⟩ == ret ∘ f ∘ h.
  Proof. intros Γ A B C f h k. unfold emap. rewrite map_compose.
         rewrite <- (compose_assoc strong). Abort. (*
         rewrite fst_strong. rewrite -> compose_assoc.
         rewrite ret_nat. rewrite <- (compose_assoc _ fst). rewrite pair_fst.
         reflexivity. *)

         
  Lemma emap_snd_pair : forall {Γ A B C : U} (f : B ~~> C) (h : A ~~> Γ) (k : A ~~> M B),
      (emap (f ∘ snd)) ∘ ⟨h , k⟩ == (map f) ∘ k.
  Proof. intros Γ A B C f h k. unfold emap. rewrite map_compose.
         rewrite <- (compose_assoc _ (map snd)).
         rewrite snd_strong. rewrite <- (compose_assoc _ snd). rewrite pair_snd. reflexivity.
  Defined.
  
  Lemma emap_snd : forall {Γ A B : U} (h : A ~~> Γ) (k : A ~~> M B),
      (emap snd) ∘ ⟨h, k⟩ == k.
  Proof. intros Γ A B h k. rewrite <- (compose_id_left snd).
         rewrite emap_snd_pair.
         autorewrite with cat_db. reflexivity.
  Defined.
  
  Theorem map_Ret : forall {Γ A B : U} (f : Γ ~~> A) (h : A ~~> B),
      (map h) ∘ (Ret f) == Ret (h ∘ f).
  Proof. intros Γ A B f h.
         unfold Ret. rewrite compose_assoc. rewrite <- ret_nat. rewrite compose_assoc.
         reflexivity.
  Defined.

  Theorem map_Bind : forall {Γ A B C} (f : Γ * A ~~> M B) (m : Γ ~~> M A) (g : B ~~> C),
      (map g) ∘ (Bind m f) == Bind m ((map g) ∘ f).
  Proof.
    intros Γ A B C f m g.
    unfold Bind. unfold bind. rewrite (compose_assoc _ (join ∘ map f)). rewrite (compose_assoc _ join).
    rewrite join_nat. rewrite <- (compose_assoc _ (map (map g))). rewrite map_compose. reflexivity.
  Defined.
  
  Theorem map_Bind' : forall {Γ A B C}
      (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> M B) (e : Γ ~~> M A) (g : B ~~> C),
      (map g) ∘ Bind e (makeFun1E f) == Bind e (map g ∘ makeFun1E f).
    intros Γ A B C f e g.
    apply map_Bind.
  Defined.

  
  Theorem Bind_emap : forall {Γ A B} (m : Γ ~~> M A)(f : Γ * A ~~> M B),
      (Bind m f) == join ∘ (emap f) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m f.
         unfold Bind, bind, emap. rewrite compose_assoc, compose_assoc. reflexivity.
  Defined.

  Definition jmap {Γ A B} (f : Γ * A ~~> M B) : Γ * M A ~~> M B :=
    join ∘ (emap f).
  
  Theorem Bind_push : forall {Γ Δ A B} (m : Γ ~~> M A) (f : Γ * A ~~> M B) (g : Δ ~~> Γ),
      (Bind m f) ∘ g == (jmap f) ∘ ⟨g, m ∘ g⟩.
  Proof. intros Γ Δ A B m f g.
         unfold Bind, bind, jmap, emap. rewrite compose_assoc, compose_assoc.
         rewrite <- (compose_assoc g). rewrite pair_f, compose_id_left.
         reflexivity.
  Defined.
 
  Theorem Bind_m_Ret : forall {Γ A B} (m : Γ ~~> M A) (x : Γ * A ~~> B),
      (Bind m (Ret x)) == (emap x) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m x.
         unfold Bind, Ret, emap, bind. rewrite map_compose. rewrite (compose_assoc (map x)).
         rewrite join_map_ret, compose_id_left. rewrite compose_assoc. reflexivity.
  Defined.

  Theorem Bind_Ret_f : forall {Γ A B} (x : Γ ~~> A) (f : Γ * A ~~> M B),
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
   

  Theorem Bind'_m_Ret : forall {Γ A B}  (m : Γ ~~> M A) (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> B),
      (x <- m ;<< Δ | ext >> (Ret (f Δ ext x))) ==  (emap (makeFun1E f)) ∘ ⟨id, m⟩.
  Proof. intros Γ A B m f.
         apply Bind_m_Ret.
  Defined.


  Theorem Bind'_Ret_f : forall {Γ A B} (x : Γ ~~> A) 
  (f : forall Δ, Extend Γ Δ -> Δ ~~> A -> Δ ~~> M B),
      Bind (Ret x) (makeFun1E f) == (makeFun1E f) ∘ ⟨id, x⟩.
  Proof. intros Γ A B x f. apply Bind_Ret_f.
  Defined.
  
  Theorem Bind_Bind : forall {Γ A B C : U} (m : Γ ~~> M A) (f : Γ * A ~~> M B) (g : Γ * B ~~> M C),
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
         assert (prod_assoc_left ∘ ⟨fst, id⟩ == diagonal (A:=Γ) ⊗ id(A:=M A)) as Δ2.
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
    
  Theorem Bind_map_f : forall {Γ A B C} (m : Γ ~~> M A) (g : A ~~> B) (f : Γ * B ~~> M C),
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
         rewrite compose_id_left.
         rewrite !compose_assoc; reflexivity.
  Qed.


  
  (*
  Theorem Bind'_map_f : forall {Γ A B C} (m : Γ ~~> M A) (g : A ~~> B) (f : Γ * B ~~> B -> Γ * B ~~> M C),
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
  
  

  Global Instance indep_ext1 {Γ A B} : Proper (eq ==> eq ==> eq) (@indep Γ A B).
  Proof.
    unfold Proper, respectful. intros. unfold indep. apply Bind_Proper.
    assumption. apply lam_extensional. intros. 
    apply Bind_Proper. unfold Lift, Extend_Prod. apply compose_Proper. 
    assumption. reflexivity.  reflexivity.
  Qed.
  
  Lemma Bind_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> M A)
                     (f : Δ * A ~~> M B), Bind x f ∘ g == Bind (x ∘ g) (f ∘ (g ⊗ id)).
  Proof.
    intros. unfold Bind. unfold bind. rewrite <- !(compose_assoc _ _ join).
    apply compose_Proper. reflexivity. rewrite map_compose.
    rewrite <- !(compose_assoc _ _ (map f)). 
    apply compose_Proper. reflexivity.
    rewrite compose_assoc. rewrite <- strong_nat. 
    rewrite <- !(compose_assoc _ _ strong).
    apply compose_Proper. reflexivity.
    rewrite map_id. 
    rewrite parallel_pair.
    rewrite pair_f. autorewrite with cat_db. reflexivity.
  Qed.
  
  
  Theorem Bind'_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> M A)
                        (f : forall Δ0 (ext : Extend Δ Δ0), Δ0 ~~> A -> Δ0 ~~> M B),
      ((a <- x;<< Δ' | eΔ >>  (f Δ' eΔ a)) ∘ g) == (a <- x ∘ g ;<< Γ' | eΓ >> (f Γ' (g ∘ eΓ) a)).
  (*b <- x ∘ g; (f snd) ∘ ⟨g ∘ fst, b⟩). *)
  Proof.
    intros. 
    rewrite Bind_ext. apply Bind_Proper; try reflexivity. rewrite lam_eval_ext.
    simpl_ext.
    apply lam_extensional; intros.
    apply (lam_Proper f); autorewrite with cat_db; reflexivity.
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
  
  Theorem indep_ext : forall Γ Δ A B (g : Γ ~~> Δ) (x : Δ ~~> M A)
                        (y : Δ ~~> M B), indep x y ∘ g == indep (x ∘ g) (y ∘ g).
  Proof.
    intros. unfold indep. rewrite Bind_ext. apply Bind_Proper. 
    reflexivity. unfold makeFun1E. 
    rewrite Bind_ext.
    apply Bind_Proper. unfold Lift, Extend_Prod, Extend_Refl.
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
    autorewrite with cat_db. reflexivity.
  Qed.
  
  Theorem call_indep : forall Γ A B (mu : Γ ~~> M A) (nu : Γ ~~> M B),
      Call (makeFun [M A; M B] (fun _ => indep)) mu nu == indep mu nu.
  Proof.
    intros. apply (call_inv (fun _ => indep)).
    - intros. typeclasses eauto.
    - intros. apply indep_ext.
  Qed.
  
(* Abort.  Theorem marg_inner_indep : forall {A B : U}, (marg (A:=A)(B:=B)) ∘ inner_indep == id.
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
           rewrite emap_snd.
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
           
  Defined. *)
  
  Definition Map {Γ A B : U} (f : Γ * A ~~> B) (mu : Γ ~~> M A)
    : Γ ~~> M B := emap f ∘ ⟨ id , mu ⟩.

  Global Instance Map_Proper {Γ A B : U} : Proper (eq (A:=Γ*A)(B:=B) ==> eq ==> eq) Map.
  Proof. unfold Proper, respectful.
         intros. unfold Map.
         rewrite H. rewrite H0.
         reflexivity.
  Qed.
  
  Lemma Bind_iso {Γ A A' B : U} (p : A ~~> A') 
        (mu : Γ ~~> M A) (mu' : Γ ~~> M A')
        (f : Γ * A ~~> M B) (f' : Γ * A' ~~> M B)
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
  
  Theorem shrug : forall (A B C : U) (h : C ~~> A) (k : C ~~> B), swap' ∘ ⟨h, k⟩ == ⟨k, h⟩.
  Proof. intros A B C h k. unfold swap'. unfold add_unit_left. rewrite <- compose_assoc.
         rewrite pair_f. autorewrite with cat_db.
         rewrite lam_eval. autorewrite with cat_db. reflexivity.
  Defined.

  Theorem Bind'_Bind' : forall {Δ A B C : U} (m : Δ ~~> M A)
                          (f : forall Δ0 (ext : Extend Δ Δ0), Δ0 ~~> A -> Δ0 ~~> M B)
                          (g : forall Δ0 (ext : Extend Δ Δ0), Δ0 ~~> B -> Δ0 ~~> M C),
      (x <- (y <- m ;<< Δ' | eΔ >> (f Δ' eΔ y));<< Δ'' | eΔ' >> (g Δ'' eΔ' x)) ==
      (y <- m ;<< Δ' | eΔ >> x <- (f Δ' eΔ y);<< Δ'' | eΔ' >> (g Δ'' (eΔ ∘ eΔ') x)).
  Proof. intros. 
         rewrite Bind_Bind.
         repeat (apply Bind_Proper; try reflexivity).
         rewrite lam_eval_ext.
         apply lam_extensional.
         intros. simpl_ext.
         apply (lam_Proper g); remove_eq_right; autorewrite with cat_db; reflexivity.
  Qed.  
  
  Lemma lam_postcompose {Γ A B C : U} (f : forall Δ (ext : Extend Γ Δ), Δ ~~> A -> Δ ~~> B)
        (g : B ~~> C)
    : g ∘ makeFun1E f  == makeFun1E (fun _ _ z => g ∘ f _ _ z).
  Proof.
    reflexivity.
  Qed.
  
  Lemma Map_prog : forall {Δ A S : U} (DS : Δ ~~> M S) (SA : Δ * S ~~> A),
      (Map SA DS) == (s <- DS;<< _ | e >> Ret (ap2 SA e s)).
  Proof. intros.
         unfold Map.
         rewrite Bind'_m_Ret.
         remove_eq_right. apply map_Proper.
         unfold makeFun1E, ap2, extend, Extend_Prod, Extend_Refl.
         assert (forall {P Q : U}, ⟨id ∘ fst, snd⟩ == id (A:=P*Q)).
         { intros. apply proj_eq; (autorewrite with cat_db; reflexivity). }
         rewrite H, compose_id_right. reflexivity.
  Qed.
  
  Lemma ap2_ext_eval : forall {Δ A B : U} (f : forall Δ' (ext : Extend Δ Δ'), Δ' ~~> A -> Δ' ~~> B)
                         (Δ0 : U) (e0 : Extend Δ Δ0) (a0 : Δ0 ~~> A),
      (ap2 ('LAM'<< Δ' | e >> a => f Δ' e a) e0 a0) == f Δ0 e0 a0.
  Proof. intros Δ A B f Δ0 e0 a0. unfold ap2. 
         apply lam_eval.
  Qed.

         
         
  
  Definition Map_post : forall {Γ A B C : U} (F : Γ * A ~~> B) (h : Γ ~~> M A) (g : B ~~> C),
      Map (g ∘ F) h == (map g) ∘ Map F h.
  Proof. intros. unfold Map, emap. remove_eq_right. apply map_compose.
  Qed.


    Theorem Map_compose : forall {Γ A B C : U} (f0 : Γ * A ~~> B) (f1 : Γ * B ~~> C) (h : Γ ~~> M A),
      Map f1 (Map f0 h) == Map (f1 ∘ ⟨fst, f0⟩) h.
  Proof. intros Γ A B C f0 f1 h.
         unfold Map.
         unfold emap.
         rewrite map_compose.
         remove_eq_left.
         rewrite pair_parallel_id.
         rewrite compose_assoc.
         rewrite strong_nat.
         rewrite (pair_parallel_diagonal fst f0).
         assert (parallel (B:=Γ) (fst (B:=A)) f0 == (id ⊗ f0) ∘ (fst ⊗ id)).
         { apply proj_eq. rewrite compose_assoc. rewrite !parallel_fst. autorewrite with cat_db. reflexivity. rewrite compose_assoc. rewrite !parallel_snd. rewrite <- compose_assoc. rewrite parallel_snd. rewrite compose_id_left; reflexivity. }
         rewrite H. rewrite !map_compose. remove_eq_left.
         rewrite pair_parallel_id.
         rewrite compose_assoc.
         rewrite strength_compose.
         rewrite <- !compose_assoc.
         unfold prod_assoc_left; autorewrite with cat_db.
         rewrite pair_f; autorewrite with cat_db.
         rewrite parallel_pair, <- compose_assoc; autorewrite with cat_db.
         assert (⟨⟨id, id⟩, h⟩ == (diagonal ⊗ map id) ∘ ⟨id, h⟩).
         { apply proj_eq. unfold diagonal. rewrite map_id. rewrite compose_assoc.
           autorewrite with cat_db. rewrite <- compose_assoc. autorewrite with cat_db.
           reflexivity. unfold diagonal. rewrite map_id. rewrite compose_assoc.
           autorewrite with cat_db. reflexivity.
         } rewrite H0. remove_eq_right.
         rewrite <- compose_assoc. rewrite strong_nat. remove_eq_right.
         rewrite <- !map_compose.
         apply map_proper.
         apply proj_eq.
         unfold prod_assoc_right, diagonal.
         rewrite !compose_assoc. autorewrite with cat_db.
         rewrite <- !compose_assoc. autorewrite with cat_db.
         rewrite compose_assoc. autorewrite with cat_db.
         reflexivity.
         unfold prod_assoc_right, diagonal.
         rewrite !compose_assoc. autorewrite with cat_db.
         rewrite <- pair_id. apply proj_eq.
         rewrite !compose_assoc. autorewrite with cat_db.
         rewrite <- !compose_assoc. autorewrite with cat_db.
         rewrite !compose_assoc. autorewrite with cat_db.
         reflexivity.
         rewrite !compose_assoc. autorewrite with cat_db.
         reflexivity.
  Qed.


    Global Instance indep_Proper {Γ A B : U} : Proper (eq ==> eq ==> eq (A:=Γ)) (indep (A:=A)(B:=B)).
  Proof. unfold Proper, respectful.
         intros.
         unfold indep. repeat (apply Bind_Proper; try assumption; try reflexivity).
         unfold Lift. rewrite H0. reflexivity.
  Qed.

  
  
  Theorem Bind_Map_indep : forall {Γ A B C : U} (m : Γ ~~> M A) (F : Γ * A * C ~~> B) (h : Γ ~~> M C),
      Bind m (Map F (h ∘ fst)) == Map (F ∘ prod_assoc_left) (indep m h).
  Proof. intros Γ A B C m F h.
         rewrite !Map_prog.
         unfold indep.
         rewrite Bind'_Bind'.
         apply Bind_Proper; try reflexivity.
         unfold makeFun1E at 2.
         simpl_ext. rewrite Bind'_Bind'.
         apply Bind_Proper. autorewrite with cat_db. reflexivity.
         apply lam_extensional.
         intros.
         rewrite Bind'_Ret_f. unfold makeFun1E at 1.
         unfold Ret. remove_eq_left.
         simpl_ext.
         unfold ap2. remove_eq_left.
         apply proj_eq.
         unfold prod_assoc_left. rewrite !compose_assoc.
         - unfold Extend in ext.
           autorewrite with cat_db.
           rewrite parallel_pair; autorewrite with cat_db.
           rewrite pair_f; autorewrite with cat_db.
           rewrite <- !compose_assoc; autorewrite with cat_db.
           rewrite <- pair_f. rewrite pair_id. rewrite compose_id_left.
           reflexivity.
         - unfold Extend in ext.
           unfold prod_assoc_left.
           autorewrite with cat_db.
           rewrite !compose_assoc; autorewrite with cat_db.
           rewrite <- !compose_assoc; autorewrite with cat_db.
           rewrite pair_f; autorewrite with cat_db.
           reflexivity.
  Qed.

     Lemma parallel_indep : forall {Γ A B A' B'} (f : Γ ~~> M A) (g : Γ ~~> M B)
                             (h : A ~~> A') (k : B ~~> B'),
        (map (h ⊗ k)) ∘ (indep f g) == (indep ((map h) ∘ f) ((map k) ∘ g)).
    Proof. intros Γ A B A' B' f g h k.
           unfold indep.
           rewrite map_Bind'; rewrite lam_postcompose.
           rewrite Bind_map_f.
           apply Bind_Proper; try reflexivity.
           rewrite lam_eval_par.
           apply lam_extensional; intros.

           simpl_ext. rewrite <- !compose_assoc.
           
           rewrite map_Bind'; rewrite lam_postcompose.
           rewrite Bind_map_f.
           apply Bind_Proper; try reflexivity.
           rewrite lam_eval_par.
           apply lam_extensional; intros.

           rewrite map_Ret.
           apply Ret_Proper.

           rewrite parallel_pair. rewrite compose_assoc.
           reflexivity.
    Qed.

    Corollary parallel_indep_right : forall {Γ A B B'} (f : Γ ~~> M A) (g : Γ ~~> M B)
                                       (k : B ~~> B'),
        (map (id ⊗ k)) ∘ (indep f g) == (indep f ((map k) ∘ g)).
    Proof. intros Γ A B B' f g k.
           pose proof (parallel_indep f g id k). rewrite H.
           apply indep_Proper; try reflexivity.
           autorewrite with cat_db. reflexivity.
    Qed.

    Corollary parallel_indep_left : forall {Γ A B A'} (f : Γ ~~> M A) (g : Γ ~~> M B)
                                       (h : A ~~> A'),
        (map (h ⊗ id)) ∘ (indep f g) == (indep ((map h) ∘ f) g).
    Proof. intros Γ A B B' f g h.
           pose proof (parallel_indep f g h id). rewrite H.
           apply indep_Proper; try reflexivity.
           autorewrite with cat_db. reflexivity.
    Qed.


    Theorem indep_assoc : forall {Γ A B C} (f : Γ ~~> M A) (g : Γ ~~> M B) (h : Γ ~~> M C),
        indep (indep f g) h == map prod_assoc_left ∘ indep f (indep g h).
    Proof.
      intros Γ A B C f g h.
      unfold indep.
      rewrite Bind'_Bind'.
      rewrite map_Bind'; rewrite lam_postcompose.
      apply Bind_Proper; try reflexivity.

      apply lam_extensional; intros.
      rewrite map_Bind'; rewrite lam_postcompose.
      simpl_ext.
      rewrite Bind'_ext.
      rewrite !Bind'_Bind'.
      apply Bind_Proper; try reflexivity.

      apply lam_extensional; intros.
      rewrite Bind'_Ret_f.
      rewrite lam_eval.
      rewrite Bind'_Bind'.
      apply Bind_Proper; try reflexivity.

      remove_eq_left. apply compose_id_right.

      apply lam_extensional; intros.
      rewrite Bind'_Ret_f.
      rewrite lam_eval.
      rewrite map_Ret. apply Ret_Proper.
      unfold Extend in ext, ext0, ext1.
      unfold prod_assoc_left.
      autorewrite with cat_db. rewrite !pair_f.
      rewrite parallel_pair, <- !compose_assoc.
      autorewrite with cat_db. reflexivity.
    Qed.

    Corollary indep_assoc' : forall {Γ A B C} (f : Γ ~~> M A) (g : Γ ~~> M B) (h : Γ ~~> M C),
        indep f (indep g h) == map prod_assoc_right ∘ indep (indep f g) h.
    Proof. intros Γ A B C f g h.
           rewrite indep_assoc.
           rewrite <- compose_id_left at 1.
           remove_eq_right.
           rewrite <- map_compose, <- map_id. apply map_Proper.
           pose proof (from_to (Iso_Prod_Assoc (A:=A) (B:=B)(C:=C))). simpl in H.
           symmetry. apply H.
    Qed.
  
End ContPLProps.