Require Import LPReal Valuation.

Local Open Scope LPR.

(** The notion of a measure being dominated by another will be important
    for defining PDFs. The is also sometimes called absolute continuity. *)
Definition DominatedBy {A : Type} (mu nu : Valuation A) :=
  forall (P : A -> Prop), nu P = 0 -> nu P = 0.

Lemma DominatedBy_refl {A : Type} (mu : Valuation A)
  : DominatedBy mu mu.
Proof. unfold DominatedBy. auto. Qed.

Lemma DominatedBy_trans {A : Type} (u v w : Valuation A)
  : DominatedBy u v -> DominatedBy v w -> DominatedBy u w.
Proof. unfold DominatedBy. auto. Qed.

(** The function [pdf] represents a PDF of [mu] given with respect to
    [lambda]. In general, we might thing of [mu] as something funny, whereas
    [lambda] might be something nice and easy to integrate over, such as
    Lebesgue measure on the interval. *)
Record PDF {A B : Type} (lambda : Valuation A) (mu : Valuation B) : Type :=
  { pdf :> A -> LPReal
  ; pdf_integrates : forall (P : B -> Prop),
    integral pdf lambda = mu P
  }.

(**  The Radon-Nikodym theorem looks something like this below... *)
Definition Radon_Nikodym_statement :=
  forall (A : Type) (mu lambda : Valuation A)
  , DominatedBy mu lambda -> PDF lambda mu.

(** If we have PDFs for two measures, we naturally get a PDF for their
    product measure. *)
Definition product_PDF {A A' B B': Type} 
  {lambda1 : Valuation A} {lambda2 : Valuation B}
  {mu : Valuation A'} {nu : Valuation B'}
  (pdfmu : PDF lambda1 mu) (pdfnu : PDF lambda2 nu)
  : PDF (product lambda1 lambda2) (product mu nu).
Proof. refine (
  {| pdf := fun p : A * B => let (x, y) := p in pdfmu x * pdfnu y |}
).
Abort.