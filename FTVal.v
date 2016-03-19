Require Import LPReal Frame.
Local Open Scope LPR.

Module FinVal.

Generalizable All Variables.
Section Defn.
Context {S : Type} {leS : S -> S -> Prop}.

Record T (mu : S -> LPReal) :=
  { monotone : forall a b, leS a b -> mu a <= mu b
  ; modular : forall a b minab maxab,
      @PreO.min _ leS a b minab
    -> @PreO.max _ leS a b maxab
    -> mu a + mu b = mu minab + mu maxab
  }.

End Defn.
End FinVal.

Module JoinVal. 
Section Defn.

Context {S} {ops : Lattice.Ops S}.
Variable bot : S.
Hypothesis bok_ok : @PreO.bottom _ Lattice.le bot.

Definition extend (mu : S -> LPReal) (U : S -> Prop) : LPReal :=
  LPRsup (fun s : { t | U t } => mu (projT1 s)).

Hypothesis Cov : S -> (S -> Prop) -> Prop.

Record T (mu : S -> LPReal) :=
  { monotone : forall a U, Cov a U -> mu a <= extend mu U
  ; modular : forall (a b : S), mu a + mu b = 
     mu (Lattice.min a b) + mu (Lattice.max a b)
  }.

End Defn.
End JoinVal.