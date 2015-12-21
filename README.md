An exploration of how to formalize probability in Coq.

## Files

- Qnn.v : Non-negative rational numbers
  - semiring (0, 1, addition, multiplication)
  - truncated subtraction

- LPReal.v : Non-negative lower real numbers encoded as lower Dedekind cuts
  - semiring (0, 1, addition, multiplication)
  - indicators of logical propositions
  - supremum, min, max

- Valuation.v : The vast majority of the interesting code
  - definition of valuations and continuous valuations
  - definition of simple functions, integration, and assumption
    of many facts about integration
  - operations for construction valuations: `unit`, `bind`, `join`,
    `map`, `product`, `restrict`, `inject`
  - attempted definition of measurability
  - supremum and fixpoint valuations, continuity of valuation functionals
  - principles for constructing and reasoning about 
    finite and countable measures
  - examples: probabilistic choice, Bernoulli, binomial, geometric
  - example of Geom/Geom/1 queue system

- Sample.v : Definition of random samplers
  - Samplers of the form `R -> R * A`, where we sample random values of `A`
    from a random seed `R`
  - Probability distributions over streams
  - Partial computations, partial valuations, and partial samplers

- PDF.v : (Very incomplete) characterization of PDFs of measures relative
  to more standard measures

- Iso.v : Definition of isomorphisms (bijections)

- Finite.v : Definition and characterization of finite types

- Prob.v, Prob2.v, Prob3.v : these files are old. They were three different
attempts to encode probability in Coq. In Prob.v and Prob2.v, I was hoping
to base everything off of the Cantor space, where everything is naturally
sample-able.
