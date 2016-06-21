A programming language for topology and probability in Coq.

## Building

To build, run `make` at the base level of the project directory.

## Files

### Spec/

The "specification" for the continuous programming language, stated
in terms of categories.

- Category.v : Definition of categories and their properties
  - Cartesian monoidal categories (finite products)
  - Strong monads (e.g., measures and probability distributions)
- Discrete.v : Discrete spaces
  - Every Coq type has an according discrete space, and every Coq function
    is a continuous map between the according discrete spaces
- Sum.v : Sum spaces
  - The empty space, and binary sums (disjoint) unions of spaces
- Lift.v : Lifted spaces
  - Given any space, adjoints a "bottom" element, which can be thought 
    of as indicating non-termination. The bottom element is a generic point.
    Lifted spaces are compact because the new open set for the whole space
    must be in every open cover. This allows interpretation of
    general recursion.
- Sierpinski.v : The Sierpisnski space
  - The Sierpinski space is homeomorphic to the lifting of unit. Perhaps
    I will end up defining it this way, but here it is specified as something
    on its own.
- Stream.v : Infinite streams
- Real.v : Real numbers
  - lower real numbers, non-negative lower-real numbers,
    non-located real numbers (upper and lower Dedekind cuts which may have
    an entire interval as a gap rather than just a point),
    and bona fide real numbers
- Prob.v : Measure and probability spaces
  - Definition of open sets and abstraction from maps to the Sierpinski space
  - Measure, subprobability, and probability monads
  - way-underspecified coinflip distribution and normal distribution
  - probabilistic infinite streams

### FormTopC/

Computationally relevant definitions of formal topology and some
constructions.

### Numbers/
- Qnn.v : Non-negative rational numbers
  - semiring (0, 1, addition, multiplication)
  - truncated subtraction

- LPReal.v : Non-negative lower real numbers encoded as lower Dedekind cuts
  - semiring (0, 1, addition, multiplication)
  - indicators of logical propositions
  - supremum, min, max

## Algebra/
- FrameC.v : Computationally-relevant definitions of preorders, partial orders, semilattices, lattices, and frames
- SetsC.v : Computationally-relevant definitions of subsets and notations
- Sets.v : Computationally-irrelevant definitions of subsets and notations

### Base directory
- Samplers.v : Random samplers
  - Definition of random samplers, proofs and constructions

- Valuation.v (old, and full of lies!)
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

### Types/

Facts about types. In particular, facts about isomorphisms/equivalences of
types, and characterization of finite types.

### FormTop/ (Old)

Definitions of formal topology, but computationally relevant parts
were hidden in Prop.

### Old
- Prob.v, Prob2.v, Prob3.v : these files are old. They were three different
attempts to encode probability in Coq. In Prob.v and Prob2.v, I was hoping
to base everything off of the Cantor space, where everything is naturally
sample-able.
