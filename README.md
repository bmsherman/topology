An exploration of how to formalize probability in Coq.

## Files

Qnn.v : Non-negative rational numbers

LPReal.v : Non-negative lower real numbers encoded as lower Dedekind cuts

Valuation.v : definition of measures (valuations), integrals, and probability.
Product measures, Dirac measures, Bernoulli, Binomial, "submeasures",
partial valuations, Sampling, PDFs.

Prob.v, Prob2.v, Prob3.v : these files are old. They were three different
attempts to encode probability in Coq. In Prob.v and Prob2.v, I was hoping
to base everything off of the Cantor space, where everything is naturally
sample-able.
