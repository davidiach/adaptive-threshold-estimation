# Relevance of the supplied ETH preprint

**Status: reading-level relevance assessment, not verification of the paper.**

The user supplied OpenAI's [The Exponential Time Hypothesis is False, revised
October 25, 2026](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf).
The introduction and technique overview were inspected. Its full proof was not
audited here, and no result in this repository depends on its claimed theorem.

The preprint proposes exact counting for fixed-width SAT using algebraic
replacement forms, interpolation, and shared linear measurements that allow
smaller groups to be summed separately. The possible transferable idea is to
reduce interactions between parts of a large discrete search or exact evaluator.

Our evaluator already combines exponentially many binary histories into states
consisting of success counts and stopping decisions. It does not enumerate all
binary tapes. There is currently no demonstrated further reduction using the
preprint's construction, nor an implementation or timing improvement claimed.

A future search over finite stopping-policy tables could investigate a SAT or
integer-programming encoding, with explicit control of encoding size. That is
a proposal, not an immediate consequence of the preprint. The present search
uses just two real threshold parameters and runs quickly with the existing
recursion.

The project's lower bounds count observations and already allow unrestricted
uncharged computation. They do not assume ETH. A faster discrete computation
would therefore not invalidate those statistical lower bounds. The remaining
Lean targets concern real analysis and probability; this paper does not supply
a direct replacement proof for them.
