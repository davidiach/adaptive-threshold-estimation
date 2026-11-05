# Sequential testing in the observable experiment

This checkpoint formalizes the dependent-observation testing step of the
[law-dependent time-uniform lower bound](TIME_UNIFORM_LOWER.md). It does not yet
formalize the full asymptotic comparison with the selection functional.

Let Q be one reference probability law and P_k a family of alternatives on
the same experiment. Suppose the corresponding means are θ and θ+a_k, where
a_k>0 and 3a_k≤a_i for every i<k. The estimates at increasing budgets are
measurable functions of their observed prefixes; the prefix at step k can
recover every earlier estimate.

Assume simultaneous error at most t_i with probability at least 1−δ under
Q and every P_k, where 0≤δ≤1/2. If every t_i<a_i/6, set

    E_k = {estimate_k > θ+a_k/2},
    A_k = E_k \ union_{i<k} E_i.

On simultaneous accuracy under Q, no E_k occurs. On simultaneous accuracy
under P_k, the first crossing occurs exactly at k: earlier thresholds are
farther away by the separation assumption. Thus P_k(A_k)≥1−δ, the A_k are
disjoint, and their total Q mass is at most δ.

If the observable prefix KL at step k is at most K_k, binary data processing
and binary entropy bounded by log 2 give

    Q(A_k) ≥ exp(−K_k/(1−δ))/4,
    sum_{k in F} exp(−K_k/(1−δ)) ≤ 4δ

for every finite set F. No conditional KL bound is assumed. Summability
therefore follows. Applying this argument to any tail proves that a divergent
testing schedule forces t_k≥a_k/6 infinitely often.

The final theorem, observed_separated_frequently, instantiates this argument
with the repository's actual experimentLaw and observablePrefixLaw, one
common adaptive policy, and measurable prefix estimates. OnlineAccuracy
quantifies simultaneous accuracy over every admissible rare sign prior.
The schedule is required to be monotone, and the exact theorem still takes
the separated family and its prefix information bounds as premises.

The eight-root audit also checks that exp(−log(k+2)/2) is not summable.
Substituting a concrete prior family and proving its integer-budget
asymptotics are further steps.

Run:

    python tools/verify_anytime_sequential.py

The audit independently restates all eight public statements and checks
their transitive axioms. The native evidence is recorded separately from the
earlier fifteen-root prior-family audit.
