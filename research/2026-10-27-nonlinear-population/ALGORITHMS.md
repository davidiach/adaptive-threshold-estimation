# Algorithms, observations and reproduction

`lower/full_class.tex` specifies the exact two-flip policy and its four rational output values. A head means revisit; a tail means a fresh iid coin. It takes exactly two genuine observations, without a pilot, sampled-gap access or q-dependent calibration. `lower/full_class_certificate.py` verifies its entire feasible parameter triangle using exact Fraction polynomial coefficients. `lower/feedback_certificate.py` preserves three earlier two-profile certificates. The design priors were found by bounded exploratory bisection; optimality of those priors is neither assumed nor required by the exact inequalities.

`feedback_experiment.py` implements the scalable heuristic. Given a finite-prior posterior, each action's predicted head probability is p_a(q); its one-step target-variance reduction is Cov(theta,p_a)^2/[mean(p_a)(1-mean(p_a))]. The policy chooses the maximum, observes one real bit and updates the posterior. Coin counts are sufficient given a hypothesis; adaptive scheduling adds no q-dependent likelihood factor. Duplicate count histories have equal action values. The final posterior mean is nonlinear in the observations. This is a myopic finite-prior rule, not a globally optimal policy or a true-q posterior.

The hidden simulator and policy have separate interfaces. Known mu,rho initialize Model; estimate receives only Model and a bound flip(identity) callback. Reservoir alone uses the actual q,D,S. Coin identities identify persistent tapes. Separate streams for each coin's latent draw and its flips couple corresponding coins across policies. Seeds and all configurations are in EXPERIMENT_LOCK.json. Conditional-bit predictions were checked against 128 exact Fraction calculations and the variance-reduction identity before locking.

The numerical suite uses 64,256,1024 deterministic flips per sampling method. Fresh-only and blocks 4/16 use the same posterior estimator, so the comparison changes acquisition rather than supplied information. Constant zero, half and rarity midpoint spend zero flips. There are no tuning or pilot observations. Deterministic setup and cache costs are described in EXPERIMENT_ACCOUNTING.md; no one-shot wall-time comparison is claimed. Raw outputs, clipped outputs, wall time, work, number of coins and maximum local depth are in RAW.csv. SUMMARY.csv adds all prescribed risk metrics and uncertainty. EXPERIMENT_REPORT.json is the concise analysis.

Reproduction from the repository root:

    python research/2026-10-27-nonlinear-population/lower/feedback_certificate.py
    python research/2026-10-27-nonlinear-population/lower/full_class_certificate.py
    python research/2026-10-27-nonlinear-population/upper/check_exact.py

These scripts write checkpoint outputs; run copies in a new directory when preserving the archived results. Their independent checks are in audit/replay.py and audit/replay_v2.py. Read those scripts' path assumptions before moving them; they locate this research directory relative to themselves.

For a fresh complete heuristic replay, copy feedback_experiment.py, CONTRACT.md and EXPERIMENT_LOCK.json into an empty directory with the same repository-relative layout and NumPy available. Run `feedback_experiment.py run`, preserving the lock instead of recreating it. The script refuses to overwrite RAW.csv. `analyze_experiment.py` processes the raw data without changing the policy. `replay_experiment.py` checks replicate 0 in all 240 cells and refuses to overwrite REPLAY.json. Exact mathematical claims do not depend on the floating experiment.

The finite-convex-program formulation is specified in upper/FINITE_APPROXIMATION.tex. It was proved but not implemented or solved here. Its decision weights keep all feedback choices; expected-work constraints apply separately to each grid allocation. Output variables use a quadratic perspective, avoiding unjustified output discretization. Its size may be prohibitive, so the existence theorem is not a computational-efficiency claim.
