# Focused source audit and a pilot-design obligation

Baseline inspected: HEAD `d75c775633df545b892e69fc876930d6d2dcc329`. The complete additive extension in `research/2026-10-27-critical-two/construction.tex` was read at SHA-256 `8e72d93569fdd917675fda976475f9ddb9762e1e7c79d6fe43e9a269a01bf44a`. Concurrent `nonlinear-critical/review.md` and `sources.md` were read as research context, not accepted proof dependencies. No old source, result, or lock was edited.

## Primary Lee--Valiant comparison

[Lee--Valiant, arXiv:1904.09228v3](https://arxiv.org/pdf/1904.09228v3), Section 7, printed pp.33--37, Lemmas 22--23, Theorems 4--5, and Appendix C's coefficient calculation were inspected. Their estimator requires known positive and negative conditional bias distributions, a design mixture proportion, and a per-coin depth cap. A quadratic program determines terminal coefficients; reciprocal variance is a linear objective for optimizing the stopping flow. Calibration remains unbiased if the scalar mixture proportion changes while the conditional distributions stay fixed. The comparison with fully adaptive algorithms is constant-confidence, uses the same cap, and compares nearby scalar mixture proportions. Section 7 discusses bootstrapping but performs its analysis with exact conditional distributions. **OVERLAPPING:** optimizing acquisition and terminal scores jointly is a concrete promising principle. **DIFFERENT MODEL / UNRESOLVED:** learning those conditional laws uniformly in the present hidden-q class, paying the pilot cost, and controlling misspecification have not been supplied by that theorem. It does not justify plugging an estimated q into the oracle solution and inheriting the optimum.

## A model-specific calibration identity

The following is a direct calculation for the current model, not a claim imported from Lee--Valiant. Condition on a pilot transcript H and the resulting single-coin production policy and output Y_H. Let

`m_H,s(d)=E[Y_H | D=d,S=s,H]`, `g_H(d)=m_H,+(d)-m_H,-(d)`.

Assume integrability before subtracting means. The production expectation under q is

`b_H(q)=integral m_H,- dmu + integral q g_H dmu`.

If the selected output is calibrated at a fitted allocation qhat_H, meaning `b_H(qhat_H)=theta(qhat_H)`, then its exact conditional bias under the true allocation is

`b_H(q)-theta(q)=integral (q-qhat_H)(g_H-1) dmu`.

Knowing only theta approximately does not control this expression. Ordinary L1 or total-variation error is sufficient only with a proved bound on the response residual `g_H-1`; large terminal coefficients can amplify a seemingly small pilot error. Calibration against two fitted sign-conditional distributions is not pointwise calibration against every hidden magnitude.

For n independent fresh production coins conditional on H, the raw arithmetic mean has conditional MSE

`Var_q(Y_H | H)/n + [b_H(q)-theta(q)]^2`.

Pilot randomness must be averaged after this conditional identity. The squared bias does not disappear merely because the pilot and production data are independent. If the production sample count or policy depends on H, their actual conditional costs must be integrated as well.

## A concrete feasible route, with its unresolved step

A pilot can build a confidence set C_H of allocations using observable finite-word frequencies and their affine likelihood constraints. Select a production acquisition/output rule by optimizing a worst-case variance bound over C_H while enforcing

`sup_{q in C_H} |integral(q-qhat_H)(g_H-1)dmu| <= beta_H`.

This is local robust calibration, not true-q access. On the event q belongs to C_H, independent production has MSE at most its proved conditional variance term plus beta_H squared. After clipping, the complementary event contributes at most `rho^2 P(q notin C_H)`. All pilot and production observations are charged. This specifies a real proof obligation for a feedback construction; no claim that the confidence set contracts cheaply enough, or that this optimization attains Psi, is made here.

In particular, a shallow pilot cannot distinguish arbitrary profiles merely by taking more fresh coins. The independent upper agent's degree-four perturbation gives exactly identical local word probabilities through depth four while changing theta. Its checked identity is recorded in `REVIEW.md`. Deeper production information is necessary to separate that pair; a shallow pilot followed by deeper production is not excluded. The obstruction concerns the information actually gathered, not the quality of a fitted optimizer.

## Concurrent Juditsky--Nemirovski work

[Juditsky--Nemirovski (2009)](https://www2.isye.gatech.edu/~nemirovs/AnnStat_Saddle_2009.pdf), Section 2.1, Theorems 3.1--3.2, Lemmas 3.1--3.2 and Proposition 3.1 were freshly inspected. Their explicit theorem concerns confidence risk for finite-dimensional good observation schemes. Its exponential-moment proof also controls the scale parameter via the diagonal objective. This is a promising route to an RMS comparison for fixed acquisition. A separate concurrent task is developing the needed transcript approximation and finite-product/Poisson extension. That work is not adopted as complete here, and this agent does not duplicate its proof. General feedback and common random design do not automatically inherit the good-scheme assumption.
