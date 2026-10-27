# Track C: direct-real randomized threshold estimator

**Numerical evidence — REJECT.** Tuned GHA has lower held-out RMSE at both
requested budgets. The new estimator was selected using tuning data only, sealed
in public commit `6eec012`, then tested once with 500 repetitions per cell. No
post-test tuning was performed.

| Budget | Method | RMSE (descriptive 95% interval) | Mean work (descriptive 95% interval) |
|---:|---|---:|---:|
| 16,384 | Tuned GHA | 0.02990 (0.02778–0.03204) | 15,893 (15,619–16,167) |
| 16,384 | Direct-real | 0.03910 (0.03260–0.04563) | 15,329 (14,467–16,205) |
| 65,536 | Tuned GHA | 0.02012 (0.01862–0.02159) | 66,847 (65,667–68,031) |
| 65,536 | Direct-real | 0.02185 (0.01838–0.02581) | 64,658 (62,853–66,586) |

These are measured-work comparisons, not equal hard work caps. All final outputs
are clipped to [0,1]. Direct-real raw RMSE is 0.04310 and 0.02316, respectively;
clipping affected 6.4% and 7.2% of runs. Constant zero has RMSE **0.025**, beating
both methods' point estimates at the smaller budget. At the larger budget the
methods' intervals overlap; the point-estimate ordering does not establish a
statistically resolved separation. Bootstrap intervals use 3,000 resamples and
are descriptive, not certified heavy-tail coverage.

## Algorithm and selection

The classifier checks real sample means at dyadic checkpoints, with minimum
early-stop size 16 and boundary
`threshold * sqrt(sample_variance * (1 + log(cap/n)) / n)`.
This boundary is an experimental rule for unbounded observations, not a proved
confidence sequence. It receives no true target, latent mean, or latent sign.

The final choice at both budgets uses caps 1,024 and 4,096, threshold 1, and a
randomized telescoping sum. The level probabilities are approximately 0.738796
and 0.261204. A sampled upper level determines which coupled classifiers run;
increments are weighted by level inclusion probability. At budget 16,384 the
method uses one two-success calibration and its fresh production sample. At
65,536 it averages four independent copies before clipping. Both therefore
exercise a nontrivial multilevel correction. The original tuned GHA allocations
are single-level plans (39 samples at level 4, or 78 at level 5), as in the supplied
harness; this limitation is retained explicitly.

Four tuning-only design rounds examined prefix single-term coupling, antithetic
coarse blocks, randomized sums, and four-repeat randomized sums. All 342 cells
used 100 tuning repetitions. Selection minimizes clipped tuning RMSE separately
for each budget. Winning tuning RMSE values 0.02538 and 0.01661 did not carry over
to held-out performance. Selection over many noisy cells can be optimistic; no
post-hoc parameter revision is made from the held-out errors.

## Offline cost and reproduction

New method training consumed **128,413,344** original inner draws, and its full
tuning search consumed **1,413,243,264**, for **1,541,656,608** offline draws.
The selected fixed geometric law needs no fitted moments, but the search cost
is still charged and reported. GHA reuses **166,827,744** training draws and
**34,093,824** GHA-only tuning draws. The original package's all-method tuning
cost is 139,244,642. These are amortized production comparisons, not equal-total-
training-cost comparisons. Arithmetic and auxiliary randomization are uncharged,
matching the original harness.

`benchmark/README.md` gives commands and seed formulas. The original observation
generator, GHA allocation/training and its tuning results are copied unchanged.
GHA test seeds are 41201 and 41301; new-method seeds are 41204 and 41304. The
selection file records source hashes and the environment. The once-only test
marker links back to that selection hash. Original held-out results were not
consulted before selection. Raw new outcomes are in `results/real_test_raw.npz`;
cell summaries and descriptive intervals are in `results/real_test.json`.

Implementation verification passed 71,049 finite-tape checks, 1,000 exact
telescoping checks, and 10 checks equating a four-repeat production call to four
separate calls with the same random stream. Independent scalar classifiers check
stopping decisions and charged work. These tests do not prove statistical rates.

## Calibration identities — proved on paper

Fix the trained or selected parameters, independently of production observations.
Let an iid randomized term be `(Y,C)` with `0 < C <= M`, finite second moment,
mean cost `c`, and mean `m`. A pilot succeeds when an independent uniform is below
`C/M`, so its iid success probability is `p=c/M`. Let `K` be the number of pilots
through the second success. Use `K-1` fresh iid production terms and average their
values. Their mean is `m`, because the production sample is independent of `K`.
The negative-binomial identity `E[1/(K-1)]=p` gives raw variance `Var(Y)*c/M`.
Wald's identity gives expected pilot work `E[K]c=2M`; independent production costs
give `(E[K]-1)c=2M-c`. Total expected work is exactly **4M-c <= 4M**. Averaging
four independent copies divides raw variance by four and multiplies expected
work by four. These statements concern expectation, not a per-run work bound.

For the randomized sum, write `Q_l=P(J>=l)` and define
`Y=Z_0 + sum_{1<=l<=J}(Z_l-Z_(l-1))/Q_l` using a common observation stream.
The level draw is independent of that stream and every `Q_l` is positive.
Finite linearity gives `E[Y]=E[Z_L]`. The calibration wrapper therefore preserves
the expectation of the final capped classifier before clipping. This expectation
need not equal the true threshold probability. No new universal error theorem or
unbiasedness claim for the clipped output is asserted. These algebraic arguments
were not formalized in Lean in this track.
