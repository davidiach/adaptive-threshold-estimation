# A fully polynomial approximation scheme for finite-law entropy-tail selection

6 November 2026. Baseline: `68adbf3`. Status: **full scheme: paper proof and
executable prototype; no independent review.** The entropy perturbation lemma
and certified-bin state-compression invariant are now
[Lean-checked components](../../lean/ThresholdHC/SelectionApproximation/README.md).
The full approximation guarantee, bit complexity, concrete bin-index function
and Python execution are not Lean-checked.

## Result

Let `mu` be a finite probability law with positive rational masses and rational
gaps in `(0,1/2]`. Let `0 < rho <= 1/4`, `B > 0`, and `0 < epsilon <= 1` be
rational. There is an algorithm, polynomial in the binary input length and
`1/epsilon`, returning a bandwise upper-gap suffix selection `s` such that

\[
 K_{\mu,\rho}(B)\le J(s)\le (1+\epsilon)K_{\mu,\rho}(B).
\]

Here `J` is the **capped** deterministic entropy-tail objective. No bound on
the number of occupied bands or distinct positive menu costs is assumed.
The algorithm also produces rational endpoints `l,u` with

\[
 l\le K\le J(s)\le u\le(1+\epsilon)l.
\]

The unrestricted exact polynomial-time problem remains open. The result
concerns known finite laws and their rate functional, not a new estimator,
confidence interval, or statistical minimax theorem.

The prerequisite is the existing finite-law suffix theorem, including its
connection to **all fractional submeasures**, not merely hard subsets. See
[`GapLawMenus/Full.lean`](../../lean/ThresholdHC/GapLawMenus/Full.lean),
especially `finite_law_solver`, and
[`BAND_COST_SELECTION.md`](../../docs/BAND_COST_SELECTION.md).

## 1. Finite menus and the obstacle

In each of `m` occupied dyadic bands, enumerate the empty choice and every
upper-gap suffix. A choice has inverse-square cost
`a = sum_selected w_i/d_i^2` and saves ordinary cost
`sum_selected w_i min(1,1/(d_i sqrt(B)))`.
For a trace choosing one option in each band, write

\[
 A=\sum_j a_j,\quad
 G(a)=A+\sum_{j:a_j>0}a_j\log(A/a_j),\quad
 T=\sum_{i\text{ omitted}}w_i\min(1,1/(d_i\sqrt B)),
\]
\[
 J(a)=\min\{\rho,T+\sqrt{\rho G(a)/B}\}.
\]

Set `G(0)=0`. In particular `G(a)>=A` and `T>=0`.
The existing theorem says that `K` equals the minimum over these traces.
Grouping exact cost multisets can remain exponential. We instead approximate
two additive coordinates and keep the ordinary cost exact.

It is unsafe to infer a relative entropy bound merely by approximating two
large terms and subtracting them. The following normalization explicitly
controls that cancellation.

## 2. Rational additive coordinates

Let `r` be the smallest positive cost in any menu and let
`U=sum_j max_menu_j a`. Both are positive rational numbers. Put

\[
 R=U/r\ge1,\qquad L=4+\lceil\log_2 R\rceil,
 \qquad \delta=\epsilon/8,
 \qquad M=\lceil16mL/\epsilon\rceil.
\]

For every positive menu cost `a`, compute a rational `u(a)` such that

\[
 \log(a/r)\le u(a)\le\log(a/r)+\delta.
\]

This is possible using binary range reduction and the positive atanh series.
For example, enclose the logarithm to width `epsilon/16`, then round the upper
endpoint upward to a multiple of `1/ceil(16/epsilon)`. The sum of the two
errors is at most `epsilon/8`.

For a trace define additive rational coordinates

\[
 A=\sum_j a_j,\qquad \widetilde H=\sum_{j:a_j>0}a_j(1+u(a_j)).
\]

If `H=sum a_j(1+log(a_j/r))`, then

\[
 0\le\widetilde H-H\le\delta A,\quad
 A\le\widetilde H\le LA,\quad
 G(a)=f(A)-H,\quad f(A)=A(2+\log(A/r)).                 \tag{1}
\]

Every nonempty partial trace has `r<=A<=U` and `r<=Htilde<=LU`.
On `[r,U]`, `0<f'(A)=3+log(A/r)<=L`.

## 3. Trimming invariant

Partition positive values `x>=r` by dyadic intervals
`[r*2^k,r*2^(k+1))`, each split into `M` equal subintervals.
The ratio of the upper to lower endpoint of every bin is at most `1+1/M`.
Zero has its own bin. Bin indices use only rational arithmetic.

Starting with the empty trace, process one menu at a time. Extend every
retained trace by every option, group by the pair of bins for `(A,Htilde)`,
and retain **one actual trace with the smallest ordinary tail cost** per group.
Equivalently, maximize saved ordinary cost. At a fixed stage, all traces
have the same total available ordinary cost, so the two comparisons agree.

**Invariant.** For every original trace `x` of length `j`, a retained trace
`y` has no larger tail cost and satisfies, for each positive coordinate,

\[
 (1+1/M)^{-j}\le A_y/A_x\le(1+1/M)^j,
 \quad
 (1+1/M)^{-j}\le\widetilde H_y/\widetilde H_x\le(1+1/M)^j.       \tag{2}
\]

The empty trace remains exactly empty. To prove (2), induct on `j`.
Adding the same nonnegative menu contribution preserves a two-sided
multiplicative comparison. Replacing an extension by a representative in
the same bin costs at most one additional factor `1+1/M`. The representative
saves at least as much ordinary cost; a common extension preserves this
ordering. These facts prove the induction, including zero coordinates.

At the final stage set `kappa=(1+1/M)^m` and `eta=kappa-1`.
Since `m/M<=epsilon/(16L)<=1/64` and `exp(x)<=1+2x` on `[0,1/2]`,

\[
 \eta\le\epsilon/(8L),\qquad\kappa\le2.                    \tag{3}
\]

## 4. The central entropy perturbation lemma

Let `x` be a nonempty trace and `y` its retained representative from (2).
Write `E_z=Htilde_z-H_z`, so `0<=E_z<=delta A_z`. Then

\[
\begin{aligned}
 G(y)-G(x)
 &=f(A_y)-f(A_x)-(\widetilde H_y-\widetilde H_x)+E_y-E_x\\
 &\le L\eta A_x+\eta\widetilde H_x+\delta A_y\\
 &\le(2L\eta+\delta\kappa)A_x\\
 &\le(\epsilon/2)A_x\le(\epsilon/2)G(x).
\end{aligned}                                                     \tag{4}
\]

The first bound uses the mean value theorem on `[r,U]` and both sides of
(2). The penultimate bound follows from (3) and `delta=epsilon/8`.
This is the step that makes the approximation valid despite cancellation.

Because `T_y<=T_x`, square roots and clipping preserve the conclusion

\[
 J(y)\le\sqrt{1+\epsilon/2}\,J(x)
       \le(1+\epsilon/4)J(x).                               \tag{5}
\]

For a nonempty trace this follows by applying the factor to each nonnegative
term and then using `min(rho,c z)<=c min(rho,z)` for `c>=1`.
For the empty trace the comparison is exact. Apply (5) to an optimal trace.
If `V` is the minimum over retained traces and `beta=1+epsilon/4`, then

\[
 K\le V\le\beta K.                                        \tag{6}
\]

## 5. Endpoint selection and bit complexity

Enclose every retained trace's **original** objective by rational intervals
`[l_s,u_s]`, without replacing its entropy by the surrogate. Let
`l_*=min_s l_s`, `u_*=min_s u_s`, and retain a witness attaining `u_*`.
Refine precision until `u_*<=beta l_*`. Equation (6) gives

\[
 l_*/\beta\le K\le J(\text{witness})\le u_*,\qquad
 u_*\le\beta^2(l_*/\beta)\le(1+\epsilon)(l_*/\beta),
\]

where `(1+epsilon/4)^2<=1+epsilon` for `0<epsilon<=1`.
This proves both stated guarantees; exact equality testing of transcendental
values is unnecessary.

There are at most

\[
 S=1+M^2(1+\lfloor\log_2R\rfloor)
              (1+\lfloor\log_2(LR)\rfloor)
\]

retained states per stage. If `Q` is the total number of menu options,
there are at most `Q*S` extensions. Here `Q=n+m` for `n` atoms.
The logarithm of `R`, `L`, and all rational bit lengths are polynomial in
the binary input length. Dyadic binning avoids representing gigantic powers
of `1+1/M`. A common rational denominator for the rounded `u(a)` keeps the
additive surrogate bit lengths polynomial as well.

Saved ordinary costs have the form `x+y/sqrt(B)` with rational coefficients.
Their ordering is exact: after resolving signs, compare `B*x^2` with `y^2`.
No algebraic-number oracle is required.

Final refinement terminates with polynomial precision. Every nonempty trace
has uncapped objective at least `sqrt(rho*r/B)`, while the empty trace has
ordinary cost at least `min(1,2/sqrt(B))`. Hence all clipped objectives exceed
the positive bound

\[
 \min\{\rho,\sqrt{\rho r/B},1,2/\sqrt B\}.
\]

Its logarithmic inverse is polynomial in input length. The finitely many
logarithms and square roots can therefore be enclosed tightly enough using
polynomially many bits and rational arithmetic. This proves the stated
fully polynomial approximation scheme, not just an arithmetic-operation bound.

## 6. Implementation and boundaries

[`approximate_selection.py`](../../toolkit/threshold_toolkit/approximate_selection.py)
implements this construction using the existing rational interval primitives.
It returns a feasible selection, a global enclosure conditional on this paper
proof, and state/transition counts. It never labels its selection exactly
optimal. The prototype retains the toolkit's finite precision limits and a
user-controlled transition cap; exceeding either raises an error rather than
returning a partial certificate. The mathematical algorithm allows these
resources to grow as above. Polynomial worst-case complexity does not promise
small practical constants on highly disparate laws.

## 7. Prior art and review boundary

State trimming and approximate Pareto sets are established techniques.
Woeginger's [2000 paper](https://pubsonline.informs.org/doi/10.1287/ijoc.12.1.57.11901)
gives general conditions for obtaining fully polynomial schemes from dynamic
programs. Papadimitriou and Yannakakis's
[2000 paper](https://citeseerx.ist.psu.edu/document?doi=e841026102d180fd00ffa906b953fd49a29f9744&repid=rep1&type=pdf)
studies polynomial approximate trade-off sets. We inspected the former's
publisher abstract and the latter's accessible extended abstract. We do not
claim a new general approximation paradigm or a comprehensive novelty search.

The project-specific argument here is the normalized, rational surrogate
and perturbation bound (4), allowing trimming despite subtraction in `G`,
together with the existing fractional-selection reduction. The proof and
implementation were produced and self-reviewed in one agent session.
Numerical cross-checks do not establish the universal theorem. There is no
Lean verification of the full scheme, independent agent review, or external
specialist review. The separately audited entropy and compression components
have the narrower formal scope linked at the start of this note.
