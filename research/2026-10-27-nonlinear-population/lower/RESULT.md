# Exact acquisition-feedback separation

## Full global-rarity class: strengthened result

**PROVED-ON-PAPER with exact rational verification.** For
`mu=(delta_(1/4)+delta_(1/8))/2`, `rho=1/4`, and the **entire** class
`Q_rho`, an explicit feedback estimator using exactly two genuine flips
has worst-case MSE below `0.015443`. Every noninteractive procedure in
the stated comparison class has minimax MSE above `0.015475`, even with
local stopping, shared independent seeds and arbitrary nonlinear terminal
postprocessing. Thus the strict minimax MSE advantage exceeds `0.000032`.

This remains a **deterministic total cap of two**, not an expected-budget-two
comparison. The noninteractive policies are preselected and cannot use
cross-coin observations or outcome-dependent cancellation to allocate flips.
The feedback policy chooses a fresh coin after a first tail and revisits
after a first head. Its fixed four-entry rational output table is given in
[full_class.tex](full_class.tex).

The global worst-case bound is certified over the whole rarity triangle,
not a grid: write `A=E[Dq(D)]` and `theta=Eq`. The feasible `(A,theta)`
region is a triangle. Risk is convex in `theta` for fixed `A`, and the
three edge risks have strictly positive second derivatives, verified from
their exact rational polynomial coefficients. Its maximum is therefore at
one of the three vertices. A two-endpoint Bayes lower bound then applies
to every noninteractive design and every nonlinear terminal estimator.

Reproduce the full-class certificate:

```text
python research/2026-10-27-nonlinear-population/lower/full_class_certificate.py
```

The command passed and produced
[full_class_certificate.json](full_class_certificate.json), including all
polynomial coefficients, edge curvature certificates, vertex risks, output
table, and exact strict minimax gap. No floating-point optimization or
Monte Carlo evidence is used for the accepted inequalities.

This establishes a genuine full-class finite minimax benefit from acquisition
feedback. It does not establish an asymptotically growing benefit or resolve
the expected-work rare-event minimax law.

## Earlier two-profile certificate, preserved

Status: **PROVED-ON-PAPER with certified rational arithmetic** for a finite
two-hypothesis, deterministic-cap experiment. No Lean or novelty claim.

The actual hidden iid reservoir model has a strict minimax advantage from
feedback across coin identities, even after allowing arbitrary nonlinear
terminal estimation in the noninteractive comparison class.

Take `rho=1/4`, `mu=(delta_(1/4)+delta_(1/8))/2`, and the two admissible
profiles `q0=0`, `q1=1/4`. Under a deterministic total cap of two flips,
every preselected collection of local coin policies without cross-coin
feedback is dominated by a random mixture of two fixed schedules: two
flips of one coin, or one flip each of two fresh coins. This includes local
stopping, independent local seeds, a shared preselected seed, and arbitrary
nonlinear terminal estimation. An external monitor that cancels one local
policy based on another's observations is feedback and is excluded.

The adaptive policy uses a fresh coin after the first tail and revisits the
same coin after the first head. An explicitly pinned rational posterior-mean
estimator has maximum conditional MSE below `0.015246`; every noninteractive
procedure in the comparison class has minimax MSE above `0.015313`.
All inequalities are certified exactly, not inferred from decimal output.

The full argument, comparison class, policy tables, likelihood and posterior
formulas are in [feedback.tex](feedback.tex). The proof uses no external
theorem beyond elementary conditional expectation and finite Bayes risk.

Reproduction:

```text
python research/2026-10-27-nonlinear-population/lower/feedback_certificate.py
```

The output is [feedback_certificate.json](feedback_certificate.json), with
exact probabilities, posterior outputs, conditional losses, and strict
rational gaps. Three cases have magnitude ratios 2, 16 and 256. The dyadic
priors were selected in an exploratory command by 30 rational bisection
steps and then fixed in the certificate; correctness does not depend on
the search finding an optimum. No sampling, random seed or floating-point
optimization is used in the certification.

**Limits:** this is not an expected-budget-two comparison. Noninteractive
procedures allowed occasional work above two are outside the comparison
class. The parameter class here contains two specified profiles, not all
of `Q_rho`. The result is a strict finite minimax separation, not a rate
separation or a resolution of the arbitrary-law population conjecture.

The failed amplification route is explicit: a constant two-flip advantage
does not accumulate automatically into a growing critical-law advantage.
One needs a multiscale family with simultaneous uniform budget control and
a lower bound against the entire competing design class. The existing
single-coin/additive obstruction and the fixed-product nonlinear theorem
do not supply that missing statement for observation-dependent acquisition.

The additional paper proof [local_information.tex](local_information.tex)
explains this feedback effect for **every** magnitude law supported on
`(0,1/4]`, on the constant-sign-probability submodel. At `q=0`, the
conditional Fisher information from revisiting after a head exceeds that
of a fresh bit, which exceeds that of revisiting after a tail. For the
exact critical law the two-flip information is `97/66` with feedback,
versus `576/473` for revisiting and `1` for two fresh coins. This is a
finite local-information theorem, not an unrestricted minimax bound.
The accompanying equal-prior small-rarity expansion shows why the finite
Bayes gain is only of order `rho^4` against leading risk `rho^2`; it does
not prove the growing advantage needed to remove the critical logarithm.

Verification performed in this pass:

- Ran the certificate command above: `PASS: 3 exact rational
  minimax-separation certificates`.
- Ran a separate exact `Fraction` check of all six displayed critical-law
  information constants: passed.
- The separate `audit_singlecoin` agent independently replayed the three
  certificates and reviewed the noninteractive dominance proof, general
  information formulas, and Bayes expansion; it found no blocking defect.
  Its replay and pinned hashes are in the sibling audit directory. This is
  agent review, not external peer review.

The files in this directory were written without changing the inherited
single-coin, additive, radial, fixed-product, or formal baselines. No local
commit or push was performed by this subtask.
