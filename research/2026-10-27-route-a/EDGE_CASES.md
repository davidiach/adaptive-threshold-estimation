# Route A edge cases and attempts

Status: elementary deductions from the existing, Lean-checked variational
identity; the formulas below are not a new algorithmic theorem. They were used
to choose and stress-test the research target. Write h=B^(-1/2).

## Atoms and joint limits

For a point mass at d, Psi=min(rho,h sqrt(rho)/d). The saturation boundary is
B=1/(rho d^2), including d=1/2. An estimator that knows only rho can always
output rho/2 at zero work. Thus even a good large-budget argument must allow
this saturation rather than claim a rho/B variance rate at every budget.

For mu=m delta_delta+(1-m)delta_a, 0<delta<a<=1/2 and 0<m<1, put
H=m/delta^2+(1-m)/a^2 and z=m+(1-m)delta^2/a^2.

* If rho<=z, then t=sqrt(rho/H)<=delta and
  Psi=min(rho,h sqrt(rho H)).
* If rho>z, then t=a sqrt((rho-m)/(1-m))>delta. Psi=rho when h>=t;
  Psi=m+(h/a)sqrt((1-m)(rho-m)) when delta<=h<t; and
  Psi=h[m/delta+sqrt((1-m)(rho-m))/a] when h<delta.

The endpoint formulas agree at h=delta and h=t. They follow by inserting the
two atoms into E min(1,t^2/D^2)=rho and the existing three-region identity.
They cover arbitrary joint limits of the small gap, rarity, atom mass, and
budget; none observes an individual magnitude. They show why a fixed positive
minimum gap bound is insufficient for a uniform two-scale theorem. The
continuation's example m=rho,delta=rho^2,a=1/4,h=rho^2 lies in saturation:
Psi=rho. It refutes the old rho-rescaled unrestricted modulus, not Psi.

For a=1/2 the easy component has deterministic flips, but the small-gap component
does not. Replacing the entire population by observed signs would incorrectly
remove that component's statistical difficulty. The new classifier's reference
gaps are at most1/4, so its likelihood logarithms are finite even when the true
coin is deterministic.

## Critical and supercritical powers

For alpha=2 and u=t/a, the exact cutoff equation is
rho=u^2(1+2 log(1/u)). When h<t,

    Psi = [2 h t (1+log(a/t)) - h^2]/a^2.

This is between h rho/t and 2h rho/t. Consequently the critical predicted
unsaturated scale is comparable to
(h/a)sqrt(rho[1+log(1/rho)]), with saturation at rho. These formulas do not
establish an upper algorithm. The new untruncated construction has divergent
inverse-square work at alpha=2; taking alpha down to2 is not a proof of the
critical regime.

For alpha>2, the cutoff equation is
rho=[alpha/(alpha-2)]u^2-[2/(alpha-2)]u^alpha.
The simple two-sided bound

    min(rho,h sqrt(rho)/a) <= Psi
       <= min(rho,h sqrt(rho alpha/(alpha-2))/a)

is enough for the new rate theorem. The lower inequality uses the feasible
constant allocation; the upper uses Cauchy–Schwarz and E D^-2. Both hold jointly
in h,rho,a. Their constants and the new work bound may diverge near alpha=2.

## Prove-or-refute record

1. **Symmetric screening — parked.** High-confidence classification of both
   signs makes all-negative work pay log(1/rho). No proof that this log is
   necessary for all algorithms; it is a failure of this construction.
2. **Ballot survival — parked.** The examined unbiased survival construction
   has positive conditional second moment of order1/D. Concentrating positives
   in the smallest rho mass gives rho^(1-1/alpha), too large for the intended
   rho moment. Again, this is an estimator-family obstruction.
3. **Fixed finite dictionaries — useful diagnostic.** They remove infinite
   scale-search issues, but a minimum-gap or minimum-atom-mass dependent bound
   does not settle the uniform two-atom problem. Existing separated-coin
   literature already covers much of that restricted setting.
4. **Asymmetric screening + random-level correction — selected.** False
   positive error rho epsilon; false negative error epsilon. Only positive
   work pays log(1/rho). The sharp rearrangement bound
   E[q D^-2]<=alpha/(alpha-2) a^-2 rho^(1-2/alpha) absorbs that work for alpha>2.
   In particular E[q D^-2]<=rho E[D^-2] is NOT assumed and is generally false.
5. **Many separated scales — open lead.** For weights roughly proportional
   to d_k^2, each scale can contribute similarly to an inverse-square moment.
   The new detector pays an additional scale-index cost. This suggests a test
   for the arbitrary-law conjecture, but neither a restricted search nor a
   sequential sign-classification obstruction proves an estimation lower
   bound. The missing lemma is a hidden-magnitude estimator attaining the
   clipped inverse-square allocation with a universal cost, or an all-policy
   converse showing that this allocation omits another obstruction.

No route was silently changed into the claim that the arbitrary-law conjecture
has been settled. The chosen complete restriction is alpha>2; alpha=2 and the
uniform two-atom question remain open in this session.
