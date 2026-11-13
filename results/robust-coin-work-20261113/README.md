# The work of the race for a coin with a larger gap than the reference

This record covers the per-coin work bounds needed by the
[robust use of the known-law estimator](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator).
The stopping time of the race is not monotone in the flips: increasing a gap
can remove a wrong early exit. Its three work bounds nevertheless hold at a
reference gap $d_0$ for a coin of every gap $d\ge d_0$.

The race is the one of the
[error transfer](../robust-error-transfer-20261113/README.md): a negative and
a positive bank test on the even flips against the ordinary classifier on the
odd flips, with cap $M=2^L$. Work is the number of flips bought. All
statements are in
[RobustCoinWork.lean](../../lean/ThresholdHC/RobustContinuation/RobustCoinWork.lean).

| Statement | Lean-checked guarantee |
|---|---|
| Ordinary kernel | For every cap $M>0$, $\min\{M,\,17d^{-2}(1+\log_+(Md^2))\}$ does not increase with the gap $d$. |
| Any race | For any two prefix tests, either sign and $d\ge d_0$: the expected work on a coin of gap $d$ is at most $2\min\{M,\,17d_0^{-2}(1+\log_+(Md_0^2))\}$. |
| Negative drift | The drift of a negative reference score increases with the gap of the coin. For a reference matched to $d_0$, $d_0/2\le r\le d_0$, and a negative coin of gap $d\ge d_0$, its crossing time has mean at most $\tfrac34d_0^{-2}(1+b)$ for a threshold $b\ge0$. |
| Negative coin | For the bank with allowance $0<\varepsilon\le1$, a reference gap $d_0$ in band $j$ with weight $0<w_j\le1$, and a negative coin of gap $d\ge d_0$: the expected work is at most $\tfrac32d_0^{-2}\bigl(1+\log\tfrac1{\varepsilon w_j}\bigr)$. |
| Positive survival | For a reference gap $d_0$ in band $j$ and a positive coin of gap $d\ge d_0$, under the conditions of the known-law theorem at $d_0$: the race is still running after $n$ rounds with probability at most $e^{-nd_0^2/2}$. |
| Positive coin | Under the same conditions the expected number of rounds is at most $6U/d_0^2$, and for a design $\sigma+\tau+\zeta$ the expected work is at most $12\,A(d_0)/d_0^2$, where $A(d_0)$ is the positive allowance with the three-piece surcharge at $d_0$. |

Each bound is the one of the known-law theorem
([negative](../../lean/ThresholdHC/EntropyTailUpper/BankRace.lean),
[positive](../../lean/ThresholdHC/EntropyTailUpper/BankWork.lean),
[ordinary](../../lean/ThresholdHC/EntropyTailUpper/Ordinary.lean)) with the
reference gap in place of the gap of the coin. The reasons differ:

- **Ordinary.** The kernel is an explicit function of the gap.
- **Negative coin.** The race stops by the crossing time of the matching
  negative reference, and a Wald bound holds for every coin; only the drift
  depends on the coin, and it grows with the gap.
- **Positive coin.** The race has stopped once the running mean of the bank's
  flips is above $1/2+d_0/2$. A low running mean is a lower set of tapes, so
  it is at most as likely under the coin with the larger gap.

None of them needs the stopping time to be monotone, and none uses a crossing
time that ignores wrong exits.

It does not include:

- **The level work under a coupling**: integrating these bounds over a true
  law coupled above the reference, with the rarity budget of the induced sign
  allocation. The bank's null law here is the design law itself; a reference
  law with mass at zero is not treated in this record.
- The coupling as a construction, the corrections and the plan under the
  true law, the physical-cap median and the connection to the paid stage.
- The robust continuation as a whole, the all-budget controller and the
  arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/85ae1f3fc071284ad14d538139ad6c66602df41c),
the new module was built from source on Linux with Lean `v4.36.0-rc1`, on top
of a build of every project module made in the same environment and against
the Mathlib cache for the pinned revision. It compiled without warnings.
[9 exact statements](robust_coin_work.lean) passed with
[9 transitive axiom reports](robust_coin_work.log), one for each declaration
of the module, using only `propext`, `Classical.choice` and `Quot.sound`. The
whole-project audit `python tools/verify_project_axioms.py --no-build` passed
on the same build: 1,188 modules, 12,605 constants and 10,180 theorems, with no
declared axiom. Its kernel replay was not run locally. The
[native record](status.json) lists the source hash of every project module in
the import closure of the new module. Its base checkpoint is the head of the
[error-transfer change](../robust-error-transfer-20261113/README.md).

Run `python tools/verify_robust_coin_work.py` with the pinned toolchain. The
audit restates every theorem in full and fails if a declaration of the module
is not registered.
