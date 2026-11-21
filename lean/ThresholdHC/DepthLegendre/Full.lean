import ThresholdHC.DepthLegendre.Floor

/-! The part-2 targets of the bounded-depth obstruction, proved: `lem:poly` and
the explicit odd-Legendre pair of `thm:cap` in
`research/2026-10-27-nonlinear-population/upper/proof-body.tex`, with the
self-contained floor `ρ/(2(K+1)(2K+1))` for every procedure obeying the per-coin
cap `2K`. Components: `legendre_ode`, `legendre_eval_one` and
`abs_depthSlope_ge_one` (Rodrigues), and `quadratic_cut_integral` (QuadraticLaw). -/

noncomputable section
namespace ThresholdHC.DepthLegendre

/-- `lem:poly`: `u_K` is an even polynomial of degree `2K`, bounded by one on `[0,1]`,
orthogonal to `x^(2j+2)` for `j < K`, with `∫₀¹ 2x u_K = 1/((K+1)(2K+1))`. -/
theorem depth_polynomial : DepthPolynomialStatement :=
  depthPolynomialFacts

/-- `thm:cap`, the explicit pair for the exact quadratic law: admissible, rare,
targets `ρ/2 (1 ± m_K)`, separation `ρ/((K+1)(2K+1))`, and equal word probabilities
through depth `2K`; the separation is at most the cap-`2K` diameter (Lean-only). -/
theorem depth_pair : DepthPairStatement :=
  depthPair

/-- `thm:cap`, self-contained: equal seed-and-transcript laws under per-coin cap `2K`
and worst RMS at least `ρ/(2(K+1)(2K+1))`, whatever the work. -/
theorem depth_cap_floor : DepthCapFloorStatement :=
  depthCapFloor

end ThresholdHC.DepthLegendre
