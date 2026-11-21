import ThresholdHC.QuantileFactorUpper.Checker

/-! Kernel certificate for the bisection cover of `[1,31/20]`.

The grid interval `[gridDen,gridTop] = [20*2^24,31*2^24]` is split at its
quarter points `381681664`, `427819008` and `473956352`, and each quarter is
checked by `certify` with fuel `22` by kernel reduction (`decide +kernel`). The
whole tree has 85 accepted cells of depth at most 21. -/
namespace ThresholdHC.QuantileFactorUpper

theorem certify_of_halves {d l m r : ℕ} (hm : (l+r)/2 = m) (h1 : certify d l m = true)
    (h2 : certify d m r = true) : certify (d+1) l r = true := by
  subst hm
  simp [certify, h1, h2]

theorem certify_quarter1 : certify 22 gridDen 381681664 = true := by decide +kernel

theorem certify_quarter2 : certify 22 381681664 427819008 = true := by decide +kernel

theorem certify_quarter3 : certify 22 427819008 473956352 = true := by decide +kernel

theorem certify_quarter4 : certify 22 473956352 gridTop = true := by decide +kernel

theorem certify_full : certify 24 gridDen gridTop = true :=
  certify_of_halves (by decide)
    (certify_of_halves (by decide) certify_quarter1 certify_quarter2)
    (certify_of_halves (by decide) certify_quarter3 certify_quarter4)

end ThresholdHC.QuantileFactorUpper
