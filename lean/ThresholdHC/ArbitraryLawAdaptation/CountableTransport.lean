import ThresholdHC.ArbitraryLawAdaptation.CountableEntropy

/-! The factor-three transport inequality for countably many source bands and
displacements. Only individual destination columns must be summable; the
total cost and entropy may both be infinite. -/

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTailQuantile

def partialTransport (b : ℕ × ℕ → ℝ) (dest : ℕ × ℕ → ℕ) (n j : ℕ) : ℝ :=
  ∑ x : Fin n × Fin n, if dest (x.1.val,x.2.val) = j then b (x.1.val,x.2.val) else 0

theorem partialTransport_nonneg {b : ℕ × ℕ → ℝ} (hb : ∀ x, 0 ≤ b x)
    (dest : ℕ × ℕ → ℕ) (n j : ℕ) : 0 ≤ partialTransport b dest n j := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hb _
  · exact le_rfl

theorem partialTransport_entropy_le {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2 * f x)
    (dest : ℕ × ℕ → ℕ) (n m : ℕ) :
    costEntropy (fun j : Fin m => partialTransport b dest n j.val) ≤
      3*costEntropy (fun i : Fin n => a i.val) := by
  have hmerge := costEntropy_finite_destination_prefix
    (fun x : Fin n × Fin n => hb (x.1.val,x.2.val))
    (fun x : Fin n × Fin n => dest (x.1.val,x.2.val)) m
  apply hmerge.trans
  exact finite_band_transport_three (fun i : Fin n => ha i.val)
    (fun x : Fin n × Fin n => hf (x.1.val,x.2.val))
    (fun x : Fin n × Fin n => hb (x.1.val,x.2.val))
    (fun i : Fin n => hrow i.val n) (fun x : Fin n × Fin n => hcost (x.1.val,x.2.val))

theorem partialTransport_countableEntropy_le {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2 * f x)
    (dest : ℕ × ℕ → ℕ) (n : ℕ) :
    countableEntropy (partialTransport b dest n) ≤ 3*countableEntropy a := by
  apply iSup_le
  intro m
  calc
    _ ≤ ENNReal.ofReal (3*costEntropy (fun i : Fin n => a i.val)) :=
      ENNReal.ofReal_le_ofReal (partialTransport_entropy_le ha hf hb hrow hcost dest n m)
    _ = 3*ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    _ ≤ 3*countableEntropy a := by
      gcongr
      exact prefix_le_countableEntropy a n

theorem partialTransport_tendsto {b : ℕ × ℕ → ℝ} (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0)) (j : ℕ) :
    Tendsto (fun n => partialTransport b dest n j) atTop
      (𝓝 (∑' x, if dest x = j then b x else 0)) :=
  summable_tendsto_square (hcol j)

/-- Countable band transport with extended-valued entropy. The local column
condition does not require a finite total inverse-square moment. -/
theorem countable_band_transport_three {a : ℕ → ℝ} {f b : ℕ × ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤ a i)
    (hcost : ∀ x, b x ≤ bandContraction x.2 * f x)
    (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0)) :
    countableEntropy (fun j => ∑' x, if dest x = j then b x else 0) ≤
      3*countableEntropy a :=
  countableEntropy_limit_le (partialTransport_tendsto dest hcol)
    (partialTransport_countableEntropy_le ha hf hb hrow hcost dest)

end ThresholdHC.ArbitraryLawAdaptation
