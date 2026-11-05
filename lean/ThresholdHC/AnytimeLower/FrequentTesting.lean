import ThresholdHC.AnytimeLower.SeparatedTesting
import Mathlib.Analysis.PSeries

noncomputable section
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower

theorem separated_accuracy_frequently {Ω : Type} [MeasurableSpace Ω]
    {X : ℕ → Type} [∀ k, MeasurableSpace (X k)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (P : ℕ → Measure Ω) [∀ k, IsProbabilityMeasure (P k)]
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k))
    (obs : ∀ k, Ω → X k) (hobs : ∀ k, Measurable (obs k))
    (readback : ∀ k, ℕ → X k → ℝ) (hr : ∀ k i, Measurable (readback k i))
    (hread : ∀ k i, i ≤ k → ∀ x, readback k i (obs k x) = z i x)
    (θ : ℝ) (a t : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hsep : ∀ i k, i < k → 3*a k ≤ a i)
    {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (hbase : 1-δ ≤ Q.real {x | ∀ i, |z i x-θ| ≤ t i})
    (halt : ∀ k, 1-δ ≤ (P k).real {x | ∀ i, |z i x-(θ+a k)| ≤ t i})
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hkl : ∀ k, klDiv ((P k).map (obs k)) (Q.map (obs k)) ≤ ENNReal.ofReal (K k))
    (hdiv : ¬Summable (fun k => exp (-K k/(1-δ)))) :
    ∃ᶠ k in atTop, a k/6 ≤ t k := by
  by_contra hh
  simp only [not_frequently,not_le] at hh
  obtain ⟨m,hm⟩ := eventually_atTop.mp hh
  have hbase' : 1-δ ≤ Q.real {x | ∀ i, |z (i+m) x-θ| ≤ t (i+m)} :=
    hbase.trans (measureReal_mono (fun _ hx i => hx (i+m)))
  have halt' (k : ℕ) : 1-δ ≤ (P (k+m)).real
      {x | ∀ i, |z (i+m) x-(θ+a (k+m))| ≤ t (i+m)} :=
    (halt (k+m)).trans (measureReal_mono (fun _ hx i => hx (i+m)))
  have hs := separated_accuracy_summable Q (fun k => P (k+m))
    (fun i => z (i+m)) (fun i => hz (i+m))
    (fun k => obs (k+m)) (fun k => hobs (k+m))
    (fun k i => readback (k+m) (i+m)) (fun k i => hr (k+m) (i+m))
    (fun k i hi x => hread (k+m) (i+m) (Nat.add_le_add_right hi m) x)
    θ (fun i => a (i+m)) (fun i => t (i+m)) (fun i => ha (i+m))
    (fun i k hi => hsep (i+m) (k+m) (Nat.add_lt_add_right hi m))
    (fun i => hm (i+m) (Nat.le_add_left m i)) hd hbase' halt'
    (fun k => K (k+m)) (fun k => hK (k+m)) (fun k => hkl (k+m))
  exact hdiv ((summable_nat_add_iff m).mp hs)

theorem not_summable_half_log :
    ¬Summable (fun k : ℕ => exp (-log ((k:ℝ)+2)/2)) := by
  intro h
  have hh : Summable (fun k : ℕ => 1/((k:ℝ)+2)) := by
    apply h.of_nonneg_of_le (fun k => by positivity)
    intro k
    have hx : 0 < (k:ℝ)+2 := by positivity
    have hl : 0 ≤ log ((k:ℝ)+2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    calc
      1/((k:ℝ)+2) = exp (-log ((k:ℝ)+2)) := by rw [exp_neg,exp_log hx,one_div]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hh' : Summable (fun k : ℕ => 1/((k+2:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh
  exact not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hh')

end ThresholdHC.AnytimeLower
