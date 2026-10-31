import ThresholdHC.Genie.Model
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.StoppingProgram.PrefixInformation

/-! Latent-reveal rewards dominate ordinary prefix information and are
harmonic down the observation tree, including extended values. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.CapIdentification

theorem measurable_prefixLikelihood (s : Bool) (n k : ℕ) :
    Measurable (prefixLikelihood s n k) := by
  cases s
  · change Measurable (fun d : Gap => (1/2-(d:ℝ))^k*(1/2+(d:ℝ))^(n-k))
    fun_prop
  · change Measurable (fun d : Gap => (1/2+(d:ℝ))^k*(1/2-(d:ℝ))^(n-k))
    fun_prop

theorem measurable_revealIntegrand (Q : FourPriors) (n k : ℕ) :
    Measurable (fun d : Gap =>
      ENNReal.ofReal (prefixLikelihood true n k d)*perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
      ENNReal.ofReal (prefixLikelihood false n k d)*perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d)) := by
  have hd := Q.high.property.1.sub Q.low.property.1
  exact ((ENNReal.measurable_ofReal.comp (measurable_prefixLikelihood true n k)).mul
    (measurable_perspective _ _ hd Q.variance.property.1)).add
    ((ENNReal.measurable_ofReal.comp (measurable_prefixLikelihood false n k)).mul
      (measurable_perspective _ _ hd (measurable_const.sub Q.variance.property.1)))

theorem revealReward_root (μ : Measure Gap) (Q : FourPriors) :
    revealReward μ Q 0 0 = latentDivergence μ Q := by
  simp [revealReward,latentDivergence,prefixLikelihood]

theorem revealReward_children (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) (hk : k ≤ n) :
    revealReward μ Q (n+1) k+revealReward μ Q (n+1) (k+1) = revealReward μ Q n k := by
  unfold revealReward
  rw [←lintegral_add_left (measurable_revealIntegrand Q (n+1) k)]
  apply lintegral_congr
  intro d
  calc
    _ = (ENNReal.ofReal (prefixLikelihood true (n+1) k d)+
        ENNReal.ofReal (prefixLikelihood true (n+1) (k+1) d))*
          perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
      (ENNReal.ofReal (prefixLikelihood false (n+1) k d)+
        ENNReal.ofReal (prefixLikelihood false (n+1) (k+1) d))*
          perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d) := by ring
    _ = _ := by
      rw [←ENNReal.ofReal_add (prefixLikelihood_nonneg true _ _ d) (prefixLikelihood_nonneg true _ _ d),
        ←ENNReal.ofReal_add (prefixLikelihood_nonneg false _ _ d) (prefixLikelihood_nonneg false _ _ d),
        prefixLikelihood_add true n k hk d,prefixLikelihood_add false n k hk d]

theorem revealReward_le_latentDivergence (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) :
    revealReward μ Q n k ≤ latentDivergence μ Q := by
  apply lintegral_mono
  intro d
  apply add_le_add
  · exact (mul_le_mul_left (show ENNReal.ofReal (prefixLikelihood true n k d) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal (prefixLikelihood_le_one true n k d)) _).trans_eq (one_mul _)
  · exact (mul_le_mul_left (show ENNReal.ofReal (prefixLikelihood false n k d) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal (prefixLikelihood_le_one false n k d)) _).trans_eq (one_mul _)

def prefixDensity (q : SignLaw) (n k : ℕ) (d : Gap) : ℝ :=
  q.val d*prefixLikelihood true n k d+(1-q.val d)*prefixLikelihood false n k d

theorem prefixDensity_integrable (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (n k : ℕ) : Integrable (prefixDensity q n k) μ := by
  convert (integrable_weighted_prefix μ q true n k).add
    ((integrable_prefixLikelihood μ false n k).sub (integrable_weighted_prefix μ q false n k)) using 1
  ext d
  simp only [prefixDensity,Pi.add_apply,Pi.sub_apply]
  ring

theorem prefixDensity_nonneg (q : SignLaw) (n k : ℕ) (d : Gap) :
    0 ≤ prefixDensity q n k d :=
  add_nonneg (mul_nonneg (q.property.2 d).1 (prefixLikelihood_nonneg _ _ _ _))
    (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (prefixLikelihood_nonneg _ _ _ _))

theorem perspective_neg_left (x y : ℝ) : perspective (-x) y = perspective x y := by
  simp [perspective]

theorem prefixDensity_information_le (Q : FourPriors) (n k : ℕ) (d : Gap) :
    perspective (prefixDensity Q.high n k d-prefixDensity Q.low n k d)
      (prefixDensity Q.variance n k d) ≤
      ENNReal.ofReal (prefixLikelihood true n k d)*perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
      ENNReal.ofReal (prefixLikelihood false n k d)*perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d) := by
  have he : prefixDensity Q.high n k d-prefixDensity Q.low n k d =
      prefixLikelihood true n k d*(Q.high.val d-Q.low.val d)+
      prefixLikelihood false n k d*(-(Q.high.val d-Q.low.val d)) := by unfold prefixDensity; ring
  rw [he,prefixDensity,mul_comm (Q.variance.val d),mul_comm (1-Q.variance.val d)]
  have h := perspective_add_le
    (x := prefixLikelihood true n k d*(Q.high.val d-Q.low.val d))
    (z := prefixLikelihood false n k d*(-(Q.high.val d-Q.low.val d)))
    (mul_nonneg (prefixLikelihood_nonneg true n k d) (Q.variance.property.2 d).1)
    (mul_nonneg (prefixLikelihood_nonneg false n k d) (sub_nonneg.mpr (Q.variance.property.2 d).2))
  rwa [perspective_scale _ _ (prefixLikelihood_nonneg true n k d),
    perspective_scale _ _ (prefixLikelihood_nonneg false n k d),perspective_neg_left] at h

theorem prefixInformation_le_revealReward (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (n k : ℕ) : prefixInformation μ Q n k ≤ revealReward μ Q n k := by
  have h := perspective_integral_le μ
    (fun d => prefixDensity Q.high n k d-prefixDensity Q.low n k d) (prefixDensity Q.variance n k)
    ((prefixDensity_integrable μ Q.high n k).sub (prefixDensity_integrable μ Q.low n k))
    (prefixDensity_integrable μ Q.variance n k) (prefixDensity_nonneg Q.variance n k)
  rw [integral_sub (prefixDensity_integrable μ Q.high n k) (prefixDensity_integrable μ Q.low n k)] at h
  exact h.trans (lintegral_mono (prefixDensity_information_le Q n k))

end ThresholdHC.Genie
