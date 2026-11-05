import ThresholdHC.OptimalQuantile.Continuity

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

def scalarPeak (k : ℝ) : ℝ := sSup (partitionSeries k '' Set.Icc 1 (31/20))

theorem partitionSeries_clamped_continuous :
    Continuous (fun z : ℝ × ℝ => partitionSeries (max (sqrt 2) z.1) (max 1 z.2)) := by
  have hc : Continuous (fun z : ℝ × ℝ => (max (sqrt 2) z.1,max 1 z.2)) :=
    (continuous_const.max continuous_fst).prodMk (continuous_const.max continuous_snd)
  have hm : ∀ z : ℝ × ℝ, (max (sqrt 2) z.1,max 1 z.2) ∈ scalarDomain :=
    fun z => ⟨le_max_left (sqrt (2 : ℝ)) z.1,le_max_left (1 : ℝ) z.2⟩
  simpa only [Function.comp_def] using partitionSeries_continuousOn.comp_continuous hc hm

theorem scalarPeak_continuousOn : ContinuousOn scalarPeak (Set.Ici (sqrt 2)) := by
  have hc : Continuous (fun k : ℝ => sSup
      ((fun u : ℝ => partitionSeries (max (sqrt 2) k) (max 1 u)) '' Set.Icc 1 (31/20))) :=
    isCompact_Icc.continuous_sSup partitionSeries_clamped_continuous
  have he (k : ℝ) : (fun u : ℝ => partitionSeries (max (sqrt 2) k) (max 1 u)) ''
      Set.Icc 1 (31/20) = partitionSeries (max (sqrt 2) k) '' Set.Icc 1 (31/20) := by
    apply Set.image_congr
    intro u hu
    rw [max_eq_right hu.1]
  simp_rw [he] at hc
  apply hc.continuousOn.congr
  intro k hk
  change scalarPeak k = scalarPeak (max (sqrt 2) k)
  rw [max_eq_right hk]

theorem scalarPeak_attained {k : ℝ} (hk : sqrt 2 ≤ k) :
    ∃ u ∈ Set.Icc (1 : ℝ) (31/20), scalarPeak k = partitionSeries k u ∧
      ∀ v ∈ Set.Icc (1 : ℝ) (31/20), partitionSeries k v ≤ partitionSeries k u := by
  exact isCompact_Icc.exists_sSup_image_eq_and_ge (by
    exact ⟨1,by norm_num⟩) ((partitionSeries_continuousOn_tangent hk).mono
      (fun _ h => h.1))

theorem partitionSeries_le_peak {k u : ℝ} (hk : sqrt 2 ≤ k)
    (hu : u ∈ Set.Icc (1 : ℝ) (31/20)) : partitionSeries k u ≤ scalarPeak k := by
  obtain ⟨v,hv,he,hm⟩ := scalarPeak_attained hk
  rw [he]
  exact hm u hu

theorem scalarPeak_strictAntiOn : StrictAntiOn scalarPeak (Set.Ici (sqrt 2)) := by
  intro k hk l hl hkl
  obtain ⟨u,hu,he,_⟩ := scalarPeak_attained hl
  rw [he]
  exact (partitionSeries_strict_in_factor hk hkl hu.1).trans_le (partitionSeries_le_peak hk hu)

theorem all_tangents_iff_peak {k : ℝ} (hk : sqrt 2 ≤ k) (hkcap : k ≤ 31/20) :
    (∀ u : ℝ, 1 ≤ u → partitionSeries k u ≤ 1) ↔ scalarPeak k ≤ 1 := by
  constructor
  · intro h
    obtain ⟨u,hu,he,_⟩ := scalarPeak_attained hk
    rw [he]
    exact h u hu.1
  · intro h u hu
    by_cases hucap : u ≤ 31/20
    · exact (partitionSeries_le_peak hk ⟨hu,hucap⟩).trans h
    · have hcapu : (31/20 : ℝ) ≤ u := (lt_of_not_ge hucap).le
      exact (partitionSeries_mono_above_factor hk hkcap hcapu).trans
        ((partitionSeries_le_peak hk (by norm_num)).trans h)

theorem all_finite_bounds_iff_peak {k : ℝ} (hk : sqrt 2 ≤ k) (hkcap : k ≤ 31/20) :
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarPeak k ≤ 1 :=
  (all_finite_bounds_iff_series hk).trans (all_tangents_iff_peak hk hkcap)

end ThresholdHC.OptimalQuantile
