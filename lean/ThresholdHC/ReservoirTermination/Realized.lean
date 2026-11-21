import ThresholdHC.ReservoirTermination.WalkLaw
import ThresholdHC.Tier3.StoppingBase

/-!
From the finite-prefix laws to the realized experiment. Under any measure whose
prefix expectations are the creation-model sums of the walk policy, the expected
total work is the supremum of the finite expected work, and the probability of
never stopping is the limit of the alive mass, because the events alive up to time
`n` decrease to `RunsForever` and, on the support, an early stop persists.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.ReservoirTermination
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Proofs

/-- Every event of a finite prefix is measurable. -/
theorem measurableSet_prefix_mem {Ω : Type} [MeasurableSpace Ω] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ) (S : Set (Prefix n)) :
    MeasurableSet {ω | processPrefix n (tape ω) ∈ S} := by
  have h : {ω | processPrefix n (tape ω) ∈ S} =
      ⋃ w ∈ S, ⋂ i : Fin n, {ω | tape ω i = w i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, fun i => rfl⟩
    · rintro ⟨w, hw, hi⟩
      have hpw : processPrefix n (tape ω) = w := funext hi
      rwa [hpw]
  rw [h]
  exact MeasurableSet.biUnion (Set.to_countable S)
    (fun w _ => MeasurableSet.iInter (fun i => htape i (w i)))

/-- A realization with a constant environment computes every finite-prefix
expectation by the creation-model sum. -/
theorem realized_prefix_sum {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure μ]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (d q : ℝ)
    (hr : RealizesCreationPrefixes μ ν seed tape (fun _ => walkPolicy)
      (fun _ _ => d) (fun _ _ => q)) (n : ℕ) (F : Prefix n → ℝ) :
    (∫ ω, F (processPrefix n (tape ω)) ∂ν) =
      ∑ w, creationLaw walkPolicy (fun _ => d) (fun _ => q) w * F w := by
  have hC : ∀ w, |F w| ≤ ∑ v, |F v| := fun w =>
    Finset.single_le_sum (f := fun v => |F v|) (fun v _ => abs_nonneg _) (Finset.mem_univ w)
  have h := hr n (fun _ w => F w) (fun _ => measurable_const) ⟨_, fun _ w => hC w⟩
  rw [h, integral_const]
  simp

theorem iSup_ofReal_of_tendsto {f : ℕ → ℝ} (hf : Monotone f) {a : ℝ}
    (ha : Tendsto f atTop (𝓝 a)) : (⨆ n, ENNReal.ofReal (f n)) = ENNReal.ofReal a := by
  have hm : Monotone (fun n => ENNReal.ofReal (f n)) :=
    fun i j hij => ENNReal.ofReal_le_ofReal (hf hij)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hm) (ENNReal.tendsto_ofReal ha)

section Realized

variable {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (tape : Ω → ProcessTape) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
  (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1)
  (hfin : ∀ (n : ℕ) (F : Prefix n → ℝ), (∫ ω, F (processPrefix n (tape ω)) ∂ν) =
    ∑ w, creationLaw walkPolicy (fun _ => d) (fun _ => q) w * F w)
include htape hd hq hfin

theorem realized_work :
    (∫⁻ ω, totalProcessWork (tape ω) ∂ν) =
      ⨆ n : ℕ, ENNReal.ofReal (walkExp (1/2+(2*q-1)*d) n (fun xs => (xs.length : ℝ))) := by
  rw [integral_total_work_eq_iSup ν tape htape]
  congr 1
  funext n
  rw [hfin n workOf]
  simp_rw [workOf_eq_length]
  rw [walk_sum_eq d q hd hq n (fun xs => (xs.length : ℝ))]

theorem realized_alive (n : ℕ) :
    ν {ω | ∀ k : Fin (n+1), walkPolicy (processHistory (tape ω) k) ≠ none} =
      ENNReal.ofReal (walkExp (1/2+(2*q-1)*d) n walkAlive) := by
  classical
  let S : Set (Prefix n) := {w | ∀ k : Fin (n+1), walkPolicy (finiteHistory w k) ≠ none}
  have hset : {ω | ∀ k : Fin (n+1), walkPolicy (processHistory (tape ω) k) ≠ none} =
      {ω | processPrefix n (tape ω) ∈ S} := rfl
  have hmeas := measurableSet_prefix_mem tape htape n S
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  congr 1
  have h1 := hfin n (S.indicator (fun _ => 1))
  have h2 : (fun ω => S.indicator (fun _ => (1:ℝ)) (processPrefix n (tape ω))) =
      {ω | processPrefix n (tape ω) ∈ S}.indicator (fun _ => 1) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [h2, integral_indicator_const _ hmeas, smul_eq_mul, mul_one] at h1
  rw [h1, ← walk_sum_eq d q hd hq n walkAlive]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hz : creationLaw walkPolicy (fun _ => d) (fun _ => q) w = 0
  · simp [hz]
  · congr 1
    unfold walkAlive
    by_cases hv : walkValue (fullHist w) = 1
    · have hw : w ∉ S := fun hw => hw (Fin.last n) (by
        rw [finiteHistory_last]
        simp [walkPolicy, hv])
      simp [Set.indicator_of_notMem hw, hv]
    · have hw : w ∈ S := fun k hk => by
        have := walk_absorb d q hd hq n w hz k hk
        simp [walkPolicy, hv] at this
      simp [Set.indicator_of_mem hw, hv]

theorem realized_runsForever {a : ℝ}
    (ha : Tendsto (fun n => walkExp (1/2+(2*q-1)*d) n walkAlive) atTop (𝓝 a)) :
    ν (RunsForever tape) = ENNReal.ofReal a := by
  let D : ℕ → Set Ω := fun n =>
    {ω | ∀ k : Fin (n+1), walkPolicy (processHistory (tape ω) k) ≠ none}
  have hD : RunsForever tape = ⋂ n, D n := by
    ext ω
    simp only [RunsForever, D, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h n k
      exact h k
    · intro h n
      exact h n (Fin.last n)
  have hanti : Antitone D := by
    apply antitone_nat_of_succ_le
    intro n ω hω k
    exact hω k.castSucc
  have hmeas (n : ℕ) : MeasurableSet (D n) := measurableSet_prefix_mem tape htape n
    {w | ∀ k : Fin (n+1), walkPolicy (finiteHistory w k) ≠ none}
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hmeas n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hD]
  apply tendsto_nhds_unique hlim
  have heq : (ν ∘ D) = fun n => ENNReal.ofReal (walkExp (1/2+(2*q-1)*d) n walkAlive) := by
    funext n
    exact realized_alive ν tape htape d q hd hq hfin n
  rw [heq]
  exact ENNReal.tendsto_ofReal ha

end Realized

/-- The general first-passage law on a realized experiment, from the finite-prefix
sums. -/
theorem walk_first_passage_of_sums {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (d η : ℝ)
    (hd0 : 0 < d) (hd1 : d ≤ 1/2) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ((∀ (n : ℕ) (F : Prefix n → ℝ), (∫ ω, F (processPrefix n (tape ω)) ∂ν) =
        ∑ w, creationLaw walkPolicy (fun _ => d) (fun _ => 1/2 + η) w * F w) →
      ν (RunsForever tape) = 0 ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ENNReal.ofReal (1 / (4 * d * η))) ∧
    ((∀ (n : ℕ) (F : Prefix n → ℝ), (∫ ω, F (processPrefix n (tape ω)) ∂ν) =
        ∑ w, creationLaw walkPolicy (fun _ => d) (fun _ => 1/2 - η) w * F w) →
      ν (RunsForever tape) = ENNReal.ofReal (8 * d * η / (1 + 4 * d * η)) ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ∞) := by
  have hd : 0 ≤ d ∧ d ≤ 1/2 := ⟨hd0.le, hd1⟩
  have hdη : 0 < d * η := mul_pos hd0 hη0
  have hdη1 : d * η < 1/4 := by nlinarith
  set r := 1/2 + 2*d*η with hr
  have hr12 : 1/2 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hplus : 1/2+(2*(1/2+η)-1)*d = r := by rw [hr]; ring
  have hminus : 1/2+(2*(1/2-η)-1)*d = 1 - r := by rw [hr]; ring
  constructor
  · intro hfin
    have hq : 0 ≤ 1/2 + η ∧ 1/2 + η ≤ 1 := ⟨by linarith, by linarith⟩
    have hlim := walk_plus_limits r hr12 hr1.le
    rw [← hplus] at hlim
    constructor
    · rw [realized_runsForever ν tape htape d _ hd hq hfin hlim.2, ENNReal.ofReal_zero]
    · rw [realized_work ν tape htape d _ hd hq hfin]
      rw [iSup_ofReal_of_tendsto (walkExp_length_mono _ (by rw [hplus]; linarith)
        (by rw [hplus]; linarith)) hlim.1, hplus]
      congr 1
      rw [hr]
      ring
  · intro hfin
    have hq : 0 ≤ 1/2 - η ∧ 1/2 - η ≤ 1 := ⟨by linarith, by linarith⟩
    have hlim := walk_minus_limits r hr12 hr1
    constructor
    · rw [realized_runsForever ν tape htape d _ hd hq hfin (a := 1 - (1-r)/r)
        (by rw [hminus]; exact hlim.1)]
      congr 1
      rw [hr]
      field_simp
      ring
    · rw [realized_work ν tape htape d _ hd hq hfin, hminus]
      rw [iSup_eq_top]
      intro b hb
      have hρ : 0 < 1 - (1-r)/r := by
        rw [sub_pos, div_lt_one (by linarith)]
        linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (b.toReal / (1 - (1-r)/r))
      refine ⟨n, ?_⟩
      rw [← ENNReal.ofReal_toReal hb.ne, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      have h1 := hlim.2 n
      rw [div_lt_iff₀ hρ] at hn
      linarith

end ThresholdHC.ReservoirTermination
