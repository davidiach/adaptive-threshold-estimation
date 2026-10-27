import ThresholdHC.Tier3.StoppingBase
import ThresholdHC.Tier3.Randomized

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Tier3

local instance optionMeasurableSpaceTesting (α : Type) : MeasurableSpace (Option α) := ⊤

theorem acceptedBy_processPrefix_iff {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (n : ℕ) (u : Seed) (x : ProcessTape) :
    acceptedBy pol decision n u (processPrefix n x) ↔
      ∃ k ≤ n, pol u (processHistory x k) = none ∧ decision u (processHistory x k) = true := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Nat.le_of_lt_succ k.isLt, hk⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, h⟩

theorem measurableSet_acceptedBy {Seed : Type} [MeasurableSpace Seed] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (hp : MeasurablePolicy pol) (hdc : ∀ xs, Measurable (fun u => decision u xs))
    (n : ℕ) (w : Fin n → Option Bool) : MeasurableSet {u | acceptedBy pol decision n u w} := by
  simp only [acceptedBy, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (hp (finiteHistory w k) none).inter
    (measurableSet_eq_fun (hdc (finiteHistory w k)) measurable_const)

def prefixAcceptanceSet {Seed Ω : Type} {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (n : ℕ) : Set Ω :=
  {ω | acceptedBy pol decision n (seed ω) (processPrefix n (tape ω))}

theorem measurableSet_prefixAcceptance {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    {m : ℕ} (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (hs : Measurable seed) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol) (hdc : ∀ xs, Measurable (fun u => decision u xs))
    (n : ℕ) : MeasurableSet (prefixAcceptanceSet seed tape pol decision n) := by
  classical
  have hm := measurable_prefix_function seed tape hs htape n
    (fun u w => if acceptedBy pol decision n u w then (true:Bool) else false)
    (fun w => measurable_const.ite (measurableSet_acceptedBy pol decision hp hdc n w) measurable_const)
  simpa [prefixAcceptanceSet] using measurableSet_eq_fun hm (measurable_const : Measurable (fun _ : Ω => true))

theorem prefixAcceptance_mono {Seed Ω : Type} {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool) :
    Monotone (prefixAcceptanceSet seed tape pol decision) := by
  intro n N hn ω hω
  obtain ⟨k,hkn,hk⟩ := (acceptedBy_processPrefix_iff pol decision n (seed ω) (tape ω)).mp hω
  exact (acceptedBy_processPrefix_iff pol decision N (seed ω) (tape ω)).mpr ⟨k,hkn.trans hn,hk⟩

theorem terminalAccept_eq_iUnion {Seed Ω : Type} {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool) :
    terminalAccept seed tape pol decision = ⋃ n, prefixAcceptanceSet seed tape pol decision n := by
  ext ω
  constructor
  · rintro ⟨n,hn⟩
    exact Set.mem_iUnion.mpr ⟨n,(acceptedBy_processPrefix_iff pol decision n (seed ω) (tape ω)).mpr ⟨n,le_rfl,hn⟩⟩
  · intro hω
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
    obtain ⟨k,hkn,hk⟩ := (acceptedBy_processPrefix_iff pol decision n (seed ω) (tape ω)).mp hn
    exact ⟨k,hk⟩

theorem prefixAcceptance_subset_terminal {Seed Ω : Type} {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool) (n : ℕ) :
    prefixAcceptanceSet seed tape pol decision n ⊆ terminalAccept seed tape pol decision := by
  rw [terminalAccept_eq_iUnion]
  exact Set.subset_iUnion _ n

theorem prefixAcceptance_tendsto {Seed Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool) :
    Tendsto (fun n => ν.real (prefixAcceptanceSet seed tape pol decision n)) atTop
      (𝓝 (ν.real (terminalAccept seed tape pol decision))) := by
  rw [terminalAccept_eq_iUnion]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_measure_iUnion_atTop (prefixAcceptance_mono seed tape pol decision))

def terminalFiniteTest {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (n : ℕ) (u : Seed) : Finset (Prefix n) := by
  classical
  exact Finset.univ.filter (acceptedBy pol decision n u)

theorem terminalFiniteTest_measurable {Seed : Type} [MeasurableSpace Seed] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (hp : MeasurablePolicy pol) (hdc : ∀ xs, Measurable (fun u => decision u xs)) (n : ℕ) :
    MeasurableTest (terminalFiniteTest pol decision n) := by
  intro w
  simpa [terminalFiniteTest] using measurableSet_acceptedBy pol decision hp hdc n w

theorem realized_prefix_acceptance {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsFiniteMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (pol : Seed → List Bool → Option (Fin m))
    (decision : Seed → List Bool → Bool) (d q : Fin m → ℝ)
    (hs : Measurable seed) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol) (hdc : ∀ xs, Measurable (fun u => decision u xs))
    (hr : RealizesPrefixes μ ν seed tape pol d q) (n : ℕ) :
    ν.real (prefixAcceptanceSet seed tape pol decision n) =
      randomizedAcceptance μ pol d q (terminalFiniteTest pol decision n) := by
  classical
  let f : Seed → Prefix n → ℝ := fun u w => if acceptedBy pol decision n u w then 1 else 0
  have hf : ∀ w, Measurable (fun u => f u w) := fun w =>
    measurable_const.ite (measurableSet_acceptedBy pol decision hp hdc n w) measurable_const
  have hb : ∃ C : ℝ, ∀ u w, |f u w| ≤ C := by
    refine ⟨1, fun u w => ?_⟩
    dsimp [f]
    split_ifs <;> norm_num
  have heq := hr n f hf hb
  have heql : (fun ω => f (seed ω) (processPrefix n (tape ω))) =
      (prefixAcceptanceSet seed tape pol decision n).indicator (fun _ => (1:ℝ)) := rfl
  rw [heql, integral_indicator_const 1 (measurableSet_prefixAcceptance seed tape pol decision hs htape hp hdc n)] at heq
  simpa [randomizedAcceptance, terminalFiniteTest, f, Finset.sum_filter, mul_ite] using heq

theorem continuousAt_testing_kl (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ContinuousAt (fun x : ℝ => klB (1-x) x) δ := by
  have h1 : 0 < 1-δ := sub_pos.mpr hδ1
  have heq : (fun x : ℝ => klB (1-x) x) =
      fun x => (1-x)*Real.log ((1-x)/x) + x*Real.log (x/(1-x)) := by
    funext x
    simp only [klB, sub_sub_cancel]
  rw [heq]
  fun_prop (disch := positivity)

theorem unbounded_testing : UnboundedTestingStatement := by
  intro Seed Ω _ _ μ P Q _ _ _ m seed tape pol decision d η h δ hs htape hp hdc hrP hrQ hh hd hη hdη hδ hδhalf hfin hPA hQA
  let E := (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal
  let a := P.real (terminalAccept seed tape pol decision)
  let an := fun n => P.real (prefixAcceptanceSet seed tape pol decision n)
  let δn := fun n => δ+a-an n
  have han (n : ℕ) : an n ≤ a :=
    measureReal_mono (prefixAcceptance_subset_terminal seed tape pol decision n)
  have hδn (n : ℕ) : 0 < δn n := by dsimp [δn]; linarith [han n]
  have hδle (n : ℕ) : δ ≤ δn n := by dsimp [δn]; linarith [han n]
  have hconv : Tendsto δn atTop (𝓝 δ) := by
    have hc := (tendsto_const_nhds (x := δ+a)).sub
      (prefixAcceptance_tendsto P seed tape pol decision)
    simpa [δn, a] using hc
  have hsmall : ∀ᶠ n in atTop, δn n < 1/2 := (tendsto_order.1 hconv).2 _ hδhalf
  have hb : ∀ᶠ n in atTop, klB (1-δn n) (δn n) ≤ (128/225)*h^2*E := by
    filter_upwards [hsmall] with n hn
    have haN : 1-δn n ≤ randomizedAcceptance μ pol d (fun i => 1/2+η i)
        (terminalFiniteTest pol decision n) := by
      rw [← realized_prefix_acceptance μ P seed tape pol decision d _ hs htape hp hdc hrP]
      dsimp [δn, an, a] at *
      linarith
    have hbN : randomizedAcceptance μ pol d (fun i => 1/2-η i)
        (terminalFiniteTest pol decision n) ≤ δn n := by
      rw [← realized_prefix_acceptance μ Q seed tape pol decision d _ hs htape hp hdc hrQ]
      exact (measureReal_mono (prefixAcceptance_subset_terminal seed tape pol decision n)).trans
        (hQA.trans (hδle n))
    have ht := randomized_testing_bound Seed μ m n pol d η h (δn n)
      (terminalFiniteTest pol decision n) hp (terminalFiniteTest_measurable pol decision hp hdc n)
      hh hd hη hdη (hδn n) hn haN hbN
    apply ht.trans
    rw [← realized_prefix_work_eq μ P seed tape pol d _ hrP]
    exact mul_le_mul_of_nonneg_left (prefix_work_le_total P tape htape hfin n) (by positivity)
  exact le_of_tendsto ((continuousAt_testing_kl δ hδ (by linarith)).tendsto.comp hconv) hb

end ThresholdHC.Tier3
