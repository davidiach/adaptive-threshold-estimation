import ThresholdHC.Tier5.Entropy
import ThresholdHC.Tier4.StoppedReconstruction

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

def prefixSigma (Seed : Type) [MeasurableSpace Seed] (n : ℕ) :
    MeasurableSpace (Seed × ProcessTape) :=
  MeasurableSpace.comap (fun z : Seed × ProcessTape => (z.1, processPrefix n z.2)) inferInstance

theorem prefixSigma_mono (Seed : Type) [MeasurableSpace Seed] :
    Monotone (prefixSigma Seed) := by
  intro n N hnN
  let trunc : Seed × Prefix N → Seed × Prefix n :=
    fun z => (z.1, fun i => z.2 (Fin.castLE hnN i))
  have hm : Measurable trunc := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (Fin.castLE hnN i)).comp measurable_snd
  have hN : @Measurable (Seed × ProcessTape) (Seed × Prefix N)
      (prefixSigma Seed N) _ (fun z => (z.1, processPrefix N z.2)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact (hm.comp hN).comap_le

theorem prefixSigma_iSup (Seed : Type) [MeasurableSpace Seed] :
    (⨆ n, prefixSigma Seed n) = (inferInstance : MeasurableSpace (Seed × ProcessTape)) := by
  apply le_antisymm
  · exact iSup_le fun n => (measurable_jointPrefix (Seed := Seed) n).comap_le
  · have hn (n : ℕ) : @Measurable (Seed × ProcessTape) (Seed × Prefix n)
        (⨆ n, prefixSigma Seed n) _ (fun z => (z.1, processPrefix n z.2)) :=
      measurable_iff_comap_le.mpr (le_iSup (prefixSigma Seed) n)
    have hseed : @Measurable (Seed × ProcessTape) Seed
        (⨆ n, prefixSigma Seed n) _ Prod.fst := (hn 0).fst
    have htape : @Measurable (Seed × ProcessTape) ProcessTape
        (⨆ n, prefixSigma Seed n) _ Prod.snd := by
      apply @Measurable.of_eval (Seed × ProcessTape) ℕ (fun _ => Option Bool)
        (⨆ n, prefixSigma Seed n)
      intro k
      exact (measurable_pi_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1))).comp
        (hn (k+1)).snd
    have hid : @Measurable (Seed × ProcessTape) (Seed × ProcessTape)
        (⨆ n, prefixSigma Seed n) _ id := hseed.prodMk htape
    simpa only [MeasurableSpace.comap_id] using hid.comap_le

theorem joint_tape_kl_eq_iSup_prefix_of_ac (Seed : Type) [MeasurableSpace Seed]
    (P Q : Measure (Seed × ProcessTape)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hac : P ≪ Q) :
    klDiv P Q = ⨆ n, klDiv
      (P.map (fun z => (z.1, processPrefix n z.2)))
      (Q.map (fun z => (z.1, processPrefix n z.2))) :=
  klDiv_eq_iSup_map_of_generates P Q _ measurable_jointPrefix
    (prefixSigma_mono Seed) (prefixSigma_iSup Seed) hac

end ThresholdHC.Tier5
