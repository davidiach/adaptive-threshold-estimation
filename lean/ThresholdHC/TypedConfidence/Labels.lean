import ThresholdHC.TypedConfidence.SignTransfer

noncomputable section
namespace ThresholdHC.TypedConfidence

/-- Every component has a countably infinite supply of persistent labels. -/
def typedLabel {k : ℕ} [NeZero k] (component : Fin k) (coin : ℕ) : ℕ :=
  (Nat.divModEquiv k).symm (coin,component)

def labelType (k : ℕ) [NeZero k] (label : ℕ) : Fin k :=
  (Nat.divModEquiv k label).2

theorem labelType_typedLabel {k : ℕ} [NeZero k] (component : Fin k) (coin : ℕ) :
    labelType k (typedLabel component coin) = component := by
  change ((Nat.divModEquiv k) ((Nat.divModEquiv k).symm (coin,component))).2 = component
  rw [Equiv.apply_symm_apply]

theorem typedLabel_injective {k : ℕ} [NeZero k] :
    Function.Injective (fun z : ℕ × Fin k => typedLabel z.2 z.1) :=
  (Nat.divModEquiv k).symm.injective

/-- Choosing a component and coin index adaptively is exactly a natural-label
policy after encoding. Returning to a pair returns to the same physical coin. -/
theorem typed_policy_word {k : ℕ} [NeZero k]
    (pol : List Bool → Option (ℕ × Fin k)) (n : ℕ) (tapes : ℕ → ℕ → Bool) :
    (CriticalEntropy.populationSimulation
      (fun xs => (pol xs).map (fun z => typedLabel z.2 z.1)) n tapes).2 =
      (CriticalEntropy.populationSimulation pol n
        (fun z => tapes (typedLabel z.2 z.1))).2 :=
  ObservableSimulation.populationSimulation_word_embed
    (fun z : ℕ × Fin k => typedLabel z.2 z.1) typedLabel_injective n pol _ (fun _ _ => rfl) tapes

end ThresholdHC.TypedConfidence
