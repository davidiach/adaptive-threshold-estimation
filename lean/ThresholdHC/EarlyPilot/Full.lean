import ThresholdHC.EarlyPilot.Easy

/-! The early-stopping pilot. The existence theorem exhibits the estimator
`earlyEstimator`, which runs the `J m` probes one after another and starts the
next probe as soon as one stops; the other four theorems hold for every family
that meets `IsEarlyPilot`, and the existence theorem makes them non-vacuous. -/

noncomputable section
namespace ThresholdHC.EarlyPilot

theorem early_pilot_exists : EarlyPilotExistsStatement :=
  fun J m _ hρ _ => ⟨earlyEstimator J m _, earlyEstimator_isEarlyPilot J m hρ⟩

theorem early_pilot_event : EarlyPilotEventStatement := early_pilot_event_holds

theorem early_pilot_work : EarlyPilotWorkStatement := early_pilot_work_holds

theorem easy_law_work : EasyLawWorkStatement := easy_law_work_holds

theorem easy_law_vanishing : EasyLawVanishingStatement := easy_law_vanishing_holds

end ThresholdHC.EarlyPilot
