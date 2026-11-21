import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Proofs.Tier2.InformationCore

/-!
Per-seed queried-coin KL bound for two constant sign priors.

For an adaptive finite transcript with revealed magnitudes, the KL divergence
between the transcript laws under the constant priors `theta'` and `theta` is a
sum over coins. Coin `i` contributes nothing on transcripts that never query
it; on the others its contribution is bounded by the two-point log-sum
inequality. The visit masses of coin `i` agree under the two extreme priors,
so coin `i` costs at most its visit mass times the binary KL. The visit masses
sum to at most the horizon `n`.
-/

noncomputable section
namespace ThresholdHC.BernoulliTimeUniform
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier5 Real

/-- The Bernoulli KL divergence is at most the chi-square divergence. -/
theorem klB_le_chisq (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) : klB p q ≤ (p-q)^2 / (q*(1-q)) := by
  have h1 := mul_le_mul_of_nonneg_left
    (log_le_sub_one_of_pos (div_pos hp hq)) hp.le
  have h2 := mul_le_mul_of_nonneg_left
    (log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1-p)
      (by linarith : 0 < 1-q))) (by linarith : 0 ≤ 1-p)
  have he : p*(p/q-1) + (1-p)*((1-p)/(1-q)-1) = (p-q)^2/(q*(1-q)) := by
    have hq' : q ≠ 0 := hq.ne'
    have hq1' : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
    field_simp
    ring
  unfold klB
  linarith

/-- The two-point log-sum inequality for one coin mixed under two priors. -/
theorem two_point_log_sum {θ θ' a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (hθ' : 0 < θ' ∧ θ' < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (θ'*a+(1-θ')*b)*log ((θ'*a+(1-θ')*b)/(θ*a+(1-θ)*b)) ≤
      θ'*a*log (θ'/θ)+(1-θ')*b*log ((1-θ')/(1-θ)) := by
  have h0 : 0 < 1-θ := by linarith
  have h0' : 0 < 1-θ' := by linarith
  have h := Tier2Information.log_sum_finite
    (fun x : Bool => if x then θ'*a else (1-θ')*b)
    (fun x : Bool => if x then θ*a else (1-θ)*b) Finset.univ
    (fun x => by
      cases x
      · exact mul_nonneg h0'.le hb
      · exact mul_nonneg hθ'.1.le ha)
    (fun x => by
      cases x
      · exact mul_nonneg h0.le hb
      · exact mul_nonneg hθ.1.le ha)
    (fun x => by
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        intro hx
        have : b = 0 := by
          rcases mul_eq_zero.mp hx with h | h
          · exact absurd h h0.ne'
          · exact h
        rw [this, mul_zero]
      · simp only [↓reduceIte]
        intro hx
        have : a = 0 := by
          rcases mul_eq_zero.mp hx with h | h
          · exact absurd h hθ.1.ne'
          · exact h
        rw [this, mul_zero])
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true] at h
  have e1 : θ'*a*log (θ'*a/(θ*a)) = θ'*a*log (θ'/θ) := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · simp [ha0]
    · rw [mul_div_mul_right _ _ ha0]
  have e2 : (1-θ')*b*log ((1-θ')*b/((1-θ)*b)) = (1-θ')*b*log ((1-θ')/(1-θ)) := by
    rcases eq_or_ne b 0 with hb0 | hb0
    · simp [hb0]
    · rw [mul_div_mul_right _ _ hb0]
  rw [e1, e2] at h
  exact h

theorem otherMass_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (ω : Fin n → Option Bool) (i : Fin m) : 0 ≤ otherMass pol d q ω i := by
  unfold otherMass coinMix
  apply mul_nonneg (pathValidity_nonneg pol ω)
  apply Finset.prod_nonneg
  intro j _
  have hA := coinLike_nonneg pol ω j (p := 1/2+d j) (by linarith [(hd j).1])
    (by linarith [(hd j).2])
  have hB := coinLike_nonneg pol ω j (p := 1/2-d j) (by linarith [(hd j).2])
    (by linarith [(hd j).1])
  exact add_nonneg (mul_nonneg (hq j).1 hA) (mul_nonneg (sub_nonneg.mpr (hq j).2) hB)

/-- Changing the prior of one coin changes only that coin's mixture factor. -/
theorem transcriptLaw_update {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (v : ℝ) :
    transcriptLaw pol d (Function.update q i v) ω =
      otherMass pol d q ω i *
        (v*coinLike pol ω i (1/2+d i)+(1-v)*coinLike pol ω i (1/2-d i)) := by
  rw [transcriptLaw_split pol d (Function.update q i v) ω i]
  congr 1
  · unfold otherMass
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    unfold coinMix
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  · unfold coinMix
    rw [Function.update_self]

/-- On the support of the first law, the log-likelihood ratio of two prior
choices is the sum of the per-coin log ratios. -/
theorem transcript_log_ratio_sum {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q r : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hr : ∀ i, 0 < r i ∧ r i < 1) (ω : Fin n → Option Bool) :
    transcriptLaw pol d q ω * log (transcriptLaw pol d q ω / transcriptLaw pol d r ω) =
      ∑ i, transcriptLaw pol d q ω * log (coinMix pol d q ω i / coinMix pol d r ω i) := by
  by_cases hP : transcriptLaw pol d q ω = 0
  · simp [hP]
  have hfq : transcriptLaw pol d q ω = pathValidity pol ω * ∏ i, coinMix pol d q ω i :=
    transcriptLaw_factor pol d q ω
  have hfr : transcriptLaw pol d r ω = pathValidity pol ω * ∏ i, coinMix pol d r ω i :=
    transcriptLaw_factor pol d r ω
  have hV : pathValidity pol ω ≠ 0 := by
    intro h; apply hP; rw [hfq, h, zero_mul]
  have hq0 : ∀ i, coinMix pol d q ω i ≠ 0 := by
    intro i h; apply hP; rw [hfq, Finset.prod_eq_zero (Finset.mem_univ i) h, mul_zero]
  have hr0 : ∀ i, coinMix pol d r ω i ≠ 0 := by
    intro i h
    have hA := coinLike_nonneg pol ω i (p := 1/2+d i) (by linarith [(hd i).1])
      (by linarith [(hd i).2])
    have hB := coinLike_nonneg pol ω i (p := 1/2-d i) (by linarith [(hd i).2])
      (by linarith [(hd i).1])
    unfold coinMix at h
    have h1 : r i * coinLike pol ω i (1/2+d i) = 0 := by
      nlinarith [mul_nonneg (hr i).1.le hA, mul_nonneg (sub_pos.mpr (hr i).2).le hB]
    have h2 : (1-r i) * coinLike pol ω i (1/2-d i) = 0 := by
      nlinarith [mul_nonneg (hr i).1.le hA, mul_nonneg (sub_pos.mpr (hr i).2).le hB]
    have hA0 : coinLike pol ω i (1/2+d i) = 0 :=
      (mul_eq_zero.mp h1).resolve_left (hr i).1.ne'
    have hB0 : coinLike pol ω i (1/2-d i) = 0 :=
      (mul_eq_zero.mp h2).resolve_left (sub_pos.mpr (hr i).2).ne'
    apply hq0 i
    unfold coinMix
    rw [hA0, hB0, mul_zero, mul_zero, add_zero]
  rw [← Finset.mul_sum]
  congr 1
  rw [hfq, hfr, mul_div_mul_left _ _ hV,
    log_div (Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hr0 i)),
    log_prod (fun i _ => hq0 i), log_prod (fun i _ => hr0 i), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [log_div (hq0 i) (hr0 i)]

/-- Coin `i` costs at most its visit mass times the chi-square divergence of
the two constant priors. -/
theorem coin_kl_le_visit {m n : ℕ} (pol : List Bool → Option (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) {θ θ' : ℝ} (hθ : 0 < θ ∧ θ < 1)
    (hθ' : 0 < θ' ∧ θ' < 1) (i : Fin m) :
    (∑ ω : Fin n → Option Bool, transcriptLaw pol d (fun _ => θ') ω *
        log (coinMix pol d (fun _ => θ') ω i / coinMix pol d (fun _ => θ) ω i)) ≤
      (θ'-θ)^2/(θ*(1-θ)) *
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → Option Bool => i ∈ queriedCoins pol ω),
          transcriptLaw pol d (fun _ => θ') ω := by
  classical
  set S := Finset.univ.filter (fun ω : Fin n → Option Bool => i ∈ queriedCoins pol ω) with hS
  set P : (Fin n → Option Bool) → ℝ := transcriptLaw pol d (fun _ => θ') with hPdef
  set O : (Fin n → Option Bool) → ℝ := fun ω => otherMass pol d (fun _ => θ') ω i with hOdef
  set A : (Fin n → Option Bool) → ℝ := fun ω => coinLike pol ω i (1/2+d i) with hAdef
  set B : (Fin n → Option Bool) → ℝ := fun ω => coinLike pol ω i (1/2-d i) with hBdef
  have hA : ∀ ω, 0 ≤ A ω := fun ω => coinLike_nonneg pol ω i (by linarith [(hd i).1])
    (by linarith [(hd i).2])
  have hB : ∀ ω, 0 ≤ B ω := fun ω => coinLike_nonneg pol ω i (by linarith [(hd i).2])
    (by linarith [(hd i).1])
  have hq' : ∀ j : Fin m, 0 ≤ (fun _ => θ') j ∧ (fun _ => θ') j ≤ 1 :=
    fun _ => ⟨hθ'.1.le, hθ'.2.le⟩
  have hO : ∀ ω, 0 ≤ O ω := fun ω => otherMass_nonneg pol d _ hd hq' ω i
  have hPsplit : ∀ ω, P ω = O ω * (θ'*A ω+(1-θ')*B ω) := fun ω =>
    transcriptLaw_split pol d (fun _ => θ') ω i
  -- extreme priors for coin i
  set Wp : (Fin n → Option Bool) → ℝ :=
    transcriptLaw pol d (Function.update (fun _ => θ') i 1) with hWpdef
  set Wm : (Fin n → Option Bool) → ℝ :=
    transcriptLaw pol d (Function.update (fun _ => θ') i 0) with hWmdef
  have hWp : ∀ ω, Wp ω = O ω * A ω := by
    intro ω
    rw [hWpdef, transcriptLaw_update]
    simp only [hOdef, hAdef]
    ring
  have hWm : ∀ ω, Wm ω = O ω * B ω := by
    intro ω
    rw [hWmdef, transcriptLaw_update]
    simp only [hOdef, hBdef]
    ring
  have hupd (u : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) :
      ∀ j : Fin m, 0 ≤ Function.update (fun _ => θ') i u j ∧
        Function.update (fun _ => θ') i u j ≤ 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hu
    · rw [Function.update_of_ne hj]; exact ⟨hθ'.1.le, hθ'.2.le⟩
  have hWp1 : ∑ ω, Wp ω = 1 :=
    (transcript_law_total m n pol d _ hd (hupd 1 ⟨zero_le_one, le_rfl⟩)).2
  have hWm1 : ∑ ω, Wm ω = 1 :=
    (transcript_law_total m n pol d _ hd (hupd 0 ⟨le_rfl, zero_le_one⟩)).2
  -- off the visited transcripts, coin i is inert
  have hoff : ∀ ω, ¬ (i ∈ queriedCoins pol ω) → A ω = 1 ∧ B ω = 1 := fun ω hω =>
    ⟨coinLike_eq_one_of_not_queried pol ω i hω _, coinLike_eq_one_of_not_queried pol ω i hω _⟩
  have hoffW : ∑ ω ∈ Finset.univ.filter (fun ω => ¬ (i ∈ queriedCoins pol ω)), Wp ω =
      ∑ ω ∈ Finset.univ.filter (fun ω => ¬ (i ∈ queriedCoins pol ω)), Wm ω := by
    apply Finset.sum_congr rfl
    intro ω hω
    have h := hoff ω (Finset.mem_filter.mp hω).2
    rw [hWp, hWm, h.1, h.2]
  have hsplitp := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun ω => i ∈ queriedCoins pol ω) Wp
  have hsplitm := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun ω => i ∈ queriedCoins pol ω) Wm
  have hvisit : ∑ ω ∈ S, Wp ω = ∑ ω ∈ S, Wm ω := by
    rw [hS]; linarith
  have hPW : ∀ ω, P ω = θ'*Wp ω+(1-θ')*Wm ω := by
    intro ω; rw [hPsplit, hWp, hWm]; ring
  have hPS : ∑ ω ∈ S, P ω = ∑ ω ∈ S, Wp ω := by
    rw [Finset.sum_congr rfl (fun ω _ => hPW ω), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hvisit]
    ring
  -- the sum over the transcripts that never query coin i vanishes
  have hzero : ∑ ω ∈ Finset.univ.filter (fun ω => ¬ (i ∈ queriedCoins pol ω)),
      P ω * log (coinMix pol d (fun _ => θ') ω i / coinMix pol d (fun _ => θ) ω i) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    have h := hoff ω (Finset.mem_filter.mp hω).2
    have h' : coinMix pol d (fun _ => θ') ω i = 1 := by
      unfold coinMix
      simp only [hAdef, hBdef] at h
      rw [h.1, h.2]; ring
    have h'' : coinMix pol d (fun _ => θ) ω i = 1 := by
      unfold coinMix
      simp only [hAdef, hBdef] at h
      rw [h.1, h.2]; ring
    rw [h', h'', div_one, log_one, mul_zero]
  -- pointwise log-sum bound
  have hpt : ∀ ω, P ω * log (coinMix pol d (fun _ => θ') ω i / coinMix pol d (fun _ => θ) ω i) ≤
      θ'*log (θ'/θ)*Wp ω+(1-θ')*log ((1-θ')/(1-θ))*Wm ω := by
    intro ω
    have hls := two_point_log_sum hθ hθ' (hA ω) (hB ω)
    have hc' : coinMix pol d (fun _ => θ') ω i = θ'*A ω+(1-θ')*B ω := rfl
    have hc : coinMix pol d (fun _ => θ) ω i = θ*A ω+(1-θ)*B ω := rfl
    rw [hPsplit, hc', hc, hWp, hWm, mul_assoc]
    have := mul_le_mul_of_nonneg_left hls (hO ω)
    linarith
  have hmain : ∑ ω, P ω * log (coinMix pol d (fun _ => θ') ω i / coinMix pol d (fun _ => θ) ω i)
      ≤ klB θ' θ * ∑ ω ∈ S, P ω := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => i ∈ queriedCoins pol ω),
      hzero, add_zero]
    calc
      _ ≤ ∑ ω ∈ S, (θ'*log (θ'/θ)*Wp ω+(1-θ')*log ((1-θ')/(1-θ))*Wm ω) :=
        Finset.sum_le_sum (fun ω _ => hpt ω)
      _ = klB θ' θ * ∑ ω ∈ S, P ω := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hvisit, hPS]
        unfold klB
        ring
  have hvis0 : 0 ≤ ∑ ω ∈ S, P ω :=
    Finset.sum_nonneg (fun ω _ => (transcript_law_total m n pol d _ hd hq').1 ω)
  exact hmain.trans (mul_le_mul_of_nonneg_right (klB_le_chisq θ' θ hθ'.1 hθ'.2 hθ.1 hθ.2) hvis0)

/-- Two constant sign priors: an adaptive transcript of horizon `n` carries at
most `n` chi-square units, whatever the number of coins and the policy. -/
theorem constant_transcript_kl {m : ℕ} (n : ℕ) (pol : List Bool → Option (Fin m))
    (d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) {θ θ' : ℝ}
    (hθ : 0 < θ ∧ θ < 1) (hθ' : 0 < θ' ∧ θ' < 1) :
    klFT (transcriptLaw (n:=n) pol d (fun _ => θ')) (transcriptLaw pol d (fun _ => θ)) ≤
      n*((θ'-θ)^2/(θ*(1-θ))) := by
  classical
  have hq' : ∀ j : Fin m, 0 ≤ (fun _ => θ') j ∧ (fun _ => θ') j ≤ 1 :=
    fun _ => ⟨hθ'.1.le, hθ'.2.le⟩
  have htot := transcript_law_total m n pol d _ hd hq'
  have hχ : 0 ≤ (θ'-θ)^2/(θ*(1-θ)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg hθ.1.le (by linarith [hθ.2]))
  unfold klFT
  rw [Finset.sum_congr rfl (fun ω _ => transcript_log_ratio_sum pol d (fun _ => θ') (fun _ => θ)
    hd (fun _ => hθ) ω), Finset.sum_comm]
  calc
    _ ≤ ∑ i, (θ'-θ)^2/(θ*(1-θ)) *
          ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → Option Bool => i ∈ queriedCoins pol ω),
            transcriptLaw pol d (fun _ => θ') ω :=
      Finset.sum_le_sum (fun i _ => coin_kl_le_visit pol d hd hθ hθ' i)
    _ = (θ'-θ)^2/(θ*(1-θ)) * ∑ ω : Fin n → Option Bool,
          ((queriedCoins pol ω).card:ℝ) * transcriptLaw pol d (fun _ => θ') ω := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (θ'-θ)^2/(θ*(1-θ)) * ∑ ω : Fin n → Option Bool,
          (n:ℝ) * transcriptLaw pol d (fun _ => θ') ω := by
      apply mul_le_mul_of_nonneg_left _ hχ
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast queriedCoins_card_le pol ω) (htot.1 ω)
    _ = n*((θ'-θ)^2/(θ*(1-θ))) := by
      rw [← Finset.mul_sum, htot.2]
      ring

end ThresholdHC.BernoulliTimeUniform
