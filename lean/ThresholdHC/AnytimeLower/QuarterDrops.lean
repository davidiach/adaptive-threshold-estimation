
import ThresholdHC.AnytimeLower.TailLimits

noncomputable section
open Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

theorem exists_quarter_drop (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (i : ℕ) :
    ∃ j, i < j ∧ W j ≤ W i/4 := by
  have he : ∀ᶠ j in atTop, W j < W i/4 :=
    hlim.eventually (eventually_lt_nhds (div_pos (hpos i) (by norm_num)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact ⟨max N (i+1),by omega,(hN _ (le_max_left _ _)).le⟩

def nextDrop (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (i : ℕ) : ℕ :=
  Nat.find (exists_quarter_drop W hpos hlim i)

theorem nextDrop_spec (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (i : ℕ) :
    i < nextDrop W hpos hlim i ∧ W (nextDrop W hpos hlim i) ≤ W i/4 :=
  Nat.find_spec (exists_quarter_drop W hpos hlim i)

theorem before_nextDrop (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) {i j : ℕ}
    (hij : i ≤ j) (hj : j < nextDrop W hpos hlim i) : W i/4 < W j := by
  by_cases he : i = j
  · subst j
    linarith [hpos i]
  · have hmin := Nat.find_min (exists_quarter_drop W hpos hlim i) hj
    have hij' : i < j := lt_of_le_of_ne hij he
    exact lt_of_not_ge (fun h => hmin ⟨hij',h⟩)

def dropIndex (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) : ℕ → ℕ
  | 0 => 0
  | k+1 => nextDrop W hpos hlim (dropIndex W hpos hlim k)

theorem dropIndex_strictMono (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) : StrictMono (dropIndex W hpos hlim) :=
  strictMono_nat_of_lt_succ (fun k => (nextDrop_spec W hpos hlim (dropIndex W hpos hlim k)).1)

theorem dropIndex_mass (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (k : ℕ) :
    W (dropIndex W hpos hlim (k+1)) ≤ W (dropIndex W hpos hlim k)/4 :=
  (nextDrop_spec W hpos hlim _).2

def dropSeparation (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (k : ℕ) : ℝ :=
  (W (dropIndex W hpos hlim k)-W (dropIndex W hpos hlim (k+1)))/32

theorem dropSeparation_lower (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (k : ℕ) :
    3*W (dropIndex W hpos hlim k)/128 ≤ dropSeparation W hpos hlim k := by
  have h := dropIndex_mass W hpos hlim k
  unfold dropSeparation
  linarith

theorem dropSeparation_pos (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (k : ℕ) : 0 < dropSeparation W hpos hlim k := by
  have h := dropSeparation_lower W hpos hlim k
  have hp := hpos (dropIndex W hpos hlim k)
  linarith

theorem dropSeparation_separated (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0)) (hmono : Antitone W) (i k : ℕ) (hik : i < k) :
    3*dropSeparation W hpos hlim k ≤ dropSeparation W hpos hlim i := by
  have hn := dropIndex_strictMono W hpos hlim
  have hm := hmono (hn.monotone (show i+1 ≤ k by omega))
  have hq := dropIndex_mass W hpos hlim i
  have hp := hpos (dropIndex W hpos hlim (k+1))
  unfold dropSeparation
  linarith

theorem nextDrop_overshoot (W : ℕ → ℝ) (hpos : ∀ j, 0 < W j)
    (hlim : Tendsto W atTop (𝓝 0))
    (hquarter : ∀ j, W j/4 ≤ W (j+1)) (i : ℕ) :
    W i/16 < W (nextDrop W hpos hlim i) := by
  let j := nextDrop W hpos hlim i
  have hj : i < j := (nextDrop_spec W hpos hlim i).1
  have hp := before_nextDrop W hpos hlim (i:=i) (j:=j-1) (by omega) (by omega)
  have hq := hquarter (j-1)
  rw [show j-1+1=j by omega] at hq
  linarith

end ThresholdHC.AnytimeLower
