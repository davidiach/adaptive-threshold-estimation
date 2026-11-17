import SharpCriticalBudget
import SharpInterpolation

/-! Integrating a finite upper histogram and transferring its price to the
original population experiment. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Tier6
open scoped ENNReal

private def box (N : ℕ) (i : Fin N) : Set ℝ := Icc ((i.val:ℝ)/N) (((i.val:ℝ)+1)/N)

private def histogram {N : ℕ} (h : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (box N i).indicator (fun _ => h i) t

private theorem box_integral {N : ℕ} (n : 0<N) (i : Fin N) (H : ℝ) :
    (∫ t in (0:ℝ)..1, (box N i).indicator (fun _=>H) t) = H/(N:ℝ) := by
  have np : (0:ℝ)<N := by exact_mod_cast n
  have hi : (i.val:ℝ)+1 ≤ N := by exact_mod_cast i.isLt
  have sub : box N i ⊆ Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨(by positivity : (0:ℝ) ≤ (i.val:ℝ)/N).trans ht.1,ht.2.trans ((div_le_one np).mpr hi)⟩
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_indicator (show MeasurableSet (box N i) from measurableSet_Icc),
    Measure.restrict_restrict (show MeasurableSet (box N i) from measurableSet_Icc),
    inter_eq_left.mpr sub,integral_const]
  simp only [box,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul]
  rw [show ((i.val:ℝ)+1)/N-i.val/N=1/(N:ℝ) by ring, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- If the bin heights majorize a valid price throughout each positive-bias
bin at h, their rescaled sum proves the unrestricted critical-point lower
bound at s=2g for every s≤h. -/
theorem minimax_from_rectangles (g : Gap) (B h : ℝ) (hs : 2*g.val ≤ h) (hh : h < 1)
    (hb : (2*g.val)^2*B=4) (N : ℕ) (hn : 0<N) (V : Fin N → ℝ)
    (nonneg : ∀ i, 0 ≤ V i) (sum : (h/(2*g.val))^2*((∑ i, V i)/(N:ℝ)) ≤ 2/3)
    (price : ∀ i : Fin N, ∀ t ∈ Icc ((i.val:ℝ)/N) (((i.val:ℝ)+1)/N), t < 1 →
      ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice h t P ∧ (1-t^2)^2 ≤ V i*P) :
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  have sp : 0<s := by dsimp [s]; linarith [g.property.1]
  have hp := sp.trans_le hs
  have np : (0:ℝ)<N := by exact_mod_cast hn
  let C := (h/s)^2
  let E := histogram V
  let K := fun t : ℝ => C*E |t|
  have cm : ∀ i : Fin N, Measurable ((box N i).indicator (fun _=>V i)) :=
    fun i => measurable_const.indicator measurableSet_Icc
  have em : Measurable E := Finset.measurable_sum _ (fun i _ => cm i)
  have each (i : Fin N) (t : ℝ) : (box N i).indicator (fun _=>V i) t ∈ Icc 0 (V i) := by
    by_cases ht : t ∈ box N i <;> simp [ht,nonneg i]
  have ecap (t : ℝ) : E t ∈ Icc 0 (∑ i, V i) :=
    ⟨Finset.sum_nonneg (fun i _ => (each i t).1),Finset.sum_le_sum (fun i _ => (each i t).2)⟩
  have I (i : Fin N) : IntervalIntegrable ((box N i).indicator (fun _=>V i)) volume 0 1 := by
    apply IntervalIntegrable.mono_fun (intervalIntegrable_const (b := (1:ℝ)) (c := V i))
      (cm i).aestronglyMeasurable
    apply ae_of_all
    intro t
    simpa only [Real.norm_eq_abs,abs_of_nonneg (each i t).1,abs_of_nonneg (nonneg i)] using (each i t).2
  have ei : IntervalIntegrable E volume 0 1 := by
    have eqn : E = ∑ i : Fin N, (box N i).indicator (fun _ => V i) := by
      funext t
      simp [E,histogram,Finset.sum_apply]
    rw [eqn]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => I i)
  have eint : (∫ t in (0:ℝ)..1, E t) = (∑ i, V i)/(N:ℝ) := by
    change (∫ t in (0:ℝ)..1, ∑ i, (box N i).indicator (fun _ => V i) t) = _
    rw [intervalIntegral.integral_finsetSum (fun i _ => I i),Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => box_integral hn i _)
  have eci := ei.const_mul C
  have contact : EqOn (fun t => C*E (-t)) K (uIoo (-1:ℝ) 0) := by
    rw [uIoo_of_le (by norm_num)]
    intro t ht
    simp [K,abs_of_neg ht.2]
  have contact' : EqOn (fun t => C*E t) K (uIoo (0:ℝ) 1) := by
    rw [uIoo_of_le zero_le_one]
    intro t ht
    simp [K,abs_of_pos ht.1]
  have reflected : IntervalIntegrable (fun t => C*E (-t)) volume (-1) 0 := by
    simpa only [neg_zero] using (IntervalIntegrable.iff_comp_neg (f := fun t => C*E t)
      (a := 1) (b := 0)).mp eci.symm
  have left := reflected.congr_uIoo contact
  have right := eci.congr_uIoo contact'
  apply minimax_from_tapered_price g B (hs.trans_lt hh) hb K
    (measurable_const.mul (em.comp measurable_abs)) (left.trans right)
  · exact ⟨C*∑ i, V i,fun t _ => ⟨mul_nonneg (sq_nonneg _) (ecap _).1,
      mul_le_mul_of_nonneg_left (ecap _).2 (sq_nonneg _)⟩⟩
  · rw [←intervalIntegral.integral_add_adjacent_intervals left right,
      ←intervalIntegral.integral_congr_uIoo contact,←intervalIntegral.integral_congr_uIoo contact',
      intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg]
    simp only [neg_zero,neg_neg,intervalIntegral.integral_const_mul,eint]
    change C*((∑ i, V i)/(N:ℝ)) + C*((∑ i, V i)/(N:ℝ)) ≤ _
    change C*((∑ i, V i)/(N:ℝ)) ≤ 2/3 at sum
    linarith only [sum]
  · intro t ht
    let j := ⌊abs t * N⌋₊
    have hj : j<N := (Nat.floor_lt (by positivity : 0 ≤ abs t * N)).mpr (by nlinarith only [mul_lt_mul_of_pos_right ht np])
    let i : Fin N := ⟨j,hj⟩
    have mem : |t| ∈ box N i :=
      ⟨(div_le_iff₀ np).mpr (Nat.floor_le (by positivity)),
        (le_div_iff₀ np).mpr (Nat.lt_floor_add_one _).le⟩
    obtain ⟨P,pp,p1,pa,pk⟩ := price i |t| mem ht
    have vi : V i ≤ E |t| := by
      have hi := Finset.single_le_sum (fun j _ => (each j |t|).1) (Finset.mem_univ i)
      simpa only [E,histogram,Set.indicator_of_mem mem] using hi
    have rpos : 0<(s/h)^2 := sq_pos_of_pos (div_pos sp hp)
    have rle : (s/h)^2≤1 := by
      have a := (div_le_one hp).mpr hs
      nlinarith [mul_nonneg (sub_nonneg.mpr a) (show 0≤1+s/h by positivity)]
    refine ⟨(s/h)^2*P,mul_pos rpos pp,(mul_le_mul_of_nonneg rle p1 rpos.le zero_le_one).trans_eq (by norm_num),
      interpolate_exit_price s h |t| P sp hs hh (abs_nonneg _) ht pp.le pa,?_⟩
    have q : K t*((s/h)^2*P)=E |t| * P := by dsimp [K,C]; field_simp
    rw [q,← sq_abs t]
    exact pk.trans (mul_le_mul_of_nonneg_right vi pp.le)

end ThresholdHC.SharpRMS
