import ThresholdHC.SharpRMS.Heterogeneous

/-! An explicit parameter-independent channel at every local history. -/
noncomputable section
namespace ThresholdHC.SharpRMS

def wordMass (p : ℝ) (h l : ℕ) := p^h*(1-p)^l

def conditionalWord (a f e : ℝ) (h l : ℕ) :=
  ((1+f*e)/2)*wordMass ((1+a)/2) h l + ((1-f*e)/2)*wordMass ((1-a)/2) h l

private def localPosterior (a : ℝ) (h l : ℕ) :=
  let A := wordMass ((1+a)/2) h l
  let B := wordMass ((1-a)/2) h l
  (A-B)/(A+B)

def channelMean (a s : ℝ) (h l : ℕ) (y : ℝ) :=
  if a ≤ s then (a/s)*y else
    let z := localPosterior a h l
    let c := copyProbability (s/a) z
    c*y+(1-c)*fallbackMean a z

theorem measurable_channelMean (s y : ℝ) (h l : ℕ) : Measurable (fun a => channelMean a s h l y) := by
  have fb (a z : ℝ) : fallbackMean a z = a/z := by
    by_cases hz : z=0 <;> simp [fallbackMean,hz]
  unfold channelMean
  simp_rw [fb]
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · fun_prop
  · unfold localPosterior wordMass copyProbability
    fun_prop

private theorem post_gap (a : ℝ) (ha : 0<a) (ha' : a≤1) (h l : ℕ) :
    |localPosterior a h l|≤1 ∧ (localPosterior a h l=0 ∨ a≤|localPosterior a h l|) := by
  simpa only [localPosterior,wordMass,show 1-(1+a)/2=(1-a)/2 by ring,
    show 1-(1-a)/2=(1+a)/2 by ring] using word_posterior_gap a ha ha' h l

theorem channel_range (a s : ℝ) (ha : 0<a) (ha' : a≤1) (hs : 0<s) (h l : ℕ)
    (y : ℝ) (hy : |y|≤1) : |channelMean a s h l y|≤1 := by
  unfold channelMean
  split_ifs with small
  · rw [abs_mul,abs_of_nonneg (div_nonneg ha.le hs.le)]
    exact (mul_le_mul_of_nonneg_left hy (div_nonneg ha.le hs.le)).trans (by simpa using (div_le_one hs).mpr small)
  · obtain ⟨c0,c1,f0,_⟩ := critical_step_kernel a s _ hs (lt_of_not_ge small)
      (post_gap a ha ha' h l).1 (post_gap a ha ha' h l).2
    let z := localPosterior a h l
    let c := copyProbability (s/a) z
    change |c*y+(1-c)*fallbackMean a z|≤1
    calc
      _ ≤ |c*y|+|(1-c)*fallbackMean a z| := abs_add_le ..
      _ ≤ c+(1-c) := by
        rw [abs_mul,abs_mul,abs_of_nonneg c0,abs_of_nonneg (sub_nonneg.mpr c1)]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_left hy c0)
          (by simpa using mul_le_mul_of_nonneg_left f0 (sub_nonneg.mpr c1))
      _ = 1 := by ring

private theorem mean_identity (a s e : ℝ) (ha : 0<a) (ha' : a≤1) (hs : 0<s)
    (h l : ℕ) (he : e = -1 ∨ e=1) :
    let p := (1+a)/2
    let q := (1-a)/2
    let A := wordMass p h l
    let B := wordMass q h l
    let f := min 1 (s/a)
    let L := conditionalWord a f e h l
    L*(((1+s*e)/2)*channelMean a s h l 1 + ((1-s*e)/2)*channelMean a s h l (-1)) =
      a*(((1+f*e)/2)*A-((1-f*e)/2)*B) := by
  let A := wordMass ((1+a)/2) h l
  let B := wordMass ((1-a)/2) h l
  let z := localPosterior a h l
  have A0 : 0≤A := by dsimp [A,wordMass]; apply mul_nonneg <;> apply pow_nonneg <;> linarith
  have B0 : 0≤B := by dsimp [B,wordMass]; apply mul_nonneg <;> apply pow_nonneg <;> linarith
  by_cases small : a ≤ s
  · have f : min 1 (s/a) = 1 := min_eq_left ((one_le_div ha).mpr small)
    simp only [f,conditionalWord,channelMean,small,↓reduceIte]
    rcases he with rfl|rfl <;> field_simp <;> ring
  · let f := s/a
    let c := copyProbability f z
    let b := fallbackMean a z
    have sf : s<a := lt_of_not_ge small
    have fmin : min 1 (s/a) = f := min_eq_right ((div_le_one ha).mpr sf.le)
    have lat := post_gap a ha ha' h l
    obtain ⟨_,_,_,step⟩ := critical_step_kernel a s z hs sf lat.1 lat.2
    have hstep := step e he
    have m : ((1+s*e)/2)*channelMean a s h l 1+((1-s*e)/2)*channelMean a s h l (-1) =
        a*(z+f*e)/(1+f*z*e) := by
      simp only [channelMean,small,↓reduceIte]
      change _*(c*1+(1-c)*b)+_*(c*(-1)+(1-c)*b)=_
      change c*(s*e)+(1-c)*b=_ at hstep
      linarith only [hstep]
    rw [fmin,m]
    change conditionalWord a f e h l * (a*(z+f*e)/(1+f*z*e)) = a*(((1+f*e)/2)*A-((1-f*e)/2)*B)
    change (((1+f*e)/2)*A+((1-f*e)/2)*B)*_ = _
    by_cases hz : A+B=0
    · have az : A=0 := by linarith
      have bz : B=0 := by linarith
      simp [az,bz]
    have f0 : 0<f := div_pos hs ha
    have f1 : f<1 := (div_lt_one ha).mpr sf
    have fz : |f*z|<1 := by
      rw [abs_mul,abs_of_pos f0]
      exact (mul_le_mul_of_nonneg_left lat.1 f0.le).trans_lt (by simpa using f1)
    have den : 1+f*z*e≠0 := by
      rcases he with rfl|rfl <;> linarith [(abs_lt.mp fz).1,(abs_lt.mp fz).2]
    rw [← mul_div_assoc,div_eq_iff den]
    change (((1+f*e)/2)*A+((1-f*e)/2)*B)*(a*((A-B)/(A+B)+f*e)) =
      a*(((1+f*e)/2)*A-((1-f*e)/2)*B)*(1+f*((A-B)/(A+B))*e)
    field_simp [hz]
    ring

/-- With the source sign fixed, one paid source flip and the history-based
channel give both target extension probabilities. The same channel works for
either source sign and every target word, even when its probability is zero. -/
theorem simulate_word_step (a s e : ℝ) (ha : 0<a) (ha' : a≤1) (hs : 0<s)
    (h l : ℕ) (he : e = -1 ∨ e=1) :
    let f := min 1 (s/a)
    let L := conditionalWord a f e h l
    let m := ((1+s*e)/2)*channelMean a s h l 1+((1-s*e)/2)*channelMean a s h l (-1)
    conditionalWord a f e (h+1) l = L*((1+m)/2) ∧
      conditionalWord a f e h (l+1) = L*((1-m)/2) := by
  let f := min 1 (s/a)
  let A := wordMass ((1+a)/2) h l
  let B := wordMass ((1-a)/2) h l
  let L := conditionalWord a f e h l
  let m := ((1+s*e)/2)*channelMean a s h l 1+((1-s*e)/2)*channelMean a s h l (-1)
  have hm : L*m=a*(((1+f*e)/2)*A-((1-f*e)/2)*B) := mean_identity a s e ha ha' hs h l he
  have hl : L=((1+f*e)/2)*A+((1-f*e)/2)*B := rfl
  have up p : wordMass p (h+1) l = wordMass p h l*p := by simp [wordMass,pow_succ]; ring
  have down p : wordMass p h (l+1) = wordMass p h l*(1-p) := by simp [wordMass,pow_succ]; ring
  change conditionalWord a f e (h+1) l = L*((1+m)/2) ∧ conditionalWord a f e h (l+1)=L*((1-m)/2)
  constructor
  · unfold conditionalWord
    rw [up,up]
    change ((1+f*e)/2)*(A*((1+a)/2))+((1-f*e)/2)*(B*((1-a)/2))=_
    linarith only [hm,hl]
  · unfold conditionalWord
    rw [down,down]
    change ((1+f*e)/2)*(A*(1-(1+a)/2))+((1-f*e)/2)*(B*(1-(1-a)/2))=_
    linarith only [hm,hl]

end ThresholdHC.SharpRMS
