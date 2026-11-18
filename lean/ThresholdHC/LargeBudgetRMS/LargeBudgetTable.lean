import ThresholdHC.SharpRMS.Entropy

/-! A rational estimator and an exact Bernstein certificate for its binomial risk.
The polynomial variable is the squared sign mean, (2p-1)^2. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget

abbrev radius : ℝ := 195454/1000000

def estimate25 (k : ℕ) : ℝ :=
  (([1,9,18,38,79,164,336,668,1249,2101,3085,3975,4686,5314,6025,6915,7899,8751,9332,9664,9836,9921,9962,9982,9991,9999] : List ℕ)[k]?.getD 0 : ℕ)/10000

private def riskPoly (x : ℝ) : ℝ :=
  (76362327416307926177978515625
    + 2067436707572937011718750000*x^1
    - 37152384302243041992187500000*x^2
    + 47642163467711914062500000000*x^3
    - 14856187717385351562500000000*x^4
    + 2603481433718440000000000000*x^5
    - 279268516221988000000000000*x^6
    + 17073030991837440000000000*x^7
    - 319733988474700800000000*x^8
    - 32834503347486720000000*x^9
    + 2724540204207833088000*x^10
    - 83170930271558041600*x^11
    + 855906583945674752*x^12
    + 4004930838855680*x^13)/2000000000000000000000000000000

private def bern : List ℕ → ℝ → ℝ
  | [], _ => 0
  | a::as, y => a*(1-y)^as.length+y*bern as y

private theorem bern_nonneg (as : List ℕ) (y : ℝ) (hy : y∈Set.Icc 0 1) : 0≤bern as y := by
  induction as with
  | nil => exact le_rfl
  | cons a as ih =>
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hy.2) _)) (mul_nonneg hy.1 ih)

private theorem interval0 (y : ℝ) (hy : y∈Set.Icc 0 1) : riskPoly (y/8) ≤ radius^2 := by
  let row : List ℕ := [
    172870925074734375000000000000,
    1188794431694203125000000000000,
    3159353619844710937500000000000,
    5352404590106750000000000000000,
    17706516541615393164062500000000,
    73825101041485472109062500000000,
    197746755934920267059812500000000,
    338288712833835365615255000000000,
    388459870118681826176872456250000,
    306100325513787127440995883750000,
    164387562590104966702375405423000,
    57772126537433682711771966304800,
    12020028919341977177267954082703,
    1125493701241274590805435861843]
  have identity : radius^2-riskPoly (y/8) = bern row y/8192000000000000000000000000000000 := by
    norm_num [riskPoly,bern,row,radius]
    ring
  exact sub_nonneg.mp (identity.trans_ge (div_nonneg (bern_nonneg row y hy) (by norm_num)))

private theorem interval1 (y : ℝ) (hy : y∈Set.Icc 0 1) : riskPoly ((1+y)/8) ≤ radius^2 := by
  let row : List ℕ := [
    1125493701241274590805435861843,
    17242807312931162183673378325215,
    120445467260503902788637057214944,
    508441174967190341920705227345792,
    1448613956105399476805907436272640,
    2944495303055247144641350196580352,
    4396753009388020262101455662284800,
    4887127258414556017263307456249856,
    4046492070875626365732255294291968,
    2466489891496437764588691552993280,
    1076358663549730828803679224594432,
    318606657451887897379988979056640,
    57359719572176537845322886414336,
    4745287754448320690346176544768]
  have identity : radius^2-riskPoly ((1+y)/8) = bern row y/8192000000000000000000000000000000 := by
    norm_num [riskPoly,bern,row,radius]
    ring
  exact sub_nonneg.mp (identity.trans_ge (div_nonneg (bern_nonneg row y hy) (by norm_num)))

private theorem interval2 (y : ℝ) (hy : y∈Set.Icc 0 1) : riskPoly ((1+y)/4) ≤ radius^2 := by
  let row : List ℕ := [
    1158517518175859543541547008,
    17174507636506697078333767680,
    116142291072646970038995124224,
    474847329920791316977221107712,
    1310745251016324539032508170240,
    2581684050547169870477743603712,
    3735560952267656759424878120960,
    4022944532179591441295526782976,
    3226279064744754460908358536448,
    1903854276185236666948556356480,
    803846750128878897802584832992,
    230035901884857805691655759600,
    40000468145233415721816900831,
    3192696539517104003586176423]
  have identity : radius^2-riskPoly ((1+y)/4) = bern row y/2000000000000000000000000000000 := by
    norm_num [riskPoly,bern,row,radius]
    ring
  exact sub_nonneg.mp (identity.trans_ge (div_nonneg (bern_nonneg row y hy) (by norm_num)))

private theorem interval3 (y : ℝ) (hy : y∈Set.Icc 0 1) : riskPoly ((1+y)/2) ≤ radius^2 := by
  let row : List ℕ := [
    3192696539517104003586176423,
    44514228750700224696227078835,
    281382871823632301313302027514,
    1067411569383978407051857754442,
    2708992640811406060543571459365,
    4849986309639582370686773078497,
    6285801410634841661636125549980,
    5946352019351956621549922478236,
    4077540518513010285758346342593,
    1977655667332580358295594217605,
    644293600706405443591162659402,
    126648276165380012392949035770,
    11364572233175101915063244691,
    240637809963598950657543]
  have identity : radius^2-riskPoly ((1+y)/2) = bern row y/2000000000000000000000000000000 := by
    norm_num [riskPoly,bern,row,radius]
    ring
  exact sub_nonneg.mp (identity.trans_ge (div_nonneg (bern_nonneg row y hy) (by norm_num)))

private theorem bounded (x : ℝ) (hx : x∈Set.Icc 0 1) : riskPoly x ≤ radius^2 := by
  rcases le_total x (1/8) with h | h
  · simpa only [show 8*x/8=x by ring] using interval0 (8*x) ⟨by linarith [hx.1],by linarith⟩
  rcases le_total x (1/4) with j | j
  · simpa only [show (1+(8*x-1))/8=x by ring] using interval1 (8*x-1) ⟨by linarith,by linarith⟩
  rcases le_total x (1/2) with l | l
  · simpa only [show (1+(4*x-1))/4=x by ring] using interval2 (4*x-1) ⟨by linarith,by linarith⟩
  simpa only [show (1+(2*x-1))/2=x by ring] using interval3 (2*x-1) ⟨by linarith,by linarith [hx.2]⟩

set_option maxHeartbeats 8000000 in
theorem table_risk (p : ℝ) (hp : p∈Set.Icc 0 1) :
    let b := 1/2+(2*p-1)*(1/5)
    (∑ j ∈ Finset.range 26, ((25:ℕ).choose j : ℝ)*b^j*(1-b)^(25-j)*(estimate25 j-p)^2) ≤ radius^2 := by
  dsimp only
  apply le_trans _ (bounded ((2*p-1)^2) ⟨sq_nonneg _,by nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]⟩)
  apply le_of_eq
  norm_num [riskPoly,Finset.sum_range_succ,estimate25,Nat.choose]
  ring

end ThresholdHC.SharpRMS.LargeBudget
