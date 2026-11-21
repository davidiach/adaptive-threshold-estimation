import ThresholdHC.LargeBudgetRMS.RevisitPolynomial
import ThresholdHC.LargeBudgetRMS.RevisitPolicy

/-! A rational terminal rule and a kernel-evaluated polynomial certificate
for its squared risk on the entire interval of sign fractions. -/
namespace ThresholdHC.RevisitUpper
open ThresholdHC.SharpRMS.Revisit ThresholdHC.SharpRMS.Revisit.IntPoly

def table : List (List ℕ) := [
  [339,577,977,1642,2726,4438],
  [577,977,1642,2726,4438,7020],
  [977,1642,2726,4438,7020,10678],
  [1642,2726,4438,7020,10678,15491],
  [2726,4438,7020,10678,15491,21398],
  [2260,4946,9871,16993,24644,31191],
  [3747,7836,14443,22511,30076,36513],
  [6105,11977,20118,28631,36154,42918],
  [9707,17564,26838,35563,43297,50450],
  [14975,24713,34693,43594,51486,58514],
  [28333,36330,45302,54698,63670,71667],
  [41486,48514,56406,65307,75287,85025],
  [49550,56703,64437,73162,82436,90293],
  [57082,63846,71369,79882,88023,93895],
  [63487,69924,77489,85557,92164,96253],
  [68809,75356,83007,90129,95054,97740],
  [78602,84509,89322,92980,95562,97274],
  [84509,89322,92980,95562,97274,98358],
  [89322,92980,95562,97274,98358,99023],
  [92980,95562,97274,98358,99023,99423],
  [95562,97274,98358,99023,99423,99661]]

def entry (j k : ℕ) := ((table[j]?.getD [])[k]?).getD 0

noncomputable def estimate (j k : ℕ) : ℝ := (entry j k : ℝ)/100000
noncomputable abbrev bound : ℝ := 188087/1000000

private def up : Coeffs := [3,4]
private def down : Coeffs := [7,-4]

def factors (j : ℕ) : Coeffs × Coeffs × ℕ × ℕ :=
  match mode j with
  | some true => ([9,40],[21],j-5,20-j)
  | some false => ([21],[49,-40],j,20-j-5)
  | none => (up,down,j,20-j)

/-- Joint word probabilities have denominator 10^25, counting each reused
coin's two observations jointly. The loss contributes a further 10^10. -/
def riskCoeffs : Coeffs := sumTo (fun j =>
  let (a,b,h,t) := factors j
  scale ((20:ℕ).choose j) (mul (mul (power up h) (power down t))
    (sumTo (fun k => scale ((5:ℕ).choose k)
      (mul (mul (power a k) (power b (5-k))) (power [entry j k,-100000] 2))) 6))) 21

private def expandedRisk : Coeffs := [
  3537633984078752937713046742200750,
  -2636444099437049083602039950211200,
  27082013733631188438525277587612800,
  -102317827589125634120485587860838400,
  160178805861782962489282145093299200,
  -18166089764940469216867137643315200,
  -309908438658544515772311603487539200,
  501586714120437026959579693016678400,
  -303271370638271659230045519475507200,
  -197742974559561899281947178722918400,
  637470715845390206905287524640358400,
  -683547441059928059645166423218585600,
  320516802034820909090462141461299200,
  139739285429455444554783950005862400,
  -337951296240240199214094877930291200,
  233657620273575862232645530078412800,
  -64837567504663609123766505622732800,
  -4150578554031053483199268336435200,
  1298800236600242568794734172569600,
  5653281078297047672313410171699200,
  -3249667077986855025888827382169600,
  590369263630115274462908435660800,
  21315289864123058991494961561600,
  -16347107089622302397790211276800,
  22985835962644050976597606400,
  321425541161411475721420800000,
  -24725041627800882747801600000,
  0]

private def difference : Coeffs := add [10^35 * 188087^2] (scale (-(10^12)) expandedRisk)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem coefficients : riskCoeffs = expandedRisk := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem certificate (p : ℝ) (hp : p∈Set.Icc 0 1) : value riskCoeffs p ≤ (10:ℝ)^35*bound^2 := by
  have cert : 0≤value difference p := by
    by_cases h0 : (4:ℝ)*p < 1
    · exact interval_sound _ 0 4 (by decide) (by decide +kernel) p (by norm_num; linarith [hp.1]) (by norm_num; linarith only [h0])
    by_cases h1 : (32:ℝ)*p < 9
    · exact interval_sound _ 8 32 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h1])
    by_cases h2 : (32:ℝ)*p < 10
    · exact interval_sound _ 9 32 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h2])
    by_cases h3 : (16:ℝ)*p < 6
    · exact interval_sound _ 5 16 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h3])
    by_cases h4 : (8:ℝ)*p < 4
    · exact interval_sound _ 3 8 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h4])
    by_cases h5 : (8:ℝ)*p < 5
    · exact interval_sound _ 4 8 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h5])
    by_cases h6 : (16:ℝ)*p < 11
    · exact interval_sound _ 10 16 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h6])
    by_cases h7 : (32:ℝ)*p < 23
    · exact interval_sound _ 22 32 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h7])
    by_cases h8 : (32:ℝ)*p < 24
    · exact interval_sound _ 23 32 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h8])
    by_cases h9 : (4:ℝ)*p < 4
    · exact interval_sound _ 3 4 (by decide) (by decide +kernel) p (by norm_num; linarith) (by norm_num; linarith only [h9])
    have eq : p=1 := by linarith [hp.2]
    rw [eq]; norm_num [difference,expandedRisk,value]
  unfold difference at cert
  rw [←coefficients,value_add,value_scale] at cert
  norm_num [value,bound] at cert ⊢
  linarith only [cert]

end ThresholdHC.RevisitUpper
