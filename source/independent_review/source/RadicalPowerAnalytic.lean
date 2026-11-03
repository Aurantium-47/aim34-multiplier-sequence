import ThreeQuarterDamping
import NewtonInterpolation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Algebra.Order.Floor.Semiring

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- Principal square-root/logarithm analytic branch, written with complex power. -/
def radicalPowerCore (w : ℂ) : ℂ :=
  Complex.exp (w ^ (1 / 2 : ℂ) * Complex.log w)

def radicalPowerAnalytic (m : ℝ) (z : ℂ) : ℂ := radicalPowerCore (z + m)

def shiftedRightHalfPlane (m : ℝ) : Set ℂ := {z | -m < z.re}

lemma isOpen_shiftedRightHalfPlane (m : ℝ) : IsOpen (shiftedRightHalfPlane m) :=
  isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_shiftedRightHalfPlane (m : ℝ) :
    IsPreconnected (shiftedRightHalfPlane m) :=
  (convex_halfSpace_gt Complex.reLm.isLinear (-m)).isPreconnected

lemma shifted_mem_slitPlane {m : ℝ} {z : ℂ} (hz : z ∈ shiftedRightHalfPlane m) :
    z + (m : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  change -m < z.re at hz
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

lemma differentiableOn_radicalPowerAnalytic (m : ℝ) :
    DifferentiableOn ℂ (radicalPowerAnalytic m) (shiftedRightHalfPlane m) := by
  intro z hz
  have hid : DifferentiableWithinAt ℂ (fun z : ℂ => z + m) (shiftedRightHalfPlane m) z :=
    differentiableWithinAt_id.add_const _
  exact ((hid.cpow_const (shifted_mem_slitPlane hz)).mul
    (hid.clog (shifted_mem_slitPlane hz))).cexp

lemma radicalPowerCore_ofReal {t : ℝ} (ht : 0 < t) :
    radicalPowerCore t = (Real.rpow t (Real.sqrt t) : ℂ) := by
  change radicalPowerCore t = ((t ^ Real.sqrt t : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos ht]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [radicalPowerCore, hhalf, ← Complex.ofReal_cpow ht.le,
    ← Complex.ofReal_log ht.le, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow]
  congr 1
  ring

lemma radicalPowerAnalytic_ofReal {m t : ℝ} (ht : 0 < t + m) :
    radicalPowerAnalytic m t = (Real.rpow (t + m) (Real.sqrt (t + m)) : ℂ) := by
  rw [radicalPowerAnalytic, ← Complex.ofReal_add]
  exact radicalPowerCore_ofReal ht

lemma sqrt_mul_log_le_threeQuarter {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * Real.log t ≤ 4 * t ^ (3 / 4 : ℝ) := by
  have hl := Real.log_le_rpow_div ht.le (by norm_num : (0 : ℝ) < 1 / 4)
  rw [Real.sqrt_eq_rpow]
  have hm := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg ht.le (1 / 2))
  have he : t ^ (1 / 2 : ℝ) * (t ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) =
      4 * t ^ (3 / 4 : ℝ) := by
    have hh : t ^ (1 / 2 : ℝ) * t ^ (1 / 4 : ℝ) = t ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      norm_num
    calc
      _ = 4 * (t ^ (1 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) := by ring
      _ = _ := by rw [hh]
  exact hm.trans_eq he

lemma radicalPowerReal_le_threeQuarter {t : ℝ} (ht : 0 < t) :
    Real.rpow t (Real.sqrt t) ≤ Real.exp (4 * t ^ (3 / 4 : ℝ)) := by
  change (t : ℝ) ^ Real.sqrt t ≤ _
  rw [Real.rpow_def_of_pos ht]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using sqrt_mul_log_le_threeQuarter ht

lemma norm_radicalPowerCore_le {m U : ℝ} (hm : 0 < m) (hU : 1 ≤ U)
    {w : ℂ} (hlo : m ≤ ‖w‖) (hhi : ‖w‖ ≤ U) :
    ‖radicalPowerCore w‖ ≤
      Real.exp ((|Real.log m| + Real.pi + 4) * U ^ (3 / 4 : ℝ)) := by
  have hw : 0 < ‖w‖ := hm.trans_le hlo
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hloglo := Real.log_le_log hm hlo
  have hloghi := Real.log_le_log hw hhi
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have habs : |Real.log ‖w‖| ≤ |Real.log m| + Real.log U := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log m), le_abs_self (Real.log m),
      abs_nonneg (Real.log m)]
  have hlogpower : Real.log U ≤ 4 * U ^ (1 / 4 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hUpos.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog : ‖Complex.log w‖ ≤ |Real.log m| + Real.pi + 4 * U ^ (1 / 4 : ℝ) := by
    have hb := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
    rw [Complex.log_re, Complex.log_im] at hb
    linarith [Complex.abs_arg_le_pi w]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hroot : ‖w ^ (1 / 2 : ℂ)‖ ≤ U ^ (1 / 2 : ℝ) := by
    rw [hhalf, Complex.norm_cpow_real]
    exact Real.rpow_le_rpow (norm_nonneg w) hhi (by norm_num)
  have hexp : (w ^ (1 / 2 : ℂ) * Complex.log w).re ≤
      (|Real.log m| + Real.pi + 4) * U ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ ‖w ^ (1 / 2 : ℂ) * Complex.log w‖ := Complex.re_le_norm _
      _ = ‖w ^ (1 / 2 : ℂ)‖ * ‖Complex.log w‖ := norm_mul _ _
      _ ≤ U ^ (1 / 2 : ℝ) * (|Real.log m| + Real.pi + 4 * U ^ (1 / 4 : ℝ)) :=
        mul_le_mul hroot hlog (norm_nonneg _) (Real.rpow_nonneg hUpos.le _)
      _ ≤ (|Real.log m| + Real.pi + 4) * U ^ (3 / 4 : ℝ) := by
        have hp : U ^ (1 / 2 : ℝ) ≤ U ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hU (by norm_num)
        have he : U ^ (1 / 2 : ℝ) * U ^ (1 / 4 : ℝ) = U ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hUpos]
          norm_num
        have hnon : 0 ≤ |Real.log m| + Real.pi := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hp hnon]
  rw [radicalPowerCore, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hexp

lemma one_le_norm_add_one {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖z + 1‖ := by
  have h := Complex.re_le_norm (z + 1)
  simp only [Complex.add_re, Complex.one_re] at h
  linarith

lemma norm_le_norm_add_one {z : ℂ} (hz : 0 ≤ z.re) : ‖z‖ ≤ ‖z + 1‖ := by
  have h1 := Complex.sq_norm z
  have h2 := Complex.sq_norm (z + 1)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, add_zero] at h1 h2
  nlinarith [norm_nonneg z, norm_nonneg (z + 1)]

lemma norm_radicalPowerAnalytic_threeQuarter {m : ℝ} (hm : 0 < m)
    {z : ℂ} (hz : z ∈ rightHalfPlane) :
    ‖radicalPowerAnalytic m z‖ ≤ Real.exp
      (((|Real.log m| + Real.pi + 4) * (1 + m) ^ (3 / 4 : ℝ)) *
        ‖z + 1‖ ^ (3 / 4 : ℝ)) := by
  have hre : 0 ≤ z.re := (show 0 < z.re from hz).le
  have hR := one_le_norm_add_one hre
  have hU : 1 ≤ (1 + m) * ‖z + 1‖ := by nlinarith
  have hlo : m ≤ ‖z + (m : ℂ)‖ := by
    have h := Complex.re_le_norm (z + (m : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at h
    linarith
  have hhi : ‖z + (m : ℂ)‖ ≤ (1 + m) * ‖z + 1‖ := by
    have h := norm_add_le z (m : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at h
    have hn := norm_le_norm_add_one hre
    nlinarith
  have hb := norm_radicalPowerCore_le hm hU hlo hhi
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + m) (norm_nonneg _)] at hb
  simpa [radicalPowerAnalytic, mul_assoc] using hb

end AIM34
