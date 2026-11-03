import IntegerZeroUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- Positive angular loss for the principal three-quarter power on a half-plane. -/
def threeQuarterCos : ℝ := Real.cos (3 * Real.pi / 8)

lemma threeQuarterCos_pos : 0 < threeQuarterCos := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

lemma re_cpow_threeQuarter_lower {w : ℂ} (hw : 0 ≤ w.re) :
    threeQuarterCos * ‖w‖ ^ (3 / 4 : ℝ) ≤ (w ^ (3 / 4 : ℂ)).re := by
  have ha : |w.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hw
  have hb : |w.arg * (3 / 4 : ℝ)| ≤ 3 * Real.pi / 8 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    nlinarith
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (w.arg * (3 / 4 : ℝ)))
    (show 3 * Real.pi / 8 ≤ Real.pi by linarith [Real.pi_pos]) hb
  rw [Real.cos_abs] at hc
  have he : (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, Complex.cpow_ofReal_re]
  simpa [threeQuarterCos, mul_comm] using
    mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (norm_nonneg w) (3 / 4))

lemma add_one_mem_slitPlane {z : ℂ} (hz : z ∈ rightHalfPlane) : z + 1 ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  change 0 < z.re at hz
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- The concrete damping factor. Its exponent and the angular loss are fully instantiated. -/
def threeQuarterDamping (A : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(A / threeQuarterCos : ℝ) * (z + 1) ^ (3 / 4 : ℂ))

lemma differentiableOn_threeQuarterDamping (A : ℝ) :
    DifferentiableOn ℂ (threeQuarterDamping A) rightHalfPlane := by
  have hp : DifferentiableOn ℂ (fun z : ℂ => (z + 1) ^ (3 / 4 : ℂ)) rightHalfPlane :=
    (differentiableOn_id.add_const 1).cpow_const (fun z hz => add_one_mem_slitPlane hz)
  exact ((differentiableOn_const _).mul hp).cexp

lemma norm_mul_threeQuarterDamping_le {f : ℂ → ℂ} {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hb : ∀ z ∈ rightHalfPlane,
      ‖f z‖ ≤ C * Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ)))
    {z : ℂ} (hz : z ∈ rightHalfPlane) :
    ‖f z * threeQuarterDamping A z‖ ≤ C := by
  have hw : 0 ≤ (z + 1).re := by
    change 0 < z.re at hz
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hlower := re_cpow_threeQuarter_lower hw
  have hD : 0 ≤ A / threeQuarterCos := div_nonneg hA threeQuarterCos_pos.le
  have hexp : A * ‖z + 1‖ ^ (3 / 4 : ℝ) -
      (A / threeQuarterCos) * ((z + 1) ^ (3 / 4 : ℂ)).re ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hlower hD
    have he : A / threeQuarterCos * (threeQuarterCos * ‖z + 1‖ ^ (3 / 4 : ℝ)) =
        A * ‖z + 1‖ ^ (3 / 4 : ℝ) := by
      field_simp [threeQuarterCos_pos.ne']
      ring
    rw [he] at hmul
    linarith
  rw [norm_mul, threeQuarterDamping, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  calc
    _ ≤ (C * Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ))) *
        Real.exp (-(A / threeQuarterCos) * ((z + 1) ^ (3 / 4 : ℂ)).re) :=
      mul_le_mul_of_nonneg_right (hb z hz) (Real.exp_nonneg _)
    _ = C * Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ) -
        (A / threeQuarterCos) * ((z + 1) ^ (3 / 4 : ℂ)).re) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hexp) hC
    _ = C := mul_one _

/-- Half-plane uniqueness for a concrete order-three-quarter growth bound, proved by
explicit damping and the bounded integer-zero theorem. -/
theorem eq_zero_of_rightHalfPlane_threeQuarter_growth {f : ℂ → ℂ} {A C : ℝ}
    (hf : DifferentiableOn ℂ f rightHalfPlane) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hb : ∀ z ∈ rightHalfPlane,
      ‖f z‖ ≤ C * Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ)))
    (hz : ∀ n : ℕ, 0 < n → f n = 0) : EqOn f 0 rightHalfPlane := by
  have hg : EqOn (fun z => f z * threeQuarterDamping A z) 0 rightHalfPlane :=
    eq_zero_of_bounded_rightHalfPlane_integer_zeros
      (hf.mul (differentiableOn_threeQuarterDamping A))
      (fun z hz => norm_mul_threeQuarterDamping_le hA hC hb hz)
      (fun n hn => by rw [hz n hn, zero_mul])
  intro z hz
  exact (mul_eq_zero.mp (hg hz)).resolve_right (Complex.exp_ne_zero _)

end AIM34
