import NewtonDecay

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- The actual infinite Newton series. -/
def newtonInterpolant (d : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' r : ℕ, (d r : ℂ) * newtonBasis r z

lemma norm_newtonTerm_le {d : ℕ → ℝ} (hd : ∀ r, 0 ≤ d r) {R : ℝ}
    (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (r : ℕ) :
    ‖(d r : ℂ) * newtonBasis r z‖ ≤ d r * R ^ r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd r)]
  exact mul_le_mul_of_nonneg_left (norm_newtonBasis_le_pow hR hz r) (hd r)

lemma summable_newtonTerms {a d : ℕ → ℝ}
    (hd : ∀ r, 0 ≤ d r) (hinv : NewtonInversion a d)
    (ha : SubexponentialUpper a) (z : ℂ) :
    Summable (fun r : ℕ => (d r : ℂ) * newtonBasis r z) := by
  let R := max 1 ‖z‖
  exact Summable.of_norm_bounded (fun r => d r * R ^ r)
    (summable_newton_coefficients_mul_pow hd hinv ha (by dsimp [R]; positivity))
    (norm_newtonTerm_le hd (le_max_left _ _) (le_max_right _ _))

/-- Entire convergence is proved from nonnegative Newton inversion and subexponential
sequence bounds, rather than assumed as an interpolation interface. -/
theorem differentiable_newtonInterpolant {a d : ℕ → ℝ}
    (hd : ∀ r, 0 ≤ d r) (hinv : NewtonInversion a d)
    (ha : SubexponentialUpper a) : Differentiable ℂ (newtonInterpolant d) := by
  intro z
  let R := max 1 (‖z‖ + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hsum := summable_newton_coefficients_mul_pow hd hinv ha (zero_le_one.trans hR)
  have hdiff : DifferentiableOn ℂ (newtonInterpolant d) (ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
    · intro r
      exact ((differentiable_const _).mul (differentiable_newtonBasis r)).differentiableOn
    · exact isOpen_ball
    · intro r w hw
      exact norm_newtonTerm_le hd hR (mem_ball_zero_iff.mp hw).le r
  apply hdiff.differentiableAt
  apply isOpen_ball.mem_nhds
  rw [mem_ball_zero_iff]
  exact lt_of_lt_of_le (by linarith : ‖z‖ < ‖z‖ + 1) (le_max_right _ _)

/-- Exact interpolation at all nonnegative integers, using termination of the series. -/
theorem newtonInterpolant_natCast {a d : ℕ → ℝ} (hinv : NewtonInversion a d) (n : ℕ) :
    newtonInterpolant d n = (a n : ℂ) := by
  rw [newtonInterpolant, tsum_eq_sum (s := Finset.range (n + 1))]
  · rw [hinv n]
    push_cast
    apply Finset.sum_congr rfl
    intro r hr
    rw [newtonBasis_natCast]
    ring
  · intro r hr
    have hnr : n < r := by simpa only [Finset.mem_range, not_lt] using hr
    simp [newtonBasis_natCast, Nat.choose_eq_zero_of_lt hnr]

lemma hasSum_choose_newton {a d : ℕ → ℝ} (hinv : NewtonInversion a d) (n : ℕ) :
    HasSum (fun r : ℕ => (n.choose r : ℝ) * d r) (a n) := by
  rw [hinv n]
  apply hasSum_sum_of_ne_finset_zero
  intro r hr
  have hnr : n < r := by simpa only [Finset.mem_range, not_lt] using hr
  simp [Nat.choose_eq_zero_of_lt hnr]

/-- The entire interpolant inherits the original sequence's sharp radial growth up to
one universal finite constant. `8` is a harmless non-sharp tail base. -/
theorem norm_newtonInterpolant_le {a d : ℕ → ℝ}
    (hd : ∀ r, 0 ≤ d r) (hinv : NewtonInversion a d)
    (ha : SubexponentialUpper a) {N : ℕ} {z : ℂ} (hz : ‖z‖ ≤ N) :
    ‖newtonInterpolant d z‖ ≤ a (3 * N) + ∑' r : ℕ, d r * (8 : ℝ) ^ r := by
  have htail := summable_newton_coefficients_mul_pow hd hinv ha (by norm_num : (0 : ℝ) ≤ 8)
  apply tsum_of_norm_bounded ((hasSum_choose_newton hinv (3 * N)).add htail.hasSum)
  intro r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd r)]
  by_cases hr : r ≤ N
  · have hlow := mul_le_mul_of_nonneg_left (norm_newtonBasis_le_choose hz hr) (hd r)
    have ht : 0 ≤ d r * (8 : ℝ) ^ r := mul_nonneg (hd r) (by positivity)
    nlinarith
  · have hNr : (N : ℝ) ≤ r := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hr))
    have hhigh := mul_le_mul_of_nonneg_left (norm_newtonBasis_le_eight_pow (hz.trans hNr)) (hd r)
    have hl : 0 ≤ ((3 * N).choose r : ℝ) * d r := mul_nonneg (Nat.cast_nonneg _) (hd r)
    linarith

/-- All analytic conclusions of the generic Newton construction, with no entire/growth
bridge hidden among the hypotheses. -/
theorem entire_newton_interpolation_and_growth {a d : ℕ → ℝ}
    (hd : ∀ r, 0 ≤ d r) (hinv : NewtonInversion a d)
    (ha : SubexponentialUpper a) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ n : ℕ, H n = (a n : ℂ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ N → ‖H z‖ ≤ a (3 * N) + C := by
  refine ⟨newtonInterpolant d, differentiable_newtonInterpolant hd hinv ha,
    newtonInterpolant_natCast hinv, ∑' r : ℕ, d r * (8 : ℝ) ^ r, ?_, ?_⟩
  · exact tsum_nonneg (fun r => mul_nonneg (hd r) (by positivity))
  · intro N z hz
    exact norm_newtonInterpolant_le hd hinv ha hz

end AIM34
