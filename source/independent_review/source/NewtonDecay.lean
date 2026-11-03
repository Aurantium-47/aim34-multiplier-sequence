import NewtonBasis
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- Explicit all-base exponential upper bounds for a real sequence. -/
def SubexponentialUpper (a : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 1 < c → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a n ≤ C * c ^ n

/-- The finite Newton inversion identity, separated from positivity of its coefficients. -/
def NewtonInversion (a d : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, a n = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * d r

lemma descFactorial_mul_lower (K r k : ℕ) (hK : 1 ≤ K) :
    K ^ k * r.descFactorial k ≤ (K * r).descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfac : K * (r - k) ≤ K * r - k := by
      rw [Nat.mul_sub_left_distrib]
      apply Nat.sub_le_sub_left
      simpa using Nat.mul_le_mul_right k hK
    calc
      K ^ (k + 1) * r.descFactorial (k + 1) =
          (K * (r - k)) * (K ^ k * r.descFactorial k) := by
        rw [Nat.descFactorial_succ, pow_succ]; ring
      _ ≤ (K * r - k) * (K * r).descFactorial k := Nat.mul_le_mul hfac ih
      _ = (K * r).descFactorial (k + 1) := rfl

lemma pow_le_choose_mul (K r : ℕ) (hK : 1 ≤ K) :
    K ^ r ≤ (K * r).choose r := by
  have h := descFactorial_mul_lower K r r hK
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose,
    mul_comm r.factorial] at h
  exact (Nat.mul_le_mul_right_iff (Nat.factorial_pos r)).mp h

lemma coefficient_mul_pow_le {a d : ℕ → ℝ} (hd : ∀ r, 0 ≤ d r)
    (hinv : NewtonInversion a d) (K r : ℕ) (hK : 1 ≤ K) :
    d r * (K : ℝ) ^ r ≤ a (K * r) := by
  have hr : r ≤ K * r := by simpa using Nat.mul_le_mul_right r hK
  have hc : (K : ℝ) ^ r ≤ ((K * r).choose r : ℝ) := by
    exact_mod_cast pow_le_choose_mul K r hK
  rw [hinv]
  calc
    _ ≤ ((K * r).choose r : ℝ) * d r := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hc (hd r)
    _ ≤ ∑ j ∈ Finset.range (K * r + 1), ((K * r).choose j : ℝ) * d j :=
      Finset.single_le_sum (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hd j))
        (Finset.mem_range.mpr (by omega))

lemma subexponential_scaled_two {a : ℕ → ℝ} (ha : SubexponentialUpper a)
    {K : ℕ} (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, a (K * r) ≤ C * (2 : ℝ) ^ r := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  let c := Real.exp (Real.log 2 / K)
  have hc : 1 < c := Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos (by norm_num)) hK')
  obtain ⟨C, hC, hbound⟩ := ha c hc
  refine ⟨C, hC, fun r => ?_⟩
  have hpow : c ^ K = 2 := by
    dsimp [c]
    rw [← Real.exp_nat_mul]
    have he : (K : ℝ) * (Real.log 2 / K) = Real.log 2 := by field_simp
    rw [he, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simpa only [pow_mul, hpow] using hbound (K * r)

/-- Nonnegative finite Newton coefficients of a subexponential sequence decay faster
than every fixed geometric rate. The useful summability formulation includes zeros. -/
theorem summable_newton_coefficients_mul_pow {a d : ℕ → ℝ}
    (hd : ∀ r, 0 ≤ d r) (hinv : NewtonInversion a d)
    (ha : SubexponentialUpper a) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun r : ℕ => d r * R ^ r) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (4 * R))
  have hK1 : 1 ≤ K := by exact_mod_cast (le_max_left 1 (4 * R)).trans hK.le
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK1)
  obtain ⟨C, hC, hbound⟩ := subexponential_scaled_two ha (by omega : 0 < K)
  have hratio : 0 ≤ 2 * R / K := by positivity
  have hratio1 : 2 * R / K < 1 := by
    rw [div_lt_one hKpos]
    have h4 : 4 * R < K := (le_max_right 1 (4 * R)).trans_lt hK
    linarith
  apply Summable.of_nonneg_of_le (fun r => mul_nonneg (hd r) (pow_nonneg hR r))
    (f := fun r : ℕ => C * (2 * R / K) ^ r) _
    ((summable_geometric_of_lt_one hratio hratio1).mul_left C)
  intro r
  have hcoeff := (coefficient_mul_pow_le hd hinv K r hK1).trans (hbound r)
  have hdiv : d r ≤ C * (2 : ℝ) ^ r / (K : ℝ) ^ r :=
    (le_div_iff₀ (pow_pos hKpos r)).mpr hcoeff
  calc
    d r * R ^ r ≤ (C * (2 : ℝ) ^ r / (K : ℝ) ^ r) * R ^ r :=
      mul_le_mul_of_nonneg_right hdiv (pow_nonneg hR r)
    _ = C * (2 * R / K) ^ r := by rw [div_pow, mul_pow]; ring

end AIM34
