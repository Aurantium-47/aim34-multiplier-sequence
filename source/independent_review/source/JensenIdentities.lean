import AIM34Definitions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial
open scoped BigOperators
namespace AIM34

lemma jensen_coeff (a : ℕ → ℝ) (N j : ℕ) :
    (jensen a N).coeff j = a j * (N.choose j : ℝ) := by
  rw [jensen, diagonal_coeff, coeff_one_add_X_pow]

lemma jensen_natDegree_le (a : ℕ → ℝ) (N : ℕ) :
    (jensen a N).natDegree ≤ N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp [jensen_coeff, Nat.choose_eq_zero_of_lt hj]

lemma jensen_derivative (a : ℕ → ℝ) (N : ℕ) :
    (jensen a (N+1)).derivative = C (N+1 : ℝ) * jensen (fun n => a (n+1)) N := by
  ext n
  simp only [coeff_derivative, jensen_coeff, coeff_C_mul]
  have hc : (N+1 : ℝ) * (N.choose n : ℝ) =
      ((N+1).choose (n+1) : ℝ) * (n+1) := by
    exact_mod_cast Nat.succ_mul_choose_eq N n
  linear_combination a (n+1) * hc.symm

/-- Exact padded-degree polar identity, including all index and zero cases. -/
lemma jensen_forwardDifference (a : ℕ → ℝ) (N : ℕ) :
    C (N+1 : ℝ) * jensen (forwardDifference a) N =
      (1+X) * (jensen a (N+1)).derivative - C (N+1 : ℝ) * jensen a (N+1) := by
  ext n
  cases n with
  | zero =>
      simp [jensen_coeff, forwardDifference, add_mul, coeff_derivative]
      <;> ring
  | succ n =>
      simp only [coeff_C_mul, jensen_coeff, forwardDifference, add_mul, one_mul,
        coeff_sub, coeff_add, coeff_X_mul, coeff_derivative, Nat.succ_eq_add_one]
      have hA : (N+1 : ℝ) * (N.choose (n+1) : ℝ) =
          ((N+1).choose (n+1+1) : ℝ) * (n+1+1) := by
        exact_mod_cast Nat.succ_mul_choose_eq N (n+1)
      have hB : (N+1 : ℝ) * (N.choose n : ℝ) =
          ((N+1).choose (n+1) : ℝ) * (n+1) := by
        exact_mod_cast Nat.succ_mul_choose_eq N n
      have hC : ((N+1).choose (n+1) : ℝ) = (N.choose n : ℝ) + (N.choose (n+1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ N n
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination a (n+1+1) * hA + a (n+1) * hB +
        (N+1) * a (n+1) * hC

end AIM34
