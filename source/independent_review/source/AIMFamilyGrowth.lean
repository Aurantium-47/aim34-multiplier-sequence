import AIM34Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Growth bounds for the exact AIM family, prepared source-only and subsequently
kernel-checked against mathlib commit c44e0c8 with Lean 4.19.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace AIM34

/-- Every term of the exact shifted-radical family is strictly positive. -/
lemma shiftedRadicalPower_pos {m : ℝ} (hm : 0 < m) (n : ℕ) :
    0 < shiftedRadicalPower m n := by
  unfold shiftedRadicalPower
  apply Real.rpow_pos_of_pos
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hm

/-- An explicit elementary threshold, without asymptotic estimates.
The square threshold also implies `1 ≤ n`, so `n + 1 ≤ 2 * n`.
-/
lemma shiftedRadicalPower_gt_polynomial_of_bounds {m C : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C) (r n : ℕ)
    (hn_square : ((r : ℝ) + 1) ^ 2 ≤ (n : ℝ))
    (hn_C : (2 : ℝ) ^ r * C < (n : ℝ)) :
    C * ((n : ℝ) + 1) ^ r < shiftedRadicalPower m n := by
  have hn_one : (1 : ℝ) ≤ n := by
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn_one
  have hbase : (1 : ℝ) ≤ (n : ℝ) + m := by linarith
  have hsqrt : (r : ℝ) + 1 ≤ Real.sqrt ((n : ℝ) + m) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hexp : ((r + 1 : ℕ) : ℝ) ≤ Real.sqrt ((n : ℝ) + m) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsqrt
  have hpower : ((n : ℝ) + m) ^ (r + 1) ≤ shiftedRadicalPower m n := by
    simpa only [shiftedRadicalPower, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hbase hexp)
  calc
    C * ((n : ℝ) + 1) ^ r ≤ C * (2 * (n : ℝ)) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = ((2 : ℝ) ^ r * C) * (n : ℝ) ^ r := by
      rw [mul_pow]
      ring
    _ < (n : ℝ) * (n : ℝ) ^ r :=
      mul_lt_mul_of_pos_right hn_C (pow_pos hn_pos r)
    _ = (n : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
    _ ≤ ((n : ℝ) + m) ^ (r + 1) :=
      pow_le_pow_left₀ hn_pos.le (by linarith) (r + 1)
    _ ≤ shiftedRadicalPower m n := hpower

/-- This quantifies over every real `C`, not just positive constants. -/
lemma shiftedRadicalPower_notPolynomiallyBounded {m : ℝ} (hm : 0 < m) :
    NotPolynomiallyBounded (shiftedRadicalPower m) := by
  intro C r
  by_cases hC : 0 ≤ C
  · obtain ⟨n, hn⟩ := exists_nat_gt
      (max (((r : ℝ) + 1) ^ 2) ((2 : ℝ) ^ r * C))
    refine ⟨n, shiftedRadicalPower_gt_polynomial_of_bounds hm hC r n ?_ ?_⟩
    · exact le_trans (le_max_left _ _) hn.le
    · exact lt_of_le_of_lt (le_max_right _ _) hn
  · refine ⟨0, ?_⟩
    have hneg : C < 0 := lt_of_not_ge hC
    simpa using (lt_trans hneg (shiftedRadicalPower_pos hm 0))

/-- The log-times-square-root exponent is eventually bounded by any positive
linear slope. The threshold is a real number and no assertion at small or
negative arguments is needed.
-/
lemma eventually_log_mul_sqrt_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x * Real.sqrt x ≤ ε * x := by
  have hsmall :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound hε
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx_nonneg
  have hlog : Real.log x ≤ ε * Real.sqrt x := by
    calc
      Real.log x ≤ ‖Real.log x‖ := Real.le_norm_self _
      _ ≤ ε * ‖Real.rpow x (1 / 2 : ℝ)‖ := hx
      _ = ε * Real.sqrt x := by
        rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  calc
    Real.log x * Real.sqrt x ≤ (ε * Real.sqrt x) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg x)
    _ = ε * x := by rw [mul_assoc, Real.mul_self_sqrt hx_nonneg]

/-- A tail estimate with a fully explicit multiplicative constant.
Only the starting index depends on the asymptotic logarithm theorem.
-/
lemma shiftedRadicalPower_eventually_le_geometric {m c : ℝ}
    (hm : 0 < m) (hc : 1 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      shiftedRadicalPower m n ≤ Real.exp (Real.log c * m) * c ^ n := by
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    (eventually_log_mul_sqrt_le (Real.log_pos hc))
  obtain ⟨N, hN⟩ := exists_nat_gt b
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) + m :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hm
  have hbound := hb ((n : ℝ) + m) (by linarith)
  calc
    shiftedRadicalPower m n =
        Real.exp (Real.log ((n : ℝ) + m) * Real.sqrt ((n : ℝ) + m)) := by
      exact Real.rpow_def_of_pos hx _
    _ ≤ Real.exp (Real.log c * ((n : ℝ) + m)) := Real.exp_le_exp.mpr hbound
    _ = Real.exp (Real.log c * m) * c ^ n := by
      rw [show Real.log c * ((n : ℝ) + m) =
        Real.log c * m + (n : ℝ) * Real.log c by ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hc_pos]

/-- The exact AIM family is bounded by a positive multiple of every geometric
sequence with real base strictly greater than one. The finite prefix is
included, so this is an all-indices bound rather than an eventual statement.
-/
lemma shiftedRadicalPower_subexponential {m : ℝ} (hm : 0 < m) :
    ∀ c : ℝ, 1 < c → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, shiftedRadicalPower m n ≤ C * c ^ n := by
  intro c hc
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨N, hN⟩ := shiftedRadicalPower_eventually_le_geometric hm hc
  let S : ℝ := ∑ k ∈ Finset.range N, shiftedRadicalPower m k / c ^ k
  have hS_nonneg : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (shiftedRadicalPower_pos hm k).le (pow_pos hc_pos k).le
  let C : ℝ := Real.exp (Real.log c * m) + S
  have hC_pos : 0 < C :=
    add_pos_of_pos_of_nonneg (Real.exp_pos _) hS_nonneg
  refine ⟨C, hC_pos, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · calc
      shiftedRadicalPower m n ≤ Real.exp (Real.log c * m) * c ^ n := hN n hn
      _ ≤ C * c ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_pos hc_pos n).le
        dsimp [C]
        linarith
  · have hn_mem : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hterm : shiftedRadicalPower m n / c ^ n ≤ S := by
      dsimp only [S]
      apply Finset.single_le_sum (s := Finset.range N) (a := n)
      · intro k hk
        exact div_nonneg (shiftedRadicalPower_pos hm k).le (pow_pos hc_pos k).le
      · exact hn_mem
    have hratio : shiftedRadicalPower m n / c ^ n ≤ C := by
      dsimp [C]
      linarith [Real.exp_pos (Real.log c * m)]
    exact (div_le_iff₀ (pow_pos hc_pos n)).mp hratio

end AIM34
