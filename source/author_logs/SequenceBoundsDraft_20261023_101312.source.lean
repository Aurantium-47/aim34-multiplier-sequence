import AIM34Definitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generic sequence bounds for the AIM34 Jensen sign gate

SOURCE DRAFT ONLY. This file has deliberately not been compiled. It does not
prove the Jensen-to-log-concavity or Jensen-to-interval-support implications.
Those hypotheses remain explicit at the interface below. No theorem about
the actual AIM34 family or a completed-target claim is made here.

The zero-tail argument is essential: adjacent log-concavity alone does not
prevent a positive term from reappearing after two consecutive zeros.
-/

noncomputable section
open scoped BigOperators

namespace AIM34.SequenceBounds

/-- The adjacent log-concavity inequality, without an implicit sign hypothesis. -/
def AdjacentLogConcave (b : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, b n * b (n + 2) ≤ b (n + 1) ^ 2

/-- Positive support is an interval; initial and terminal zero blocks are allowed. -/
def IntervalPositiveSupport (b : ℕ → ℝ) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i ≤ j → j ≤ k → 0 < b i → 0 < b k → 0 < b j

/-- Once a zero occurs after a positive term, interval support makes it permanent.
This also covers the case `j = k`; no strict separation is needed. -/
lemma zero_of_zero_after_pos {b : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ b n) (h_support : IntervalPositiveSupport b)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < b i) (hj : b j = 0) : b k = 0 := by
  apply le_antisymm ?_ (h_nonneg k)
  by_contra h
  have hk : 0 < b k := lt_of_not_ge h
  have hpos : 0 < b j := h_support hij hjk hi hk
  linarith

/-- A strict adjacent drop gives a nonincreasing tail. The zero branch uses
interval support, not an illicit cancellation by a potentially zero term. -/
lemma tail_adjacent_le_of_strict_drop {b : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ b n) (h_log : AdjacentLogConcave b)
    (h_support : IntervalPositiveSupport b) {n : ℕ}
    (h_drop : b (n + 1) < b n) :
    ∀ k : ℕ, b (n + k + 1) ≤ b (n + k) := by
  have hn : 0 < b n := lt_of_le_of_lt (h_nonneg (n + 1)) h_drop
  intro k
  induction k with
  | zero => simpa using h_drop.le
  | succ k ih =>
      have hnext : b (n + k + 2) ≤ b (n + k + 1) := by
        by_cases hz : b (n + k + 1) = 0
        · have hz' : b (n + k + 2) = 0 :=
            zero_of_zero_after_pos h_nonneg h_support
              (by omega : n ≤ n + k + 1)
              (by omega : n + k + 1 ≤ n + k + 2) hn hz
          simp only [hz, hz', le_refl]
        · have hmid : 0 < b (n + k + 1) :=
            lt_of_le_of_ne (h_nonneg _) (Ne.symm hz)
          have hleft : 0 < b (n + k) := lt_of_lt_of_le hmid ih
          have hsquare : b (n + k + 1) ^ 2 ≤
              b (n + k) * b (n + k + 1) := by
            nlinarith [mul_le_mul_of_nonneg_right ih (h_nonneg (n + k + 1))]
          have hproduct := (h_log (n + k)).trans hsquare
          exact (mul_le_mul_left hleft).mp hproduct
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

/-- The finite prefix is the only source of a larger bound than the dropping term. -/
lemma tail_le_of_strict_drop {b : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ b n) (h_log : AdjacentLogConcave b)
    (h_support : IntervalPositiveSupport b) {n : ℕ}
    (h_drop : b (n + 1) < b n) : ∀ k : ℕ, b (n + k) ≤ b n := by
  have hstep := tail_adjacent_le_of_strict_drop h_nonneg h_log h_support h_drop
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : b (n + k + 1) ≤ b n := (hstep k).trans ih
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hk

/-- A nonnegative sequence with interval support and adjacent log-concavity is
globally bounded if it has any strict adjacent drop. Finite support is allowed. -/
theorem bounded_of_strict_drop {b : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ b n) (h_log : AdjacentLogConcave b)
    (h_support : IntervalPositiveSupport b) {n : ℕ}
    (h_drop : b (n + 1) < b n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, b k ≤ B := by
  let B : ℝ := ∑ j ∈ Finset.range (n + 1), b j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => h_nonneg j)
  have hprefix : ∀ k : ℕ, k ≤ n → b k ≤ B := by
    intro k hk
    exact Finset.single_le_sum (fun j _ => h_nonneg j)
      (Finset.mem_range.mpr (by omega))
  refine ⟨B, hB, ?_⟩
  intro k
  by_cases hk : k ≤ n
  · exact hprefix k hk
  · have hn : n ≤ k := by omega
    have htail := tail_le_of_strict_drop h_nonneg h_log h_support h_drop (k - n)
    have hkn : n + (k - n) = k := Nat.add_sub_of_le hn
    rw [hkn] at htail
    exact htail.trans (hprefix n le_rfl)

/-- In particular, the possibly troublesome immediate-zero drop has finite tail. -/
lemma terminal_zero_of_drop_to_zero {b : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ b n) (h_support : IntervalPositiveSupport b)
    {n : ℕ} (hn : 0 < b n) (hz : b (n + 1) = 0) :
    ∀ k : ℕ, n + 1 ≤ k → b k = 0 := by
  intro k hk
  exact zero_of_zero_after_pos h_nonneg h_support (by omega) hk hn hz

/-- Iteration on the initial sequence, useful for induction on the order. -/
lemma iteratedDifference_succ_right (r : ℕ) (a : ℕ → ℝ) :
    iteratedDifference (r + 1) a = iteratedDifference r (forwardDifference a) := by
  exact Function.iterate_succ_apply forwardDifference r a

/-- Iteration on the resulting sequence, useful for the next-sign conclusion. -/
lemma iteratedDifference_succ_left (r : ℕ) (a : ℕ → ℝ) :
    iteratedDifference (r + 1) a = forwardDifference (iteratedDifference r a) := by
  exact Function.iterate_succ_apply' forwardDifference r a

/-- Exact finite telescoping, valid without any sign or growth assumptions. -/
lemma telescope_forwardDifference (a : ℕ → ℝ) (n : ℕ) :
    a n = a 0 + ∑ k ∈ Finset.range n, forwardDifference a k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      simp only [forwardDifference, Nat.succ_eq_add_one]
      ring

/-- One discrete integration increases a polynomial bound's degree by one.
The constant explicitly retains the completely unrestricted initial value.

The proof is the step-by-step absolute-value version of finite telescoping.
It uses `(n+1)^r ≤ (n+2)^r`, rather than any asymptotic infrastructure. -/
lemma abs_polynomial_bound_of_forwardDifference (a : ℕ → ℝ) (r : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (h_bound : ∀ n : ℕ, |forwardDifference a n| ≤ C * (n + 1 : ℝ) ^ r) :
    ∀ n : ℕ, |a n| ≤ (|a 0| + C) * (n + 1 : ℝ) ^ (r + 1) := by
  have hD : 0 ≤ |a 0| + C := add_nonneg (abs_nonneg _) hC
  have hCD : C ≤ |a 0| + C := le_add_of_nonneg_left (abs_nonneg _)
  intro n
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, zero_add, one_pow, mul_one] using
        (le_add_of_nonneg_right hC : |a 0| ≤ |a 0| + C)
  | succ n ih =>
      have hp : (n + 1 : ℝ) ^ r ≤ (n + 1 + 1 : ℝ) ^ r :=
        pow_le_pow_left₀ (by positivity) (by linarith) r
      have ha : a (n + 1) = a n + forwardDifference a n := by
        simp only [forwardDifference]
        ring
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      calc
        |a (n + 1)| = |a n + forwardDifference a n| := congrArg abs ha
        _ ≤ |a n| + |forwardDifference a n| := abs_add _ _
        _ ≤ (|a 0| + C) * (n + 1 : ℝ) ^ (r + 1) +
            C * (n + 1 : ℝ) ^ r := add_le_add ih (h_bound n)
        _ ≤ (|a 0| + C) * (n + 1 : ℝ) ^ (r + 1) +
            (|a 0| + C) * (n + 1 : ℝ) ^ r :=
          add_le_add_left (mul_le_mul_of_nonneg_right hCD (by positivity)) _
        _ = ((|a 0| + C) * (n + 1 : ℝ) ^ r) * (n + 1 + 1 : ℝ) := by
          rw [pow_succ]
          ring
        _ ≤ ((|a 0| + C) * (n + 1 + 1 : ℝ) ^ r) * (n + 1 + 1 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD) (by positivity)
        _ = (|a 0| + C) * (n + 1 + 1 : ℝ) ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- A bounded `r`-th difference bounds the original sequence in absolute value
by a degree-`r` polynomial. No lower difference is assumed nonnegative.

All finitely many initial differences are absorbed recursively into `C`;
there is no omitted vanishing-initial-data hypothesis. -/
theorem abs_polynomial_bound_of_bounded_iteratedDifference
    (r : ℕ) (a : ℕ → ℝ) (B : ℝ)
    (h_bound : ∀ n : ℕ, |iteratedDifference r a n| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |a n| ≤ C * (n + 1 : ℝ) ^ r := by
  induction r generalizing a with
  | zero =>
      have hB : 0 ≤ B := (abs_nonneg _).trans (h_bound 0)
      refine ⟨B, hB, ?_⟩
      intro n
      simpa only [iteratedDifference, Function.iterate_zero_apply, pow_zero, mul_one]
        using h_bound n
  | succ r ih =>
      have h_delta : ∀ n : ℕ, |iteratedDifference r (forwardDifference a) n| ≤ B := by
        intro n
        simpa only [Nat.succ_eq_add_one, iteratedDifference_succ_right] using h_bound n
      obtain ⟨C, hC, hC_bound⟩ := ih (forwardDifference a) h_delta
      refine ⟨|a 0| + C, add_nonneg (abs_nonneg _) hC, ?_⟩
      simpa only [Nat.succ_eq_add_one] using
        abs_polynomial_bound_of_forwardDifference a r C hC hC_bound

/-- The one-sided bound needed to contradict `NotPolynomiallyBounded`. -/
theorem polynomial_upper_bound_of_bounded_iteratedDifference
    (r : ℕ) (a : ℕ → ℝ) (B : ℝ)
    (h_bound : ∀ n : ℕ, |iteratedDifference r a n| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, a n ≤ C * (n + 1 : ℝ) ^ r := by
  obtain ⟨C, hC, h_abs⟩ :=
    abs_polynomial_bound_of_bounded_iteratedDifference r a B h_bound
  exact ⟨C, hC, fun n => (le_abs_self _).trans (h_abs n)⟩

/-- The generic sign gate: the `r`-th difference is nondecreasing provided
that particular difference is nonnegative, log-concave, and gap-free.
There is deliberately no automatic sign assumption on arbitrary differences. -/
theorem iteratedDifference_monotone_of_notPolynomiallyBounded
    (a : ℕ → ℝ) (r : ℕ) (h_growth : NotPolynomiallyBounded a)
    (h_nonneg : ∀ n, 0 ≤ iteratedDifference r a n)
    (h_log : AdjacentLogConcave (iteratedDifference r a))
    (h_support : IntervalPositiveSupport (iteratedDifference r a)) :
    Monotone (iteratedDifference r a) := by
  apply monotone_nat_of_le_succ
  intro n
  by_contra h
  have h_drop : iteratedDifference r a (n + 1) < iteratedDifference r a n :=
    lt_of_not_ge h
  obtain ⟨B, _hB, h_bound⟩ :=
    bounded_of_strict_drop h_nonneg h_log h_support h_drop
  have h_abs : ∀ k : ℕ, |iteratedDifference r a k| ≤ B := by
    intro k
    rw [abs_of_nonneg (h_nonneg k)]
    exact h_bound k
  obtain ⟨C, _hC, h_poly⟩ :=
    polynomial_upper_bound_of_bounded_iteratedDifference r a B h_abs
  obtain ⟨k, hk⟩ := h_growth C r
  exact (not_lt_of_ge (h_poly k)) hk

/-- Explicit next-order nonnegativity, for use in the Jensen invariant induction. -/
theorem iteratedDifference_succ_nonneg_of_notPolynomiallyBounded
    (a : ℕ → ℝ) (r : ℕ) (h_growth : NotPolynomiallyBounded a)
    (h_nonneg : ∀ n, 0 ≤ iteratedDifference r a n)
    (h_log : AdjacentLogConcave (iteratedDifference r a))
    (h_support : IntervalPositiveSupport (iteratedDifference r a)) :
    ∀ n : ℕ, 0 ≤ iteratedDifference (r + 1) a n := by
  have hmono := iteratedDifference_monotone_of_notPolynomiallyBounded
    a r h_growth h_nonneg h_log h_support
  intro n
  rw [iteratedDifference_succ_left]
  exact sub_nonneg.mpr (hmono (Nat.le_succ n))

end AIM34.SequenceBounds
