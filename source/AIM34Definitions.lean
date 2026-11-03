import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-! Literal actual-preserver target for AIM 2007 Problem 34.
The zero polynomial is allowed, and arbitrary real-rooted input degrees are
quantified. This is not a canonical-product or finite-difference surrogate.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace AIM34

/-- Real-rootedness of a real polynomial, with the zero polynomial allowed. -/
def RealRooted (p : ℝ[X]) : Prop :=
  p = 0 ∨ ∀ z : ℂ, aeval z p = 0 → z.im = 0

/-- The actual coefficientwise diagonal map on every real polynomial. -/
def diagonal (a : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n c => monomial n (a n * c)

def IsMultiplierSequence (a : ℕ → ℝ) : Prop :=
  ∀ p : ℝ[X], RealRooted p → RealRooted (diagonal a p)

/-- The radical is in the exponent. Indices start at zero. -/
def shiftedRadicalPower (m : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n+m) (Real.sqrt (n+m))

def FullProblem34 : Prop :=
  ∀ m : ℝ, 0 < m → ¬ IsMultiplierSequence (shiftedRadicalPower m)

/-- Finite Jensen polynomials; no converse preserver criterion is assumed. -/
def jensen (a : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  diagonal a ((1+X)^N)

def AllJensenRealRooted (a : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, RealRooted (jensen a N)

def forwardDifference (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n+1)-a n

def iteratedDifference (r : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  forwardDifference^[r] a

/-- The growth property needed by the finite Jensen argument. -/
def NotPolynomiallyBounded (a : ℕ → ℝ) : Prop :=
  ∀ (C : ℝ) (r : ℕ), ∃ n : ℕ, C*(n+1)^r < a n

lemma diagonal_coeff (a : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (diagonal a p).coeff n = a n * p.coeff n := by
  classical
  simp only [diagonal, Polynomial.sum_def, finset_sum_coeff, coeff_monomial]
  by_cases hn : n ∈ p.support
  · simp [hn]
  · simp [hn, not_mem_support_iff.mp hn]

lemma one_add_X_pow_realRooted (N : ℕ) : RealRooted ((1+X : ℝ[X])^N) := by
  right
  intro z hz
  have h : (1+z)^N = 0 := by simpa only [map_pow, map_add, map_one, aeval_X] using hz
  have h0 : 1+z = 0 := pow_eq_zero h
  have hi := congrArg Complex.im h0
  simpa using hi

lemma multiplier_allJensen (a : ℕ → ℝ) (ha : IsMultiplierSequence a) :
    AllJensenRealRooted a :=
  fun N => ha _ (one_add_X_pow_realRooted N)

end AIM34
