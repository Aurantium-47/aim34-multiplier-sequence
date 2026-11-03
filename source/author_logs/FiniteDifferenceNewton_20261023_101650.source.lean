import AIM34Definitions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace AIM34

lemma iteratedDifference_succ_right (r : ℕ) (a : ℕ → ℝ) :
    iteratedDifference (r+1) a = iteratedDifference r (forwardDifference a) :=
  Function.iterate_succ_apply forwardDifference r a

lemma iteratedDifference_succ_left (r : ℕ) (a : ℕ → ℝ) :
    iteratedDifference (r+1) a = forwardDifference (iteratedDifference r a) :=
  Function.iterate_succ_apply' forwardDifference r a

/-- Finite Newton inversion for the actual iterated forward differences.
No positivity, convergence, or analytic hypothesis occurs here. -/
theorem finiteDifference_newton_inversion (a : ℕ → ℝ) (N : ℕ) :
    a N = ∑ r ∈ Finset.range (N+1), (N.choose r : ℝ)*iteratedDifference r a 0 := by
  induction N generalizing a with
  | zero => simp [iteratedDifference]
  | succ N ih =>
      rw [show N.succ+1 = N+2 by omega]
      rw [sum_choose_succ_mul (fun r _ => iteratedDifference r a 0) N]
      simp only [iteratedDifference_succ_right]
      rw [← ih a, ← ih (forwardDifference a)]
      simp [forwardDifference]

end AIM34
