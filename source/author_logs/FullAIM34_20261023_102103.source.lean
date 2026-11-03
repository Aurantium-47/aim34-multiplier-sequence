import ForwardDifferenceSign
import RadicalInterpolationObstruction

/-! Full negative answer to AIM 2007 Problem 34, with the actual coefficient
preserver semantics. The theorem covers every positive real shift and both
indexing conventions appearing in the original sources. No Pólya–Schur
classification, Carlson theorem, or undisclosed interpolation assumption is used.
-/
noncomputable section
namespace AIM34

/-- For every positive real m, the literal sequence (n+m)^(sqrt(n+m)) is not a
classical real-rootedness-preserving coefficient multiplier sequence. -/
theorem not_multiplier_shiftedRadicalPower (m : ℝ) (hm : 0 < m) :
    ¬ IsMultiplierSequence (shiftedRadicalPower m) := by
  intro hmult
  let a := shiftedRadicalPower m
  let d := fun r => iteratedDifference r a 0
  have hd : ∀ r, 0 ≤ d r :=
    fun r => multiplier_shiftedRadicalPower_all_differences_nonneg hm hmult r 0
  have hinv : NewtonInversion a d := fun N => finiteDifference_newton_inversion a N
  have hsub : SubexponentialUpper a := shiftedRadicalPower_subexponential hm
  obtain ⟨H, hH, hn, C, hC, hb⟩ := entire_newton_interpolation_and_growth hd hinv hsub
  exact no_entire_radicalPower_interpolant hm hC hH hn hb

/-- The negative preserver result supplies an actual finite real polynomial
counterexample for each positive real shift, without a uniform degree claim. -/
theorem exists_counterexample_polynomial (m : ℝ) (hm : 0 < m) :
    ∃ p : Polynomial ℝ, RealRooted p ∧
      ¬ RealRooted (diagonal (shiftedRadicalPower m) p) := by
  classical
  obtain ⟨p, hp⟩ := not_forall.mp (not_multiplier_shiftedRadicalPower m hm)
  exact ⟨p, not_imp.mp hp⟩

theorem fullProblem34 : FullProblem34 := not_multiplier_shiftedRadicalPower

/-- The positive integer, zero-indexed convention used in Chasse's restatement. -/
theorem problem34_positive_integer_shift (m : ℕ) (hm : 0 < m) :
    ¬ IsMultiplierSequence (fun n : ℕ =>
      Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))) :=
  not_multiplier_shiftedRadicalPower m (by exact_mod_cast hm)

/-- The displayed AIM sequence begins at k=1; reindexing it from n=0 gives
n+1+m. This corollary therefore covers every original positive integer shift,
and in fact every nonnegative integer shift in this indexing convention. -/
theorem problem34_one_indexed_shift (m : ℕ) :
    ¬ IsMultiplierSequence (fun n : ℕ =>
      Real.rpow ((n : ℝ)+1+m) (Real.sqrt ((n : ℝ)+1+m))) := by
  simpa only [shiftedRadicalPower, add_assoc, add_comm (m : ℝ) 1] using
    not_multiplier_shiftedRadicalPower ((m : ℝ)+1) (by positivity)

end AIM34
