import JensenPositivity
import SequenceBoundsDraft
import AIMFamilyGrowthDraft
import FiniteDifferenceNewton

noncomputable section
namespace AIM34

lemma allJensen_iteratedDifference (a : ℕ → ℝ) (ha : AllJensenRealRooted a) (r : ℕ) :
    AllJensenRealRooted (iteratedDifference r a) := by
  induction r with
  | zero => simpa [iteratedDifference] using ha
  | succ r ih =>
      rw [show r.succ = r+1 from rfl, iteratedDifference_succ_left]
      exact allJensen_forwardDifference _ ih

/-- The complete sign invariant, with every intermediate sign and support
hypothesis discharged by induction from the actual initial sequence. -/
theorem iteratedDifference_nonneg_of_allJensen (a : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ a n) (hJ : AllJensenRealRooted a)
    (hgrowth : NotPolynomiallyBounded a) :
    ∀ r n : ℕ, 0 ≤ iteratedDifference r a n := by
  intro r
  induction r with
  | zero => simpa [iteratedDifference] using h0
  | succ r ih =>
      have hJr := allJensen_iteratedDifference a hJ r
      apply SequenceBounds.iteratedDifference_succ_nonneg_of_notPolynomiallyBounded
        a r hgrowth ih
      · exact allJensen_logconcave _ hJr
      · intro i j k hij hjk hi hk
        exact allJensen_interval_support _ hJr ih hij hjk hi hk

/-- Actual multiplier preservation for the literal shifted-radical family
would force every forward difference, at every starting index, nonnegative. -/
theorem multiplier_shiftedRadicalPower_all_differences_nonneg {m : ℝ} (hm : 0 < m)
    (h : IsMultiplierSequence (shiftedRadicalPower m)) :
    ∀ r n : ℕ, 0 ≤ iteratedDifference r (shiftedRadicalPower m) n := by
  exact iteratedDifference_nonneg_of_allJensen _
    (fun n => (shiftedRadicalPower_pos hm n).le) (multiplier_allJensen _ h)
    (shiftedRadicalPower_notPolynomiallyBounded hm)

end AIM34
