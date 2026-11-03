import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- The polynomial Newton binomial basis, with its ordinary factorial normalization. -/
def newtonBasis (r : ℕ) (z : ℂ) : ℂ := (descPochhammer ℂ r).eval z / (r.factorial : ℂ)

@[simp] lemma newtonBasis_zero (z : ℂ) : newtonBasis 0 z = 1 := by
  simp [newtonBasis]

lemma newtonBasis_succ (r : ℕ) (z : ℂ) :
    newtonBasis (r + 1) z = newtonBasis r z * (z - r) / (r + 1) := by
  simp only [newtonBasis, descPochhammer_eval_eq_prod_range, Finset.prod_range_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp [hf, hr]
  left; ring

@[simp] lemma newtonBasis_natCast (r n : ℕ) : newtonBasis r n = (n.choose r : ℂ) := by
  exact (Nat.cast_choose_eq_descPochhammer_div ℂ n r).symm

lemma differentiable_newtonBasis (r : ℕ) : Differentiable ℂ (newtonBasis r) := by
  exact (descPochhammer ℂ r).differentiable.div_const _

lemma norm_newtonBasis_le_pow {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (r : ℕ) :
    ‖newtonBasis r z‖ ≤ R ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [newtonBasis_succ, norm_div, norm_mul]
    have hd : ‖(r : ℂ) + 1‖ = (r : ℝ) + 1 := by
      rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    rw [hd, div_le_iff₀ (by positivity : (0 : ℝ) < r + 1)]
    have hfac : ‖z - (r : ℂ)‖ ≤ R * ((r : ℝ) + 1) := by
      calc
        _ ≤ ‖z‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
        _ = ‖z‖ + (r : ℝ) := by rw [Complex.norm_natCast]
        _ ≤ R * ((r : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    calc
      _ ≤ R ^ r * (R * ((r : ℝ) + 1)) :=
        mul_le_mul ih hfac (norm_nonneg _) (by positivity)
      _ = R ^ (r + 1) * ((r : ℝ) + 1) := by ring

lemma norm_newtonBasis_le_choose {N r : ℕ} {z : ℂ} (hz : ‖z‖ ≤ N) (hr : r ≤ N) :
    ‖newtonBasis r z‖ ≤ ((3 * N).choose r : ℝ) := by
  rw [newtonBasis, norm_div, Complex.norm_natCast,
    Nat.cast_choose_eq_descPochhammer_div ℝ, descPochhammer_eval_eq_prod_range,
    descPochhammer_eval_eq_prod_range, norm_prod]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.prod_le_prod (fun j hj => norm_nonneg _)
  intro j hj
  have hj' : j < r := Finset.mem_range.mp hj
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (le_of_lt hj').trans hr
  calc
    ‖z - (j : ℂ)‖ ≤ ‖z‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
    _ = ‖z‖ + (j : ℝ) := by rw [Complex.norm_natCast]
    _ ≤ ((3 * N : ℕ) : ℝ) - j := by push_cast; linarith

/-- A deliberately non-sharp universal tail bound, sufficient for the growth bridge. -/
lemma norm_newtonBasis_le_eight_pow {r : ℕ} {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖newtonBasis r z‖ ≤ (8 : ℝ) ^ r := by
  have hb := norm_newtonBasis_le_choose hz (le_refl r)
  have hc : (3 * r).choose r ≤ 2 ^ (3 * r) := by
    rcases r with _ | r
    · norm_num
    · exact (Nat.choose_le_two_pow _ _ (by omega)).le
  have hc' : ((3 * r).choose r : ℝ) ≤ (8 : ℝ) ^ r := by
    have ht : 2 ^ (3 * r) = 8 ^ r := by rw [pow_mul]; norm_num
    exact_mod_cast ht ▸ hc
  exact hb.trans hc'

end AIM34
