import AIM34Definitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The five root-product logarithmic derivative lemmas below are reused from
independently accepted CGV Bell source BellRoots.lean, frozen 2026-10-23.
Only the namespace and generic imports change; no Bell assumptions are imported.
-/
noncomputable section
open Polynomial
namespace AIM34

def rootProduct (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun a => X - C a).prod

lemma rootProduct_nonreal_eval_ne_zero (s : Multiset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) :
    (rootProduct s).eval z ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have hn : z - a ≠ 0 := by
        intro h
        exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
      have ht := ih (fun b hb => hs b (by simp [hb]))
      simpa [rootProduct] using mul_ne_zero hn ht

lemma im_mul_inv_sub_neg {z a : ℂ} (hz : z.im ≠ 0) (ha : a.im = 0) :
    z.im * ((z - a)⁻¹).im < 0 := by
  have hn : z - a ≠ 0 := by
    intro h
    exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
  rw [Complex.inv_im, Complex.sub_im, ha, sub_zero, ← mul_div_assoc]
  exact div_neg_of_neg_of_pos (by nlinarith [mul_self_pos.mpr hz])
    (Complex.normSq_pos.mpr hn)

lemma rootProduct_cons_logDerivative (a : ℂ) (s : Multiset ℂ) {z : ℂ}
    (hza : z - a ≠ 0) (hq : (rootProduct s).eval z ≠ 0) :
    (rootProduct (a ::ₘ s)).derivative.eval z /
        (rootProduct (a ::ₘ s)).eval z =
      (z - a)⁻¹ + (rootProduct s).derivative.eval z / (rootProduct s).eval z := by
  have hf : rootProduct (a ::ₘ s) = (X - C a) * rootProduct s := by
    simp [rootProduct]
  rw [hf]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, eval_one, one_mul, eval_sub, eval_X, eval_C]
  field_simp [hza, hq]
  <;> ring

lemma rootProduct_logDerivative_im_mul_nonpos (s : Multiset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) :
    z.im * ((rootProduct s).derivative.eval z / (rootProduct s).eval z).im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.im = 0 := fun b hb => hs b (by simp [hb])
      have hq := rootProduct_nonreal_eval_ne_zero s hz ht
      have hza : z - a ≠ 0 := by
        intro h
        exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
      rw [rootProduct_cons_logDerivative a s hza hq, Complex.add_im, mul_add]
      exact add_nonpos (im_mul_inv_sub_neg hz ha).le (ih ht)

lemma rootProduct_logDerivative_im_mul_neg (s : Multiset ℂ) (hne : s ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) :
    z.im * ((rootProduct s).derivative.eval z / (rootProduct s).eval z).im < 0 := by
  induction s using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.im = 0 := fun b hb => hs b (by simp [hb])
      have hq := rootProduct_nonreal_eval_ne_zero s hz ht
      have hza : z - a ≠ 0 := by
        intro h
        exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
      rw [rootProduct_cons_logDerivative a s hza hq, Complex.add_im, mul_add]
      exact add_neg_of_neg_of_nonpos (im_mul_inv_sub_neg hz ha)
        (rootProduct_logDerivative_im_mul_nonpos s hz ht)


lemma eq_leadingCoeff_rootProduct (p : ℂ[X]) :
    p = C p.leadingCoeff * rootProduct p.roots :=
  Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits_codomain p)

lemma logDerivative_eq_rootProduct (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    p.derivative.eval z / p.eval z =
      (rootProduct p.roots).derivative.eval z / (rootProduct p.roots).eval z := by
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  conv_lhs => rw [eq_leadingCoeff_rootProduct p]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  exact mul_div_mul_left _ _ hc

lemma complex_derivative_roots_real (p : ℂ[X])
    (hr : ∀ z : ℂ, p.eval z = 0 → z.im = 0) :
    p.derivative = 0 ∨ ∀ z : ℂ, p.derivative.eval z = 0 → z.im = 0 := by
  classical
  by_cases hd : p.derivative = 0
  · exact Or.inl hd
  right
  intro z hz
  by_contra hi
  have hp : p ≠ 0 := by intro h; simp [h] at hd
  have hs : ∀ a ∈ p.roots, a.im = 0 :=
    fun a ha => hr a ((Polynomial.mem_roots hp).mp ha)
  have hne : p.roots ≠ 0 := by
    intro he
    have hf := eq_leadingCoeff_rootProduct p
    simp only [he, rootProduct, Multiset.map_zero, Multiset.prod_zero, mul_one] at hf
    exact hd (hf ▸ derivative_C _)
  have hneg := rootProduct_logDerivative_im_mul_neg p.roots hne hi hs
  rw [← logDerivative_eq_rootProduct p hp z, hz] at hneg
  simpa using hneg

lemma realRooted_derivative (p : ℝ[X]) (hr : RealRooted p) : RealRooted p.derivative := by
  rcases hr with hp | hr
  · left; simp [hp]
  have hc : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 := by
    simpa only [eval_map, ← aeval_def] using hr
  rcases complex_derivative_roots_real _ hc with hz | hz
  · left
    rw [← map_derivative] at hz
    exact (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp hz
  · right
    simpa only [← map_derivative, eval_map, ← aeval_def] using hz

end AIM34
