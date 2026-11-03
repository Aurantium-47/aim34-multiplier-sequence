import RealRootGeometry
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

noncomputable section
open Polynomial
namespace AIM34

def polarLinearSum (s : Multiset ℂ) (z : ℂ) : ℝ :=
  (s.map fun a => (a.re+1) / Complex.normSq (z-a)).sum

def polarSquareSum (s : Multiset ℂ) (z : ℂ) : ℝ :=
  (s.map fun a => (a.re+1)^2 / Complex.normSq (z-a)).sum

lemma polar_factor_im (z a : ℂ) (ha : a.im = 0) :
    ((z+1)*(z-a)⁻¹).im = -z.im * ((a.re+1)/Complex.normSq (z-a)) := by
  simp only [Complex.mul_im, Complex.add_re, Complex.one_re, Complex.add_im,
    Complex.one_im, add_zero, Complex.inv_im, Complex.inv_re, Complex.sub_re,
    Complex.sub_im, ha, sub_zero]
  ring

lemma polar_factor_re {z a : ℂ} (hz : z.im ≠ 0) (ha : a.im = 0) :
    ((z+1)*(z-a)⁻¹).re = 1 + (z.re+1)*((a.re+1)/Complex.normSq (z-a)) -
      (a.re+1)^2/Complex.normSq (z-a) := by
  have hza : z-a ≠ 0 := by
    intro h
    exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
  have hD : Complex.normSq (z-a) ≠ 0 := (Complex.normSq_pos.mpr hza).ne'
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.add_im,
    Complex.one_im, add_zero, Complex.inv_im, Complex.inv_re, Complex.sub_re,
    Complex.sub_im, ha, sub_zero]
  field_simp
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ha, sub_zero]
  ring

lemma rootProduct_polar_log_im (s : Multiset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) :
    ((z+1)*((rootProduct s).derivative.eval z / (rootProduct s).eval z)).im =
      -z.im * polarLinearSum s z := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct, polarLinearSum]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.im = 0 := fun b hb => hs b (by simp [hb])
      have hza : z-a ≠ 0 := by
        intro h; exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
      rw [rootProduct_cons_logDerivative a s hza (rootProduct_nonreal_eval_ne_zero s hz ht),
        mul_add, Complex.add_im, polar_factor_im z a ha, ih ht]
      simp only [polarLinearSum, Multiset.map_cons, Multiset.sum_cons]
      ring

lemma rootProduct_polar_log_re (s : Multiset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) :
    ((z+1)*((rootProduct s).derivative.eval z / (rootProduct s).eval z)).re =
      s.card + (z.re+1)*polarLinearSum s z - polarSquareSum s z := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct, polarLinearSum, polarSquareSum]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.im = 0 := fun b hb => hs b (by simp [hb])
      have hza : z-a ≠ 0 := by
        intro h; exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans ha)
      rw [rootProduct_cons_logDerivative a s hza (rootProduct_nonreal_eval_ne_zero s hz ht),
        mul_add, Complex.add_re, polar_factor_re hz ha, ih ht]
      simp only [polarLinearSum, polarSquareSum, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      ring

lemma polarSquareSum_nonneg (s : Multiset ℂ) (z : ℂ) : 0 ≤ polarSquareSum s z := by
  apply Multiset.sum_nonneg
  intro v hv
  rcases Multiset.mem_map.mp hv with ⟨a, _, rfl⟩
  exact div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

lemma roots_eq_neg_one_of_polarSquareSum_zero (s : Multiset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hs : ∀ a ∈ s, a.im = 0) (hzero : polarSquareSum s z = 0) :
    ∀ a ∈ s, a = -1 := by
  intro a ha
  have hn : ∀ v ∈ (s.map fun a => (a.re+1)^2 / Complex.normSq (z-a)), 0 ≤ v := by
    intro v hv
    rcases Multiset.mem_map.mp hv with ⟨b, _, rfl⟩
    exact div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hv := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hn hzero
    ((a.re+1)^2 / Complex.normSq (z-a)) (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)
  have hza : z-a ≠ 0 := by
    intro h; exact hz ((congrArg Complex.im (sub_eq_zero.mp h)).trans (hs a ha))
  have hD : Complex.normSq (z-a) ≠ 0 := (Complex.normSq_pos.mpr hza).ne'
  have hu : a.re+1 = 0 := sq_eq_zero_iff.mp ((div_eq_zero_iff).mp hv |>.resolve_right hD)
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.one_re]; linarith
  · simp [hs a ha]

def complexPolar (M : ℕ) (p : ℂ[X]) : ℂ[X] :=
  (X+1)*p.derivative - C (M : ℂ)*p

lemma complexPolar_leading_pow_zero (c : ℂ) (M : ℕ) :
    complexPolar M (C c*(X+1)^M) = 0 := by
  cases M with
  | zero => simp [complexPolar]
  | succ n =>
      simp only [complexPolar, derivative_mul, derivative_C, zero_mul, zero_add,
        derivative_pow_succ, derivative_add, derivative_X, derivative_one, add_zero,
        one_mul, mul_one]
      rw [pow_succ]
      ring

/-- The padded-degree polar theorem, allowing the identically zero output. -/
lemma complexPolar_roots_real (M : ℕ) (p : ℂ[X]) (hdeg : p.natDegree ≤ M)
    (hr : ∀ z : ℂ, p.eval z = 0 → z.im = 0) :
    complexPolar M p = 0 ∨ ∀ z : ℂ, (complexPolar M p).eval z = 0 → z.im = 0 := by
  classical
  by_cases hQ : complexPolar M p = 0
  · exact Or.inl hQ
  right
  intro z hz
  by_contra hi
  have hp : p ≠ 0 := by intro he; simp [he, complexPolar] at hQ
  have hpz : p.eval z ≠ 0 := fun he => hi (hr z he)
  have hs : ∀ a ∈ p.roots, a.im = 0 :=
    fun a ha => hr a ((Polynomial.mem_roots hp).mp ha)
  have hratio : (z+1)*(p.derivative.eval z / p.eval z) = (M : ℂ) := by
    simp only [complexPolar, eval_sub, eval_mul, eval_add, eval_X, eval_one, eval_C] at hz
    field_simp
    linear_combination hz
  rw [logDerivative_eq_rootProduct p hp z] at hratio
  have him := rootProduct_polar_log_im p.roots hi hs
  rw [hratio, Complex.natCast_im] at him
  have hU : polarLinearSum p.roots z = 0 := by
    exact (mul_eq_zero.mp him.symm).resolve_left (neg_ne_zero.mpr hi)
  have hre := rootProduct_polar_log_re p.roots hi hs
  rw [hratio, Complex.natCast_re, hU, mul_zero, add_zero] at hre
  have hcard : p.roots.card = p.natDegree := by
    simpa only [Polynomial.map_id] using
      (Polynomial.natDegree_eq_card_roots (i := RingHom.id ℂ)
        (IsAlgClosed.splits_codomain p)).symm
  have hd : (p.roots.card : ℝ) ≤ M := by exact_mod_cast hcard ▸ hdeg
  have hV := polarSquareSum_nonneg p.roots z
  have hV0 : polarSquareSum p.roots z = 0 := by linarith
  have hm : p.roots.card = M := by exact_mod_cast (by linarith : (p.roots.card : ℝ) = M)
  have hsrep := Multiset.eq_replicate_card.mpr
    (roots_eq_neg_one_of_polarSquareSum_zero p.roots hi hs hV0)
  have hf : p = C p.leadingCoeff * (X+1)^M := by
    conv_lhs => rw [eq_leadingCoeff_rootProduct p]
    rw [rootProduct, hsrep, Multiset.map_replicate, Multiset.prod_replicate, hm]
    simp
  exact hQ (hf ▸ complexPolar_leading_pow_zero p.leadingCoeff M)

end AIM34
