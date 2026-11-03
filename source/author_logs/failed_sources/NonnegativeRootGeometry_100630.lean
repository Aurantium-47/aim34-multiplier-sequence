import JensenRootClosure

noncomputable section
open Polynomial
namespace AIM34

lemma re_inv_pos {z : ℂ} (hz : 0 < z.re) : 0 < z⁻¹.re := by
  have hn : z ≠ 0 := by intro h; simpa [h] using hz
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr hn)

lemma rootProduct_eval_ne_zero_of_re_lt (s : Multiset ℂ) (z : ℂ)
    (hs : ∀ a ∈ s, a.re < z.re) : (rootProduct s).eval z ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have hza : z-a ≠ 0 := by
        intro h
        have he := congrArg Complex.re (sub_eq_zero.mp h)
        linarith
      have ht := ih (fun b hb => hs b (by simp [hb]))
      simpa [rootProduct] using mul_ne_zero hza ht

lemma rootProduct_logDerivative_re_nonneg_of_re_lt (s : Multiset ℂ) (z : ℂ)
    (hs : ∀ a ∈ s, a.re < z.re) :
    0 ≤ ((rootProduct s).derivative.eval z / (rootProduct s).eval z).re := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct]
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.re < z.re := fun b hb => hs b (by simp [hb])
      have hpos : 0 < (z-a).re := sub_pos.mpr ha
      have hza : z-a ≠ 0 := by intro h; simpa [h] using hpos
      rw [rootProduct_cons_logDerivative a s hza (rootProduct_eval_ne_zero_of_re_lt s z ht),
        Complex.add_re]
      exact add_nonneg (re_inv_pos hpos).le (ih ht)

lemma rootProduct_logDerivative_re_pos_of_re_lt (s : Multiset ℂ) (hne : s ≠ 0) (z : ℂ)
    (hs : ∀ a ∈ s, a.re < z.re) :
    0 < ((rootProduct s).derivative.eval z / (rootProduct s).eval z).re := by
  induction s using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons a s ih =>
      have ha := hs a (by simp)
      have ht : ∀ b ∈ s, b.re < z.re := fun b hb => hs b (by simp [hb])
      have hpos : 0 < (z-a).re := sub_pos.mpr ha
      have hza : z-a ≠ 0 := by intro h; simpa [h] using hpos
      rw [rootProduct_cons_logDerivative a s hza (rootProduct_eval_ne_zero_of_re_lt s z ht),
        Complex.add_re]
      exact add_pos_of_pos_of_nonneg (re_inv_pos hpos)
        (rootProduct_logDerivative_re_nonneg_of_re_lt s z ht)

lemma eval_pos_of_nonneg_coeff_pos_constant (p : ℝ[X])
    (hc : ∀ n, 0 ≤ p.coeff n) (h0 : 0 < p.coeff 0) (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  classical
  rw [eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos'
  · intro n hn
    exact mul_nonneg (hc n) (pow_nonneg hx n)
  · exact ⟨0, mem_support_iff.mpr h0.ne', by simpa using h0⟩

lemma nonnegative_realRooted_roots_neg (p : ℝ[X]) (hr : RealRooted p)
    (hc : ∀ n, 0 ≤ p.coeff n) (h0 : 0 < p.coeff 0) :
    ∀ a ∈ (p.map (algebraMap ℝ ℂ)).roots, a.re < 0 := by
  have hp : p ≠ 0 := by intro he; simp [he] at h0
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  rcases hr with he | hr
  · exact (hp he).elim
  intro a ha
  have hz := (Polynomial.mem_roots hpmap).mp ha
  have hza : aeval a p = 0 := by simpa only [eval_map, ← aeval_def] using hz
  have hi := hr a hza
  have hae : a = (a.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have he : aeval (algebraMap ℝ ℂ a.re) p = 0 := by simpa [hae] using hza
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at he
  have her : p.eval a.re = 0 :=
    (algebraMap ℝ ℂ).injective (by simpa using he)
  by_contra h
  have hpos := eval_pos_of_nonneg_coeff_pos_constant p hc h0 a.re (le_of_not_gt h)
  linarith

/-- An internal zero immediately after a positive constant cannot be followed
by another positive coefficient in a nonnegative real-rooted polynomial. -/
lemma eq_constant_of_nonnegative_realRooted_coeff_one_zero (p : ℝ[X])
    (hr : RealRooted p) (hc : ∀ n, 0 ≤ p.coeff n) (h0 : 0 < p.coeff 0)
    (h1 : p.coeff 1 = 0) : p = C (p.coeff 0) := by
  let q := p.map (algebraMap ℝ ℂ)
  have hp : p ≠ 0 := by intro he; simp [he] at h0
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  have hs : ∀ a ∈ q.roots, a.re < (0 : ℂ).re :=
    nonnegative_realRooted_roots_neg p hr hc h0
  have he : q.roots = 0 := by
    by_contra hne
    have ht := rootProduct_logDerivative_re_pos_of_re_lt q.roots hne 0 hs
    rw [← logDerivative_eq_rootProduct q hq 0] at ht
    have hd : q.derivative.eval 0 = 0 := by
      simp [q, derivative_map, coeff_derivative, h1]
    simp [hd] at ht
  have hf := eq_leadingCoeff_rootProduct q
  simp only [he, rootProduct, Multiset.map_zero, Multiset.prod_zero, mul_one] at hf
  have hdeg : p.natDegree = 0 := by
    have hd : q.natDegree = 0 := by rw [hf]; exact natDegree_C _
    simpa [q] using hd
  exact eq_C_of_natDegree_eq_zero hdeg

end AIM34
