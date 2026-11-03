import SchwarzHalfPlane

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

/-- Iteratively remove the positive integer roots, using the removable quotient. -/
def removeIntegerRoots (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | N + 1 => schwarzQuotient (removeIntegerRoots f N) (N + 1)

lemma removeIntegerRoots_properties {f : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M)
    (hz : ∀ n : ℕ, 0 < n → f n = 0) (N : ℕ) :
    DifferentiableOn ℂ (removeIntegerRoots f N) rightHalfPlane ∧
    (∀ z ∈ rightHalfPlane, ‖removeIntegerRoots f N z‖ ≤ M) ∧
    (∀ n : ℕ, N < n → removeIntegerRoots f N n = 0) := by
  induction N with
  | zero => exact ⟨hf, hb, hz⟩
  | succ N ih =>
    have ha : (0 : ℝ) < N + 1 := by positivity
    have hzero : removeIntegerRoots f N (Complex.ofReal ((N : ℝ) + 1)) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one] using ih.2.2 (N + 1) (Nat.lt_succ_self N)
    refine ⟨differentiableOn_schwarzQuotient ha ih.1,
      fun z hz => norm_schwarzQuotient_le ha ih.1 hzero ih.2.1 hz, ?_⟩
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnh : (n : ℂ) ∈ rightHalfPlane := by simpa [rightHalfPlane] using hnpos
    have heq := halfPlaneToDisk_mul_schwarzQuotient ha hzero hnh
    rw [ih.2.2 n (by omega)] at heq
    have hne : halfPlaneToDisk ((N : ℝ) + 1) (n : ℂ) ≠ 0 := by
      rw [halfPlaneToDisk, div_ne_zero_iff]
      refine ⟨?_, add_ofReal_ne_zero ha hnh⟩
      intro he
      have he' := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.natCast_re, Complex.ofReal_re,
        Complex.zero_re] at he'
      have : (N : ℝ) + 1 < n := by exact_mod_cast hn
      linarith
    exact (mul_eq_zero.mp heq).resolve_left hne

lemma removeIntegerRoots_factorization {f : ℂ → ℂ}
    (hz : ∀ n : ℕ, 0 < n → f n = 0)
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    {M : ℝ} (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M)
    (N : ℕ) {z : ℂ} (hzh : z ∈ rightHalfPlane) :
    f z = (∏ k ∈ Finset.range N, halfPlaneToDisk ((k : ℝ) + 1) z) *
      removeIntegerRoots f N z := by
  induction N with
  | zero => simp [removeIntegerRoots]
  | succ N ih =>
    have hp := removeIntegerRoots_properties hf hb hz N
    have ha : (0 : ℝ) < N + 1 := by positivity
    have hzero : removeIntegerRoots f N (Complex.ofReal ((N : ℝ) + 1)) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one] using hp.2.2 (N + 1) (Nat.lt_succ_self N)
    rw [Finset.prod_range_succ, mul_assoc, removeIntegerRoots,
      halfPlaneToDisk_mul_schwarzQuotient ha hzero hzh]
    exact ih

/-- Uniform squared Cayley-factor bound on a small complex lens. -/
lemma norm_halfPlaneToDisk_sq_le {z : ℂ} (hre : (1 / 2 : ℝ) ≤ z.re)
    (hnorm : ‖z‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖halfPlaneToDisk n z‖ ^ 2 ≤ (2 * (n : ℝ) - 1) / (2 * n + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hzh : z ∈ rightHalfPlane := by change 0 < z.re; linarith
  have hden : 0 < Complex.normSq (z + (n : ℂ)) :=
    Complex.normSq_pos.mpr (add_ofReal_ne_zero (by positivity : (0 : ℝ) < n) hzh)
  rw [halfPlaneToDisk, Complex.sq_norm, Complex.normSq_div]
  simp only [Complex.ofReal_natCast]
  rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 2 * n + 1)]
  have hs : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero,
    Complex.natCast_re, Complex.natCast_im] at *
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (n : ℝ) ^ 2 by positivity)
    (show 0 ≤ 2 * z.re - 1 by linarith)
  nlinarith

lemma prod_norm_halfPlaneToDisk_sq_le {z : ℂ} (hre : (1 / 2 : ℝ) ≤ z.re)
    (hnorm : ‖z‖ ≤ 1) (N : ℕ) :
    (∏ k ∈ Finset.range N, ‖halfPlaneToDisk ((k : ℝ) + 1) z‖ ^ 2) ≤
      1 / (2 * (N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ]
    have hn := norm_halfPlaneToDisk_sq_le hre hnorm (Nat.succ_pos N)
    simp only [Nat.cast_succ] at hn
    calc
      _ ≤ (1 / (2 * (N : ℝ) + 1)) * ((2 * ((N : ℝ) + 1) - 1) /
          (2 * ((N : ℝ) + 1) + 1)) :=
        mul_le_mul ih hn (sq_nonneg _) (by positivity)
      _ = 1 / (2 * ((N + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        have h1 : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
        have h3 : (2 * ((N : ℝ) + 1) + 1) ≠ 0 := by positivity
        field_simp [h1, h3]
        <;> ring

lemma norm_sq_le_of_integer_zeros {f : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M)
    (hz : ∀ n : ℕ, 0 < n → f n = 0) {z : ℂ}
    (hre : (1 / 2 : ℝ) ≤ z.re) (hnorm : ‖z‖ ≤ 1) (N : ℕ) :
    ‖f z‖ ^ 2 ≤ M ^ 2 / (2 * (N : ℝ) + 1) := by
  have hzh : z ∈ rightHalfPlane := by change 0 < z.re; linarith
  have hq := (removeIntegerRoots_properties hf hb hz N).2.1 z hzh
  have hqsq : ‖removeIntegerRoots f N z‖ ^ 2 ≤ M ^ 2 := by
    nlinarith [norm_nonneg (removeIntegerRoots f N z)]
  rw [removeIntegerRoots_factorization hz hf hb N hzh, norm_mul, mul_pow,
    norm_prod, ← Finset.prod_pow]
  exact (mul_le_mul (prod_norm_halfPlaneToDisk_sq_le hre hnorm N) hqsq
    (sq_nonneg _) (by positivity)).trans_eq (by ring)

lemma eq_zero_on_lens_of_integer_zeros {f : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M)
    (hz : ∀ n : ℕ, 0 < n → f n = 0) {z : ℂ}
    (hre : (1 / 2 : ℝ) ≤ z.re) (hnorm : ‖z‖ ≤ 1) : f z = 0 := by
  by_contra hne
  have hp : 0 < ‖f z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (M ^ 2 / ‖f z‖ ^ 2)
  have hbound := norm_sq_le_of_integer_zeros hf hb hz hre hnorm N
  have hlarge : M ^ 2 < (N : ℝ) * ‖f z‖ ^ 2 := (div_lt_iff₀ hp).mp hN
  have hden : (0 : ℝ) < 2 * N + 1 := by positivity
  have hsmall := (le_div_iff₀ hden).mp hbound
  nlinarith [mul_nonneg (Nat.cast_nonneg N) hp.le]

/-- A bounded holomorphic function on the open right half-plane with all positive integer
zeros is identically zero. The proof iterates removable Schwarz division; it does not assume
Carlson uniqueness or a Blaschke zero-set theorem. -/
theorem eq_zero_of_bounded_rightHalfPlane_integer_zeros {f : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M)
    (hz : ∀ n : ℕ, 0 < n → f n = 0) : EqOn f 0 rightHalfPlane := by
  have ha : AnalyticOnNhd ℂ f rightHalfPlane :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_rightHalfPlane).mpr hf
  have hc : IsPreconnected rightHalfPlane :=
    (convex_halfSpace_gt Complex.reLm.isLinear 0).isPreconnected
  apply ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc
    (z₀ := (3 / 4 : ℂ)) (by norm_num [rightHalfPlane])
  have ho : IsOpen ({z : ℂ | (1 / 2 : ℝ) < z.re} ∩ ball 0 1) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
  have hm : (3 / 4 : ℂ) ∈ ({z : ℂ | (1 / 2 : ℝ) < z.re} ∩ ball 0 1) := by
    constructor <;> norm_num [mem_ball_zero_iff]
  filter_upwards [ho.mem_nhds hm] with z h
  exact eq_zero_on_lens_of_integer_zeros hf hb hz h.1.le
    (mem_ball_zero_iff.mp h.2).le

end AIM34
