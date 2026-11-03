import RadicalBranchObstruction

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

lemma norm_entire_radical_interpolant_threeQuarter {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    {H : ℂ → ℂ}
    (hb : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ N →
      ‖H z‖ ≤ Real.rpow ((3 * N : ℕ) + m) (Real.sqrt ((3 * N : ℕ) + m)) + C)
    {z : ℂ} (hz : z ∈ rightHalfPlane) :
    ‖H z‖ ≤ (C + 1) * Real.exp
      ((4 * (6 + m) ^ (3 / 4 : ℝ)) * ‖z + 1‖ ^ (3 / 4 : ℝ)) := by
  let N : ℕ := ⌈‖z‖⌉₊
  have hN : ‖z‖ ≤ (N : ℝ) := Nat.le_ceil _
  have hre : 0 ≤ z.re := (show 0 < z.re from hz).le
  have hR := one_le_norm_add_one hre
  have hzR := norm_le_norm_add_one hre
  have hNlt : (N : ℝ) < ‖z‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg z)
  have ht : (0 : ℝ) < (3 * N : ℕ) + m := by positivity
  have htU : ((3 * N : ℕ) : ℝ) + m ≤ (6 + m) * ‖z + 1‖ := by
    push_cast
    nlinarith
  have hp := Real.rpow_le_rpow ht.le htU (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hval := radicalPowerReal_le_threeQuarter ht
  have hbound := hb N z hN
  have he : 4 * (((3 * N : ℕ) : ℝ) + m) ^ (3 / 4 : ℝ) ≤
      (4 * (6 + m) ^ (3 / 4 : ℝ)) * ‖z + 1‖ ^ (3 / 4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4)
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 6 + m) (norm_nonneg _)] at hmul
    simpa [mul_assoc] using hmul
  have hval' := hval.trans (Real.exp_le_exp.mpr he)
  have hge : 1 ≤ Real.exp ((4 * (6 + m) ^ (3 / 4 : ℝ)) * ‖z + 1‖ ^ (3 / 4 : ℝ)) :=
    Real.one_le_exp (by positivity)
  nlinarith

lemma radical_interpolant_eq_on_halfPlane {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hn : ∀ n : ℕ, H n = (Real.rpow (n + m) (Real.sqrt (n + m)) : ℂ))
    (hb : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ N →
      ‖H z‖ ≤ Real.rpow ((3 * N : ℕ) + m) (Real.sqrt ((3 * N : ℕ) + m)) + C) :
    EqOn H (radicalPowerAnalytic m) rightHalfPlane := by
  let A : ℝ := 4 * (6 + m) ^ (3 / 4 : ℝ)
  let B : ℝ := (|Real.log m| + Real.pi + 4) * (1 + m) ^ (3 / 4 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : rightHalfPlane ⊆ shiftedRightHalfPlane m := by
    intro z hz
    change -m < z.re
    have hz' : 0 < z.re := hz
    linarith
  have hdiff : DifferentiableOn ℂ (fun z => H z - radicalPowerAnalytic m z) rightHalfPlane :=
    hH.differentiableOn.sub ((differentiableOn_radicalPowerAnalytic m).mono hs)
  have hzero : EqOn (fun z => H z - radicalPowerAnalytic m z) 0 rightHalfPlane := by
    apply eq_zero_of_rightHalfPlane_threeQuarter_growth hdiff
      (show 0 ≤ A + B from add_nonneg hA hB) (show 0 ≤ C + 2 by linarith)
    · intro z hz
      have hHbound := norm_entire_radical_interpolant_threeQuarter hm hC hb hz
      have hhbound := norm_radicalPowerAnalytic_threeQuarter hm hz
      change ‖H z‖ ≤ (C + 1) * Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ)) at hHbound
      change ‖radicalPowerAnalytic m z‖ ≤ Real.exp (B * ‖z + 1‖ ^ (3 / 4 : ℝ)) at hhbound
      have hpow : 0 ≤ ‖z + 1‖ ^ (3 / 4 : ℝ) := by positivity
      have hEA : Real.exp (A * ‖z + 1‖ ^ (3 / 4 : ℝ)) ≤
          Real.exp ((A + B) * ‖z + 1‖ ^ (3 / 4 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hEB : Real.exp (B * ‖z + 1‖ ^ (3 / 4 : ℝ)) ≤
          Real.exp ((A + B) * ‖z + 1‖ ^ (3 / 4 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hHfinal := hHbound.trans (mul_le_mul_of_nonneg_left hEA (by linarith : 0 ≤ C + 1))
      have hhfinal := hhbound.trans hEB
      have hnorm := norm_sub_le (H z) (radicalPowerAnalytic m z)
      nlinarith
    · intro n hnpos
      rw [hn n]
      have ht : (0 : ℝ) < n + m := by positivity
      have hval := radicalPowerAnalytic_ofReal (m := m) (t := n) ht
      simp only [Complex.ofReal_natCast] at hval
      rw [hval, sub_self]
  intro z hz
  exact sub_eq_zero.mp (hzero hz)

lemma radical_interpolant_eq_on_shiftedHalfPlane {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hn : ∀ n : ℕ, H n = (Real.rpow (n + m) (Real.sqrt (n + m)) : ℂ))
    (hb : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ N →
      ‖H z‖ ≤ Real.rpow ((3 * N : ℕ) + m) (Real.sqrt ((3 * N : ℕ) + m)) + C) :
    EqOn H (radicalPowerAnalytic m) (shiftedRightHalfPlane m) := by
  have hsame := radical_interpolant_eq_on_halfPlane hm hC hH hn hb
  have haH : AnalyticOnNhd ℂ H (shiftedRightHalfPlane m) := fun z hz => hH.analyticAt z
  have hah := (differentiableOn_radicalPowerAnalytic m).analyticOnNhd
    (isOpen_shiftedRightHalfPlane m)
  apply haH.eqOn_of_preconnected_of_eventuallyEq hah (isPreconnected_shiftedRightHalfPlane m)
    (z₀ := (1 : ℂ)) (by change -m < (1 : ℂ).re; norm_num; linarith)
  filter_upwards [isOpen_rightHalfPlane.mem_nhds (by norm_num [rightHalfPlane] :
    (1 : ℂ) ∈ rightHalfPlane)] with z hz
  exact hsame hz

/-- No entire interpolant with the proved Newton growth can interpolate the actual
radical-power sequence, for any positive real shift. -/
theorem no_entire_radicalPower_interpolant {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hn : ∀ n : ℕ, H n = (Real.rpow (n + m) (Real.sqrt (n + m)) : ℂ))
    (hb : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ N →
      ‖H z‖ ≤ Real.rpow ((3 * N : ℕ) + m) (Real.sqrt ((3 * N : ℕ) + m)) + C) : False := by
  have hext := radical_interpolant_eq_on_shiftedHalfPlane hm hC hH hn hb
  apply no_entire_radicalPower_extension (fun z => H (z - m))
    (hH.comp (differentiable_id.sub_const _))
  intro t ht
  have hz : (t : ℂ) - m ∈ shiftedRightHalfPlane m := by
    change -m < ((t : ℂ) - m).re
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [hext hz, radicalPowerAnalytic, sub_add_cancel]
  exact radicalPowerCore_ofReal ht

end AIM34
