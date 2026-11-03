import RadicalPowerAnalytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Metric Filter
open scoped Topology BigOperators
noncomputable section

namespace AIM34

def radicalRealDerivative (t : ℝ) : ℝ :=
  Real.exp (Real.sqrt t * Real.log t) * (Real.log t + 2) / (2 * Real.sqrt t)

lemma hasDerivAt_radicalReal {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.exp (Real.sqrt t * Real.log t))
      (radicalRealDerivative t) t := by
  have h := ((Real.hasDerivAt_sqrt ht.ne').mul (Real.hasDerivAt_log ht.ne')).exp
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have he : 1 / (2 * Real.sqrt t) * Real.log t + Real.sqrt t * t⁻¹ =
      (Real.log t + 2) / (2 * Real.sqrt t) := by
    field_simp [ht.ne', hs]
    nlinarith [congrArg (fun x : ℝ => x * Real.sqrt t) (Real.sq_sqrt ht.le)]
  simpa only [he, radicalRealDerivative, mul_div_assoc] using h

lemma tendsto_radicalRealDerivative_atBot :
    Tendsto radicalRealDerivative (𝓝[>] (0 : ℝ)) atBot := by
  have hv : Tendsto (fun t : ℝ => Real.sqrt t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2)
  have hexp : Tendsto (fun t : ℝ => Real.exp (Real.sqrt t * Real.log t))
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hv
  have hlog : Tendsto (fun t : ℝ => Real.log t + 2) (𝓝[>] 0) atBot := by
    exact tendsto_atBot_add_const_right _ 2 Real.tendsto_log_nhdsGT_zero
  have hnum := Filter.Tendsto.pos_mul_atBot (by norm_num : (0 : ℝ) < 1) hexp hlog
  have hs : Tendsto (fun t : ℝ => 2 * Real.sqrt t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
      simpa using tendsto_const_nhds.mul h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos (by norm_num) (Real.sqrt_pos.mpr ht)
  have hinv := tendsto_inv_nhdsGT_zero.comp hs
  unfold radicalRealDerivative
  simpa only [div_eq_mul_inv] using hnum.atBot_mul_atTop₀ hinv

/-- The radical-power branch on the positive real axis has no entire extension.
This discharges the endpoint obstruction using its derivative's actual divergence. -/
theorem no_entire_radicalPower_extension (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (heq : ∀ t : ℝ, 0 < t → G t = (Real.rpow t (Real.sqrt t) : ℂ)) : False := by
  have hderiv : ∀ t : ℝ, 0 < t → (deriv G (t : ℂ)).re = radicalRealDerivative t := by
    intro t ht
    have hreal := (hG (t : ℂ)).hasDerivAt.real_of_complex
    have hsame : (fun x : ℝ => (G (x : ℂ)).re) =ᶠ[𝓝 t]
        (fun x : ℝ => Real.exp (Real.sqrt x * Real.log x)) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      rw [heq x hx, Complex.ofReal_re]
      change (x : ℝ) ^ Real.sqrt x = _
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring
    exact hreal.unique ((hasDerivAt_radicalReal ht).congr_of_eventuallyEq hsame)
  have hcont : Continuous (deriv G) :=
    (differentiableOn_univ.mp (hG.differentiableOn.deriv isOpen_univ)).continuous
  have hfinite : Tendsto (fun t : ℝ => (deriv G (t : ℂ)).re) (𝓝[>] 0)
      (𝓝 ((deriv G 0).re)) := by
    exact (Complex.continuous_re.comp (hcont.comp Complex.continuous_ofReal)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hevent : (fun t : ℝ => (deriv G (t : ℂ)).re) =ᶠ[𝓝[>] 0] radicalRealDerivative := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hderiv t ht
  have hfinite' := hfinite.congr' hevent
  exact not_tendsto_nhds_of_tendsto_atBot tendsto_radicalRealDerivative_atBot _ hfinite'

end AIM34
