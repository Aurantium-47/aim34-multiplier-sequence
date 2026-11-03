import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Set Metric Filter
open scoped Topology

noncomputable section

namespace AIM34

/-- The open right half-plane. -/
def rightHalfPlane : Set ℂ := {z | 0 < z.re}

lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Cayley map based at a positive real point. -/
def halfPlaneToDisk (a : ℝ) (z : ℂ) : ℂ := (z - a) / (z + a)

/-- Inverse Cayley map. -/
def diskToHalfPlane (a : ℝ) (w : ℂ) : ℂ := a * (1 + w) / (1 - w)

lemma add_ofReal_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ rightHalfPlane) : z + (a : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
  change 0 < z.re at hz
  linarith

lemma halfPlaneToDisk_mem_ball {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ rightHalfPlane) : halfPlaneToDisk a z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, halfPlaneToDisk, norm_div, div_lt_one (norm_pos_iff.mpr
    (add_ofReal_ne_zero ha hz))]
  have hn : ‖z - (a : ℂ)‖ ^ 2 < ‖z + (a : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      add_zero]
    change 0 < z.re at hz
    nlinarith [mul_pos ha hz]
  nlinarith [norm_nonneg (z - (a : ℂ)), norm_nonneg (z + (a : ℂ))]

lemma one_sub_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.mp h).symm
  subst w
  simpa using hw

lemma diskToHalfPlane_mem {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : diskToHalfPlane a w ∈ rightHalfPlane := by
  have hn : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have hd : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr (one_sub_ne_zero hw)
  change 0 < (diskToHalfPlane a w).re
  rw [diskToHalfPlane, Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, zero_mul, zero_add, sub_zero, zero_sub, mul_zero, sub_zero]
  rw [← add_div]
  apply div_pos _ hd
  have hn' := hn
  rw [Complex.normSq_apply] at hn'
  nlinarith [mul_pos ha (sub_pos.mpr hn')]

lemma diskToHalfPlane_halfPlaneToDisk {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ rightHalfPlane) : diskToHalfPlane a (halfPlaneToDisk a z) = z := by
  have haz : z + (a : ℂ) ≠ 0 := add_ofReal_ne_zero ha hz
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  dsimp [diskToHalfPlane, halfPlaneToDisk]
  field_simp [haz, ha']
  <;> ring

lemma differentiableOn_halfPlaneToDisk {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (halfPlaneToDisk a) rightHalfPlane := by
  exact (differentiableOn_id.sub_const _).div (differentiableOn_id.add_const _)
    (fun z hz => add_ofReal_ne_zero ha hz)

lemma differentiableOn_diskToHalfPlane (a : ℝ) :
    DifferentiableOn ℂ (diskToHalfPlane a) (ball 0 1) := by
  exact ((differentiableOn_const _).mul ((differentiableOn_const _).add differentiableOn_id)).div
    ((differentiableOn_const _).sub differentiableOn_id) (fun w hw => one_sub_ne_zero hw)

/-- The removable Schwarz quotient is defined by `dslope`, including at the removed root. -/
def schwarzQuotient (f : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  dslope (fun w => f (diskToHalfPlane a w)) 0 (halfPlaneToDisk a z)

lemma differentiableOn_schwarzQuotient {f : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hf : DifferentiableOn ℂ f rightHalfPlane) :
    DifferentiableOn ℂ (schwarzQuotient f a) rightHalfPlane := by
  have hF : DifferentiableOn ℂ (fun w => f (diskToHalfPlane a w)) (ball 0 1) :=
    hf.comp (differentiableOn_diskToHalfPlane a) (fun w hw => diskToHalfPlane_mem ha hw)
  exact ((Complex.differentiableOn_dslope (ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))).mpr hF).comp
    (differentiableOn_halfPlaneToDisk ha) (fun z hz => halfPlaneToDisk_mem_ball ha hz)

lemma halfPlaneToDisk_mul_schwarzQuotient {f : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hfa : f a = 0) {z : ℂ} (hz : z ∈ rightHalfPlane) :
    halfPlaneToDisk a z * schwarzQuotient f a z = f z := by
  have h := sub_smul_dslope (fun w => f (diskToHalfPlane a w)) 0 (halfPlaneToDisk a z)
  rw [diskToHalfPlane_halfPlaneToDisk ha hz] at h
  simpa [schwarzQuotient, diskToHalfPlane, hfa] using h

lemma norm_schwarzQuotient_le {f : ℂ → ℂ} {a M : ℝ} (ha : 0 < a)
    (hf : DifferentiableOn ℂ f rightHalfPlane) (hfa : f a = 0)
    (hb : ∀ z ∈ rightHalfPlane, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ rightHalfPlane) :
    ‖schwarzQuotient f a z‖ ≤ M := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hbM
  have hF : DifferentiableOn ℂ (fun w => f (diskToHalfPlane a w)) (ball 0 1) :=
    hf.comp (differentiableOn_diskToHalfPlane a) (fun w hw => diskToHalfPlane_mem ha hw)
  have hm : MapsTo (fun w => f (diskToHalfPlane a w)) (ball 0 1)
      (ball (f (diskToHalfPlane a 0)) b) := by
    intro w hw
    simp only [diskToHalfPlane, add_zero, sub_zero, mul_one, div_one, hfa,
      mem_ball_zero_iff]
    exact (hb _ (diskToHalfPlane_mem ha hw)).trans_lt hbM
  simpa [schwarzQuotient] using
    (Complex.norm_dslope_le_div_of_mapsTo_ball hF hm (halfPlaneToDisk_mem_ball ha hz))

end AIM34
