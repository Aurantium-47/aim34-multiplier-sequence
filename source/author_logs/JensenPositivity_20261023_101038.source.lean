import NonnegativeRootGeometry
import Lean.Elab.Tactic.Omega

noncomputable section
open Polynomial
open scoped BigOperators
namespace AIM34

lemma jensen_two (a : ℕ → ℝ) :
    jensen a 2 = C (a 0) + C (a 1*2)*X + C (a 2)*X^2 := by
  rw [(jensen a 2).as_sum_range' 3 (Nat.lt_succ_of_le (jensen_natDegree_le a 2))]
  norm_num [Finset.sum_range_succ, jensen_coeff, ← C_mul_X_pow_eq_monomial]

lemma jensen_two_logconcave (a : ℕ → ℝ) (hr : RealRooted (jensen a 2)) :
    a 0 * a 2 ≤ a 1 ^ 2 := by
  by_cases h2 : a 2 = 0
  · simp [h2, sq_nonneg]
  have hp : jensen a 2 ≠ 0 := by
    intro he
    have hc := congrArg (fun p : ℝ[X] => p.coeff 2) he
    simpa [jensen_coeff, h2] using hc
  rcases hr with he | hr
  · exact (hp he).elim
  let p := (jensen a 2).map (algebraMap ℝ ℂ)
  have hc : p.coeff 2 ≠ 0 := by simp [p, coeff_map, jensen_coeff, h2]
  have hd : (0 : WithBot ℕ) < p.degree :=
    lt_of_lt_of_le (by norm_num : (0 : WithBot ℕ) < 2) (le_degree_of_ne_zero hc)
  obtain ⟨z, hz⟩ := Complex.exists_root hd
  have hza : aeval z (jensen a 2) = 0 := by
    simpa only [p, Polynomial.IsRoot, eval_map, ← aeval_def] using hz
  have hi := hr z hza
  have hze : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have he := hza
  rw [hze] at he
  change aeval (algebraMap ℝ ℂ z.re) (jensen a 2) = 0 at he
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at he
  have hreal : (jensen a 2).eval z.re = 0 :=
    (algebraMap ℝ ℂ).injective (by simpa using he)
  rw [jensen_two] at hreal
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at hreal
  have hm := congrArg (fun x : ℝ => a 2*x) hreal
  nlinarith [sq_nonneg (a 2*z.re+a 1)]

lemma allJensen_logconcave (a : ℕ → ℝ) (ha : AllJensenRealRooted a) (n : ℕ) :
    a n * a (n+2) ≤ a (n+1)^2 := by
  have h := jensen_two_logconcave (fun j => a (j+n)) (allJensen_shift_add a ha n 2)
  simpa only [zero_add, Nat.add_comm 1 n, Nat.add_comm 2 n] using h

lemma allJensen_zero_tail (a : ℕ → ℝ) (ha : AllJensenRealRooted a)
    (hnonneg : ∀ n, 0 ≤ a n) (i : ℕ) (hi : 0 < a i) (hi1 : a (i+1) = 0)
    (k : ℕ) (hik : i+1 ≤ k) : a k = 0 := by
  let b := fun n => a (n+i)
  have hb := allJensen_shift_add a ha i
  have hc : ∀ n, 0 ≤ (jensen b (k-i)).coeff n := by
    intro n
    rw [jensen_coeff]
    exact mul_nonneg (hnonneg _) (Nat.cast_nonneg _)
  have h0 : 0 < (jensen b (k-i)).coeff 0 := by simpa [jensen_coeff, b] using hi
  have h1 : (jensen b (k-i)).coeff 1 = 0 := by
    simp [jensen_coeff, b, Nat.add_comm 1 i, hi1]
  have he := eq_constant_of_nonnegative_realRooted_coeff_one_zero _ (hb (k-i)) hc h0 h1
  have hki : k-i ≠ 0 := by omega
  have hlast : (jensen b (k-i)).coeff (k-i) = 0 := by rw [he]; simp [hki]
  have hil : i ≤ k := by omega
  simpa [jensen_coeff, b, Nat.sub_add_cancel hil] using hlast

lemma allJensen_interval_support (a : ℕ → ℝ) (ha : AllJensenRealRooted a)
    (hnonneg : ∀ n, 0 ≤ a n) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < a i) (hk : 0 < a k) : 0 < a j := by
  have hstep : ∀ d : ℕ, i+d ≤ k → 0 < a (i+d) := by
    intro d
    induction d with
    | zero => simpa using fun _ : i ≤ k => hi
    | succ d ih =>
        intro hd
        have hprev := ih (by omega)
        by_contra hnot
        have he : a (i+d+1) = 0 := by
          apply le_antisymm
          · simpa only [Nat.succ_eq_add_one, ← Nat.add_assoc] using le_of_not_gt hnot
          · exact hnonneg _
        have hz := allJensen_zero_tail a ha hnonneg (i+d) hprev he k (by omega)
        linarith
  have h := hstep (j-i) (by omega)
  simpa only [Nat.add_sub_of_le hij] using h

end AIM34
