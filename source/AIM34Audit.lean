import FullAIM34

#print axioms AIM34.not_multiplier_shiftedRadicalPower
#print axioms AIM34.exists_counterexample_polynomial
#print axioms AIM34.fullProblem34
#print axioms AIM34.problem34_positive_integer_shift
#print axioms AIM34.problem34_one_indexed_shift
#print axioms AIM34.multiplier_shiftedRadicalPower_all_differences_nonneg
#print axioms AIM34.complexPolar_roots_real
#print axioms AIM34.no_entire_radicalPower_interpolant
#print axioms AIM34.entire_newton_interpolation_and_growth
#print axioms AIM34.eq_zero_of_bounded_rightHalfPlane_integer_zeros

example : ∀ m : ℝ, 0 < m → ¬ (∀ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) →
    let q := p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)
    q = 0 ∨ ∀ z : ℂ, Polynomial.aeval z q = 0 → z.im = 0) :=
  AIM34.not_multiplier_shiftedRadicalPower

example : AIM34.diagonal (fun _ => 1) (0 : Polynomial ℝ) = 0 := by
  simp [AIM34.diagonal]
