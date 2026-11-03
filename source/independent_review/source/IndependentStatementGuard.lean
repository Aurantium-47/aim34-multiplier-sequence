import FullAIM34
namespace AIM34Independent

theorem actualAllRealShifts : ∀ m : ℝ, 0 < m → ¬ (∀ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) →
    let q := p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)
    q = 0 ∨ ∀ z : ℂ, Polynomial.aeval z q = 0 → z.im = 0) :=
  AIM34.not_multiplier_shiftedRadicalPower

theorem actualFiniteWitness : ∀ m : ℝ, 0 < m → ∃ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) ∧
    ¬ ((p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)) = 0 ∨
      ∀ z : ℂ, Polynomial.aeval z (p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)) = 0 → z.im = 0) :=
  AIM34.exists_counterexample_polynomial

theorem actualIntegerShifts : ∀ m : ℕ, 0 < m → ¬ (∀ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) →
    let q := p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)
    q = 0 ∨ ∀ z : ℂ, Polynomial.aeval z q = 0 → z.im = 0) :=
  AIM34.problem34_positive_integer_shift

theorem actualOneIndexedShifts : ∀ m : ℕ, ¬ (∀ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) →
    let q := p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+1+m) (Real.sqrt ((n : ℝ)+1+m))*c)
    q = 0 ∨ ∀ z : ℂ, Polynomial.aeval z q = 0 → z.im = 0) :=
  AIM34.problem34_one_indexed_shift

theorem actualFullAlias : ∀ m : ℝ, 0 < m → ¬ (∀ p : Polynomial ℝ,
    (p = 0 ∨ ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0) →
    let q := p.sum fun n c => Polynomial.monomial n
      (Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m))*c)
    q = 0 ∨ ∀ z : ℂ, Polynomial.aeval z q = 0 → z.im = 0) := AIM34.fullProblem34

theorem actualCoefficient (m : ℝ) (p : Polynomial ℝ) (n : ℕ) :
    (AIM34.diagonal (AIM34.shiftedRadicalPower m) p).coeff n =
    Real.rpow ((n : ℝ)+m) (Real.sqrt ((n : ℝ)+m)) * p.coeff n :=
  AIM34.diagonal_coeff _ _ _
end AIM34Independent
