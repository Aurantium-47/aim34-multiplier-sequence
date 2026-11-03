import JensenIdentities
import PolarRealRooted

noncomputable section
open Polynomial
namespace AIM34

lemma realRooted_of_C_mul (c : ℝ) (hc : c ≠ 0) (p : ℝ[X])
    (hr : RealRooted (C c*p)) : RealRooted p := by
  rcases hr with hz | hr
  · left
    exact (mul_eq_zero.mp hz).resolve_left (C_ne_zero.mpr hc)
  · right
    intro z hz
    apply hr z
    simp [hz]

lemma realRooted_polar (M : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ M)
    (hr : RealRooted p) : RealRooted ((X+1)*p.derivative-C (M : ℝ)*p) := by
  rcases hr with hp | hr
  · left; simp [hp]
  let q : ℝ[X] := (X+1)*p.derivative-C (M : ℝ)*p
  have he : q.map (algebraMap ℝ ℂ) = complexPolar M (p.map (algebraMap ℝ ℂ)) := by
    simp [q, complexPolar, derivative_map]
  have hm : (p.map (algebraMap ℝ ℂ)).natDegree ≤ M := by
    simpa using hdeg
  have hc : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 := by
    simpa only [eval_map, ← aeval_def] using hr
  rcases complexPolar_roots_real M _ hm hc with hz | hz
  · left
    apply (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp
    exact he.trans hz
  · right
    intro z h
    apply hz z
    rw [← he, eval_map, ← aeval_def]
    exact h

lemma allJensen_shift (a : ℕ → ℝ) (ha : AllJensenRealRooted a) :
    AllJensenRealRooted (fun n => a (n+1)) := by
  intro N
  apply realRooted_of_C_mul (N+1) (by positivity)
  rw [← jensen_derivative]
  exact realRooted_derivative _ (ha (N+1))

lemma allJensen_shift_add (a : ℕ → ℝ) (ha : AllJensenRealRooted a) (k : ℕ) :
    AllJensenRealRooted (fun n => a (n+k)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using allJensen_shift _ ih

/-- Finite Jensen real-rootedness is closed under forward difference without a
classification theorem or finite Jensen sufficiency assumption. -/
lemma allJensen_forwardDifference (a : ℕ → ℝ) (ha : AllJensenRealRooted a) :
    AllJensenRealRooted (forwardDifference a) := by
  intro N
  apply realRooted_of_C_mul (N+1) (by positivity)
  rw [jensen_forwardDifference, add_comm (1 : ℝ[X]) X]
  simpa only [Nat.cast_add, Nat.cast_one] using realRooted_polar (N+1) _ (jensen_natDegree_le a (N+1)) (ha (N+1))

end AIM34
