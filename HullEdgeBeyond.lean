import DiameterHull
import HullSupport
import NormalizedEdge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! A hull vertex cannot lie strictly between two other configuration points
on the same line. -/

namespace Erdos957

/-- From an extreme configuration point `w`, the ray opposite another
configuration point `u` contains no configuration point beyond `w`.
This rules out the degenerate, collinear part of a putative point behind a
supporting hull edge. -/
theorem hull_extreme_not_opposite_ray {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {u w k : Fin n} (hw : w ∈ hullVertexIndices p)
    (hwu : w ≠ u) (t : ℝ) (ht : 0 < t)
    (hrel : p k - p w = -t • (p u - p w)) : False := by
  classical
  have hext : p w ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hw).2
  obtain ⟨f, hf⟩ := hull_extreme_strict_support p hp w hext
  have hu : f (p u) < f (p w) := hf u hwu.symm
  have hk : f (p k) ≤ f (p w) := by
    by_cases hkw : k = w
    · simp [hkw]
    · exact (hf k hkw).le
  have hmap := congrArg f hrel
  simp only [map_sub, map_smul, smul_eq_mul] at hmap
  have hmul : 0 < t * (f (p w) - f (p u)) :=
    mul_pos ht (sub_pos.mpr hu)
  nlinarith

/-- In coordinates sending `u` to zero and extreme vertex `w` to one, no
configuration point can lie strictly beyond one on the real axis. -/
theorem hull_extreme_no_normalized_beyond {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {u w k : Fin n} (huw : u ≠ w) (hw : w ∈ hullVertexIndices p)
    (him : (edgeCoordinate (p u) (p w) (p k)).im = 0)
    (hre : 1 < (edgeCoordinate (p u) (p w) (p k)).re) : False := by
  let z := edgeCoordinate (p u) (p w) (p k)
  have hden : pointToComplex (p w - p u) ≠ 0 := by
    intro hz
    have hsub : p w - p u = 0 := pointToComplex.injective (by simpa using hz)
    exact huw (hp (sub_eq_zero.mp hsub)).symm
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [z] using him
  have hquot : pointToComplex (p k - p u) /
      pointToComplex (p w - p u) = z := rfl
  have hcomplex : pointToComplex (p k - p u) =
      (z.re : ℂ) * pointToComplex (p w - p u) := by
    have h := (div_eq_iff hden).mp hquot
    rw [hzreal] at h
    exact h
  have hpoint : p k - p u = z.re • (p w - p u) := by
    apply pointToComplex.injective
    rw [map_smul]
    simpa only [Complex.real_smul] using hcomplex
  have ht : 0 < z.re - 1 := by change 1 < z.re at hre; linarith
  have hrel : p k - p w = -(z.re - 1) • (p u - p w) := by
    rw [show p k - p w = (p k - p u) - (p w - p u) by abel, hpoint]
    module
  exact hull_extreme_not_opposite_ray p hp hw huw.symm (z.re - 1) ht hrel

/-- A point strictly beyond an extreme hull vertex has strictly negative
imaginary normalized coordinate whenever it lies in the supporting lower
half-plane. -/
theorem hull_extreme_normalized_beyond_im_neg {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {u w k : Fin n} (huw : u ≠ w) (hw : w ∈ hullVertexIndices p)
    (hre : 1 < (edgeCoordinate (p u) (p w) (p k)).re)
    (him : (edgeCoordinate (p u) (p w) (p k)).im ≤ 0) :
    (edgeCoordinate (p u) (p w) (p k)).im < 0 := by
  exact lt_of_le_of_ne him (fun heq =>
    hull_extreme_no_normalized_beyond p hp huw hw heq hre)

end Erdos957
