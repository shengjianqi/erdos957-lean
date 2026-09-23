import PlanarDirections
import PlanarOrientation
import DiameterHull

/-! Reflection of planar configurations across the real coordinate axis. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Reflection in the first coordinate axis, expressed through complex conjugation. -/
noncomputable def planeReflection : Point ≃ₗᵢ[ℝ] Point :=
  (pointToComplex.trans Complex.conjLIE).trans pointToComplex.symm

@[simp]
theorem pointToComplex_planeReflection (x : Point) :
    pointToComplex (planeReflection x) = conj (pointToComplex x) := by
  simp [planeReflection]

@[simp]
theorem planeReflection_apply_zero (x : Point) : planeReflection x 0 = x 0 := by
  have h := congrArg Complex.re (pointToComplex_planeReflection x)
  simpa [pointToComplex, Complex.orthonormalBasisOneI_repr_symm_apply] using h

@[simp]
theorem planeReflection_apply_one (x : Point) : planeReflection x 1 = -x 1 := by
  have h := congrArg Complex.im (pointToComplex_planeReflection x)
  simpa [pointToComplex, Complex.orthonormalBasisOneI_repr_symm_apply] using h

@[simp]
theorem turn_planeReflection (a b c : Point) :
    turn (planeReflection a) (planeReflection b) (planeReflection c) =
      -turn a b c := by
  simp only [turn, planeReflection_apply_zero, planeReflection_apply_one]
  ring

@[simp]
theorem planeReflection_planeReflection (x : Point) :
    planeReflection (planeReflection x) = x := by
  apply pointToComplex.injective
  simp

/-- Reflection preserves the indices of actual convex hull vertices. -/
theorem hullVertexIndices_planeReflection {n : ℕ} (p : Fin n → Point) :
    hullVertexIndices (fun i => planeReflection (p i)) = hullVertexIndices p := by
  classical
  have hrange : Set.range (fun i => planeReflection (p i)) =
      planeReflection '' Set.range p := by
    ext x
    simp only [Set.mem_range, Set.mem_image]
    aesop
  have hhull : convexHull ℝ (Set.range (fun i => planeReflection (p i))) =
      planeReflection '' convexHull ℝ (Set.range p) := by
    rw [hrange]
    exact (planeReflection.toLinearEquiv.toLinearMap.image_convexHull (Set.range p)).symm
  have hext : (convexHull ℝ (Set.range (fun i => planeReflection (p i)))).extremePoints ℝ =
      planeReflection '' (convexHull ℝ (Set.range p)).extremePoints ℝ := by
    rw [hhull]
    exact (image_extremePoints planeReflection.toLinearEquiv _).symm
  ext i
  simp only [hullVertexIndices, Finset.mem_filter, Finset.mem_univ, true_and, hext]
  exact planeReflection.injective.mem_set_image

end Erdos957
