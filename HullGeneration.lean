import DiameterHull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology

/-! The vertices of a finite convex hull generate the entire hull. -/

namespace Erdos957

/-- A finite planar convex hull is the convex hull of its extreme points. -/
theorem convexHull_extremePoints_eq_of_finite (s : Set Point) (hs : s.Finite) :
    convexHull ℝ ((convexHull ℝ s).extremePoints ℝ) = convexHull ℝ s := by
  have hextfinite : ((convexHull ℝ s).extremePoints ℝ).Finite :=
    hs.subset extremePoints_convexHull_subset
  have hclosed : IsClosed (convexHull ℝ ((convexHull ℝ s).extremePoints ℝ)) :=
    hextfinite.isClosed_convexHull ℝ
  have hkm := closure_convexHull_extremePoints
    (hs.isCompact_convexHull ℝ) (convex_convexHull ℝ s)
  simpa only [hclosed.closure_eq] using hkm

/-- The image of the indexed hull vertices is exactly the set of hull extreme points. -/
theorem image_hullVertexIndices_eq_extremePoints {n : ℕ} (p : Fin n → Point) :
    p '' (hullVertexIndices p : Set (Fin n)) =
      (convexHull ℝ (Set.range p)).extremePoints ℝ := by
  classical
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro hy
    obtain ⟨i, rfl⟩ : p ⁻¹' {y} |>.Nonempty := by
      obtain ⟨i, rfl⟩ := extremePoints_convexHull_subset hy
      exact ⟨i, rfl⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩

/-- Every original point lies in the convex hull of the indexed extreme points. -/
theorem convexHull_image_hullVertexIndices {n : ℕ} (p : Fin n → Point) :
    convexHull ℝ (p '' (hullVertexIndices p : Set (Fin n))) =
      convexHull ℝ (Set.range p) := by
  rw [image_hullVertexIndices_eq_extremePoints]
  exact convexHull_extremePoints_eq_of_finite (Set.range p) (Set.finite_range p)

/-- An affine upper bound on all extreme points holds throughout the finite configuration. -/
theorem affine_le_of_hullVertexIndices_le {n : ℕ} (p : Fin n → Point)
    (L : Point →ᵃ[ℝ] ℝ) (M : ℝ)
    (hvertex : ∀ i ∈ hullVertexIndices p, L (p i) ≤ M) (j : Fin n) :
    L (p j) ≤ M := by
  have hsubset : p '' (hullVertexIndices p : Set (Fin n)) ⊆
      {x : Point | L x ≤ M} := by
    rintro x ⟨i, hi, rfl⟩
    exact hvertex i hi
  have hhull : convexHull ℝ (p '' (hullVertexIndices p : Set (Fin n))) ⊆
      {x : Point | L x ≤ M} :=
    convexHull_min hsubset ((convex_Iic M).affine_preimage L)
  apply hhull
  rw [convexHull_image_hullVertexIndices]
  exact subset_convexHull ℝ _ ⟨j, rfl⟩

/-- The linear-functional form of the extreme-point upper-bound principle. -/
theorem linear_le_of_hullVertexIndices_le {n : ℕ} (p : Fin n → Point)
    (L : Point →ₗ[ℝ] ℝ) (M : ℝ)
    (hvertex : ∀ i ∈ hullVertexIndices p, L (p i) ≤ M) (j : Fin n) :
    L (p j) ≤ M :=
  affine_le_of_hullVertexIndices_le p L.toAffineMap M hvertex j

end Erdos957
