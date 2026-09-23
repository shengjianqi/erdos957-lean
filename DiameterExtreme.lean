import Foundations
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.Strict.Extreme

/-!
Endpoints of a diameter of a finite planar set are vertices of its convex
hull.  The proof places the entire hull inside a Euclidean closed ball whose
boundary contains the endpoint, then uses strict convexity of that ball.
-/

namespace Erdos957

/-- A point attaining the maximum distance from a fixed center over a set is
an extreme point of the set's convex hull, provided that maximum is positive. -/
theorem farthest_point_extreme
    (A : Set Point) (x y : Point) (r : ℝ)
    (hx : x ∈ A) (hr : 0 < r)
    (hbound : ∀ z ∈ A, dist z y ≤ r)
    (hxy : dist x y = r) :
    x ∈ (convexHull ℝ A).extremePoints ℝ := by
  have hA_ball : A ⊆ Metric.closedBall y r := by
    intro z hz
    exact Metric.mem_closedBall.mpr (hbound z hz)
  have hHull_ball : convexHull ℝ A ⊆ Metric.closedBall y r :=
    convexHull_min hA_ball (convex_closedBall y r)
  have hxHull : x ∈ convexHull ℝ A := subset_convexHull ℝ A hx
  have hxSphere : x ∈ Metric.sphere y r := Metric.mem_sphere.mpr hxy
  have hxExtremeBall : x ∈ (Metric.closedBall y r).extremePoints ℝ :=
    StrictConvexSpace.sphere_subset_extremePoints_closedBall y hr.ne' hxSphere
  exact inter_extremePoints_subset_extremePoints_of_subset hHull_ball
    ⟨hxHull, hxExtremeBall⟩

/-- Every distance in a finite configuration is bounded by a chosen diameter. -/
theorem dist_le_of_isMaxPair {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hmax : isMaxPair p ij)
    (k l : Fin n) :
    dist (p k) (p l) ≤ pairDist p ij := by
  by_cases hkl : k = l
  · subst l
    simpa only [dist_self, pairDist] using
      (dist_nonneg : (0 : ℝ) ≤ dist (p ij.1) (p ij.2))
  · rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact hmax.2 (k, l) (mem_pairs_iff.mpr hlt)
    · have h := hmax.2 (l, k) (mem_pairs_iff.mpr hgt)
      simpa only [pairDist, dist_comm] using h

/-- Both endpoints of a maximum-distance pair are extreme points of the
convex hull of a finite configuration of distinct plane points. -/
theorem isMaxPair_endpoints_extreme {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {ij : Fin n × Fin n}
    (hmax : isMaxPair p ij) :
    p ij.1 ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ ∧
    p ij.2 ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ := by
  have hr : 0 < pairDist p ij := pairDist_pos p hp hmax.1
  have hleft : p ij.1 ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ := by
    apply farthest_point_extreme (Set.range p) (p ij.1) (p ij.2)
      (pairDist p ij) ⟨ij.1, rfl⟩ hr
    · intro z hz
      obtain ⟨k, rfl⟩ := hz
      exact dist_le_of_isMaxPair p hmax k ij.2
    · rfl
  have hright : p ij.2 ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ := by
    apply farthest_point_extreme (Set.range p) (p ij.2) (p ij.1)
      (pairDist p ij) ⟨ij.2, rfl⟩ hr
    · intro z hz
      obtain ⟨k, rfl⟩ := hz
      exact dist_le_of_isMaxPair p hmax k ij.1
    · simp only [pairDist, dist_comm]
  exact ⟨hleft, hright⟩

end Erdos957
