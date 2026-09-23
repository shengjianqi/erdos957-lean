import ExtremeSubsets
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith

/-! Strict support at the vertices of a finite planar convex hull. -/

namespace Erdos957

/-- An extreme point of a finite point set can be strictly separated from
the convex hull of all the other points. -/
theorem hull_extreme_strict_support {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (i : Fin n)
    (hext : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ) :
    ∃ f : Point →L[ℝ] ℝ, ∀ j : Fin n, j ≠ i → f (p j) < f (p i) := by
  let S : Set (Fin n) := {i}ᶜ
  have hi : i ∉ S := by simp [S]
  have hnot : p i ∉ convexHull ℝ (p '' S) :=
    extreme_not_mem_convexHull_image p hp i hext S hi
  have hfinite : (p '' S).Finite := (Set.toFinite S).image p
  have hclosed : IsClosed (convexHull ℝ (p '' S)) :=
    hfinite.isClosed_convexHull (𝕜 := ℝ)
  obtain ⟨f, c, hother, hself⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (p '' S)) hclosed hnot
  refine ⟨f, ?_⟩
  intro j hji
  have hj : p j ∈ convexHull ℝ (p '' S) :=
    subset_convexHull ℝ (p '' S) ⟨j, by simpa [S] using hji, rfl⟩
  exact (hother (p j) hj).trans hself

/-- At an extreme point of a configuration with at least two points, a
nonzero vector points strictly inward toward every other point. -/
theorem hull_extreme_inward_normal {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) (i : Fin n)
    (hext : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ) :
    ∃ axis : Point, axis ≠ 0 ∧
      ∀ j : Fin n, j ≠ i → 0 < inner ℝ axis (p j - p i) := by
  obtain ⟨f, hf⟩ := hull_extreme_strict_support p hp i hext
  let axis : Point := - (InnerProductSpace.toDual ℝ Point).symm f
  have hpos (j : Fin n) (hji : j ≠ i) :
      0 < inner ℝ axis (p j - p i) := by
    have hstrict := hf j hji
    simp only [axis, inner_neg_left, InnerProductSpace.toDual_symm_apply]
    rw [map_sub]
    linarith
  obtain ⟨ij, hij⟩ := pairs_nonempty hn
  have hneq : ij.1 ≠ ij.2 := ne_of_lt (mem_pairs_iff.mp hij)
  have haxis : axis ≠ 0 := by
    intro hzero
    by_cases hi : i = ij.1
    · have h := hpos ij.2 (by intro heq; exact hneq (hi.symm.trans heq.symm))
      rw [hzero, inner_zero_left] at h
      exact (lt_irrefl 0) h
    · have h := hpos ij.1 (by intro heq; exact hi heq.symm)
      rw [hzero, inner_zero_left] at h
      exact (lt_irrefl 0) h
  exact ⟨axis, haxis, hpos⟩

end Erdos957
