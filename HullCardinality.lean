import HullGeneration
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! A noncollinear finite configuration has at least three hull vertices. -/

namespace Erdos957

private theorem collinear_image_of_card_le_two {n : ℕ}
    (p : Fin n → Point) (H : Finset (Fin n)) (hHcard : H.card ≤ 2) :
    Collinear ℝ (p '' (H : Set (Fin n))) := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨i, hi⟩ := hH
    let E := H.erase i
    have hEcard : E.card ≤ 1 := by
      dsimp [E]
      rw [Finset.card_erase_of_mem hi]
      omega
    by_cases hE : E.Nonempty
    · obtain ⟨j, hj⟩ := hE
      have hsubset : H ⊆ {i, j} := by
        intro k hk
        by_cases hki : k = i
        · simp [hki]
        · have hke : k ∈ E := Finset.mem_erase.mpr ⟨hki, hk⟩
          have hkj := (Finset.card_le_one.mp hEcard) k hke j hj
          simp [hkj]
      have himage : p '' (H : Set (Fin n)) ⊆ ({p i, p j} : Set Point) := by
        rintro x ⟨k, hk, rfl⟩
        have hpair := hsubset hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
        rcases hpair with h | h <;> simp [h]
      exact (collinear_pair ℝ (p i) (p j)).subset himage
    · have hsubset : H ⊆ {i} := by
        intro k hk
        by_cases hki : k = i
        · simp [hki]
        · exact False.elim (hE ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩⟩)
      have himage : p '' (H : Set (Fin n)) ⊆ ({p i} : Set Point) := by
        rintro x ⟨k, hk, rfl⟩
        have hki : k = i := Finset.mem_singleton.mp (hsubset hk)
        simp [hki]
      exact (collinear_singleton ℝ (p i)).subset himage
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simpa [hEmpty] using (collinear_empty ℝ Point)

/-- If a finite convex hull has at most two indexed extreme points, all
original points are collinear. No injectivity assumption is needed. -/
theorem collinear_of_hullVertexCount_le_two {n : ℕ} (p : Fin n → Point)
    (hcount : hullVertexCount p ≤ 2) : Collinear ℝ (Set.range p) := by
  let H := hullVertexIndices p
  have hHcard : H.card ≤ 2 := hcount
  have hcolH : Collinear ℝ (p '' (H : Set (Fin n))) :=
    collinear_image_of_card_le_two p H hHcard
  have hspan : affineSpan ℝ (Set.range p) =
      affineSpan ℝ (p '' (H : Set (Fin n))) := by
    calc
      affineSpan ℝ (Set.range p) = affineSpan ℝ (convexHull ℝ (Set.range p)) :=
        (affineSpan_convexHull _).symm
      _ = affineSpan ℝ (convexHull ℝ (p '' (H : Set (Fin n)))) := by
        rw [convexHull_image_hullVertexIndices p]
      _ = affineSpan ℝ (p '' (H : Set (Fin n))) := affineSpan_convexHull _
  have hvspan : vectorSpan ℝ (Set.range p) =
      vectorSpan ℝ (p '' (H : Set (Fin n))) := by
    have h := congrArg AffineSubspace.direction hspan
    simpa only [direction_affineSpan] using h
  change Module.rank ℝ (vectorSpan ℝ (Set.range p)) ≤ 1
  rw [hvspan]
  exact hcolH

/-- A noncollinear finite configuration has at least three indexed extreme
points of its convex hull. -/
theorem hullVertexCount_ge_three_of_noncollinear {n : ℕ} (p : Fin n → Point)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    3 ≤ hullVertexCount p := by
  by_contra h
  have hle : hullVertexCount p ≤ 2 := by omega
  exact hnot (collinear_of_hullVertexCount_le_two p hle)

end Erdos957
