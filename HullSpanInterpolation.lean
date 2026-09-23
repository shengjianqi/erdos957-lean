import NormalizedReceiverInterior
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith

/-! Interpolate shallow hull points to fixed normalized horizontal coordinates. -/

namespace Erdos957

/-- Normalized edge coordinates scale linearly along a ray from its origin. -/
theorem edgeCoordinate_lineMap_self (u v x : Point) (t : ℝ) :
    edgeCoordinate u v (AffineMap.lineMap u x t) =
      t • edgeCoordinate u v x := by
  simp [edgeCoordinate, AffineMap.lineMap_apply_module', map_smul]
  ring

/-- A shallow hull point on each side can be pulled back along the segments
from `p u`, yielding normalized real coordinates exactly `-1` and `3`. -/
noncomputable def normalizedHullSpan_of_shallow_rays {n : ℕ}
    (p : Fin n → Point) (u w : Fin n) (A B : Point)
    (hA : A ∈ convexHull ℝ (Set.range p))
    (hB : B ∈ convexHull ℝ (Set.range p))
    (hAre : (edgeCoordinate (p u) (p w) A).re ≤ -1)
    (hAimlo : (edgeCoordinate (p u) (p w) A).re / 10 ≤
      (edgeCoordinate (p u) (p w) A).im)
    (hAimhi : (edgeCoordinate (p u) (p w) A).im ≤ 0)
    (hBre : 3 ≤ (edgeCoordinate (p u) (p w) B).re)
    (hBimlo : -(edgeCoordinate (p u) (p w) B).re / 30 ≤
      (edgeCoordinate (p u) (p w) B).im)
    (hBimhi : (edgeCoordinate (p u) (p w) B).im ≤ 0) :
    NormalizedHullSpan p u w := by
  let M := edgeCoordinate (p u) (p w)
  change (M A).re / 10 ≤ (M A).im at hAimlo
  change (M A).im ≤ 0 at hAimhi
  change -(M B).re / 30 ≤ (M B).im at hBimlo
  change (M B).im ≤ 0 at hBimhi
  let tA : ℝ := 1 / (-(M A).re)
  let tB : ℝ := 3 / (M B).re
  have hAneg : (M A).re < 0 := by linarith [hAre]
  have hBpos : 0 < (M B).re := by linarith [hBre]
  have htApos : 0 < tA := by
    dsimp [tA]
    exact div_pos (by norm_num) (by linarith)
  have htAone : tA ≤ 1 := by
    dsimp [tA]
    apply (div_le_iff₀ (by linarith : 0 < -(M A).re)).mpr
    linarith
  have htBpos : 0 < tB := by
    dsimp [tB]
    exact div_pos (by norm_num) hBpos
  have htBone : tB ≤ 1 := by
    dsimp [tB]
    apply (div_le_iff₀ hBpos).mpr
    linarith
  let L : Point := AffineMap.lineMap (p u) A tA
  let R : Point := AffineMap.lineMap (p u) B tB
  have hMLeft : M L = tA • M A :=
    edgeCoordinate_lineMap_self (p u) (p w) A tA
  have hMRight : M R = tB • M B :=
    edgeCoordinate_lineMap_self (p u) (p w) B tB
  have hLre : (M L).re = -1 := by
    rw [hMLeft, Complex.smul_re]
    dsimp [tA]
    field_simp [ne_of_lt hAneg]
  have hRre : (M R).re = 3 := by
    rw [hMRight, Complex.smul_re]
    dsimp [tB]
    field_simp [ne_of_gt hBpos]
  have hLimlo : -1 / 10 ≤ (M L).im := by
    rw [hMLeft, Complex.smul_im]
    simp only [smul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hAimlo htApos.le
    have hprod : tA * (M A).re = -1 := by
      simpa only [hMLeft, Complex.smul_re, smul_eq_mul] using hLre
    nlinarith only [hmul, hprod]
  have hLimhi : (M L).im ≤ 0 := by
    rw [hMLeft, Complex.smul_im]
    simp only [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos htApos.le hAimhi
  have hRimlo : -1 / 10 ≤ (M R).im := by
    rw [hMRight, Complex.smul_im]
    simp only [smul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left hBimlo htBpos.le
    have hprod : tB * (M B).re = 3 := by
      simpa only [hMRight, Complex.smul_re, smul_eq_mul] using hRre
    nlinarith only [hmul, hprod]
  have hRimhi : (M R).im ≤ 0 := by
    rw [hMRight, Complex.smul_im]
    simp only [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos htBpos.le hBimhi
  have hu : p u ∈ convexHull ℝ (Set.range p) :=
    subset_convexHull ℝ _ (Set.mem_range_self u)
  have hLmem : L ∈ convexHull ℝ (Set.range p) :=
    (convex_convexHull ℝ (Set.range p)).segment_subset hu hA
      (lineMap_mem_segment ℝ (p u) A ⟨htApos.le, htAone⟩)
  have hRmem : R ∈ convexHull ℝ (Set.range p) :=
    (convex_convexHull ℝ (Set.range p)).segment_subset hu hB
      (lineMap_mem_segment ℝ (p u) B ⟨htBpos.le, htBone⟩)
  exact ⟨L, R, hLmem, hRmem, hLre.le, hRre.ge,
    ⟨by simpa only [neg_div] using hLimlo, hLimhi⟩,
    ⟨by simpa only [neg_div] using hRimlo, hRimhi⟩⟩

end Erdos957
