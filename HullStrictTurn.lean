import HullGeneration
import PlanarOrientation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Between
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Distinct extreme points of a planar finite convex hull are never collinear. -/

namespace Erdos957

private theorem collinear_of_turn_eq_zero (a b q : Point)
    (hab : a ≠ b) (hturn : turn a b q = 0) :
    Collinear ℝ ({a, b, q} : Set Point) := by
  have hcoord : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : a 0 = b 0 := by linarith [h.1]
    have h1 : a 1 = b 1 := by linarith [h.2]
    apply hab
    ext k
    fin_cases k
    · simpa using h0
    · simpa using h1
  have hline : q ∈ line[ℝ, a, b] := by
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    rcases hcoord with h0 | h1
    · refine ⟨(q 0 - a 0) / (b 0 - a 0), ?_⟩
      ext k
      fin_cases k
      · change ((q 0 - a 0) / (b 0 - a 0)) * (b 0 - a 0) + a 0 = q 0
        field_simp
        ring
      · change ((q 0 - a 0) / (b 0 - a 0)) * (b 1 - a 1) + a 1 = q 1
        field_simp
        simp only [turn] at hturn
        nlinarith
    · refine ⟨(q 1 - a 1) / (b 1 - a 1), ?_⟩
      ext k
      fin_cases k
      · change ((q 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0) + a 0 = q 0
        field_simp
        simp only [turn] at hturn
        nlinarith
      · change ((q 1 - a 1) / (b 1 - a 1)) * (b 1 - a 1) + a 1 = q 1
        field_simp
        ring
  convert collinear_insert_of_mem_affineSpan_pair hline using 1
  ext x
  simp [or_comm, or_left_comm]

/-- Three different indexed extreme points cannot be collinear. -/
theorem hull_extreme_triple_not_collinear {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {i j k : Fin n}
    (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hj : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hk : p k ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    ¬ Collinear ℝ ({p i, p j, p k} : Set Point) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hijk | hjki | hkij
  · have hseg : p j ∈ segment ℝ (p i) (p k) := hijk.mem_segment
    rcases (mem_extremePoints_iff_forall_segment.mp hj).2
        (p i) hi.1 (p k) hk.1 hseg with h | h
    · exact hij (hp h)
    · exact hjk (hp h.symm)
  · have hseg : p k ∈ segment ℝ (p j) (p i) := hjki.mem_segment
    rcases (mem_extremePoints_iff_forall_segment.mp hk).2
        (p j) hj.1 (p i) hi.1 hseg with h | h
    · exact hjk (hp h)
    · exact hki (hp h.symm)
  · have hseg : p i ∈ segment ℝ (p k) (p j) := hkij.mem_segment
    rcases (mem_extremePoints_iff_forall_segment.mp hi).2
        (p k) hk.1 (p j) hj.1 hseg with h | h
    · exact hki (hp h)
    · exact hij (hp h.symm)

/-- Every third hull vertex lies strictly to the left of a supporting chord
oriented so that the whole configuration lies to its left. -/
theorem supporting_edge_strict {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {i j k : Fin n}
    (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hj : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hk : p k ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hsupport : ∀ l : Fin n, 0 ≤ turn (p i) (p j) (p l)) :
    0 < turn (p i) (p j) (p k) := by
  have hne : turn (p i) (p j) (p k) ≠ 0 := by
    intro hzero
    have hcol := collinear_of_turn_eq_zero (p i) (p j) (p k)
      (hp.ne hij) hzero
    exact hull_extreme_triple_not_collinear p hp hi hj hk hij hkj.symm hki hcol
  exact lt_of_le_of_ne (hsupport k) (Ne.symm hne)

end Erdos957
