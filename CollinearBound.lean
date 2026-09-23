import DiameterHull
import DiameterBound
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith

/-! A collinear configuration has at most two extreme points. -/

namespace Erdos957

/-- Every point of a collinear finite configuration lies between the endpoints
of one of its diameter pairs. -/
theorem collinear_mem_diameter_segment {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p))
    {ij : Fin n × Fin n} (hmax : isMaxPair p ij) (k : Fin n) :
    p k ∈ segment ℝ (p ij.1) (p ij.2) := by
  have hij : ij.1 ≠ ij.2 := ne_of_lt (mem_pairs_iff.mp hmax.1)
  have hpij : p ij.1 ≠ p ij.2 := hp.ne hij
  have hD : 0 < dist (p ij.1) (p ij.2) := dist_pos.mpr hpij
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hcol.mem_affineSpan_of_mem_of_ne (Set.mem_range_self ij.1)
      (Set.mem_range_self ij.2) (Set.mem_range_self k) hpij)
  have hleft : |t| * dist (p ij.1) (p ij.2) ≤ dist (p ij.1) (p ij.2) := by
    have h := dist_le_of_isMaxPair p hmax ij.1 k
    rw [← ht, dist_left_lineMap] at h
    simpa only [pairDist, Real.norm_eq_abs] using h
  have hright : |1 - t| * dist (p ij.1) (p ij.2) ≤
      dist (p ij.1) (p ij.2) := by
    have h := dist_le_of_isMaxPair p hmax ij.2 k
    rw [← ht, dist_right_lineMap] at h
    simpa only [pairDist, Real.norm_eq_abs] using h
  have ht1 : |t| ≤ 1 :=
    (mul_le_mul_iff_left₀ hD).mp (by simpa only [one_mul] using hleft)
  have ht2 : |1 - t| ≤ 1 :=
    (mul_le_mul_iff_left₀ hD).mp (by simpa only [one_mul] using hright)
  have hinterval : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [abs_le.mp ht1, abs_le.mp ht2]
  rw [← ht]
  exact lineMap_mem_segment ℝ _ _ hinterval

/-- A collinear configuration has at most two convex-hull vertices. -/
theorem hullVertexCount_le_two_of_collinear {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p)) :
    hullVertexCount p ≤ 2 := by
  classical
  by_cases hn : 2 ≤ n
  · obtain ⟨ij, hmax⟩ := exists_max_pair p hn
    have hrange : Set.range p ⊆ segment ℝ (p ij.1) (p ij.2) := by
      rintro x ⟨k, rfl⟩
      exact collinear_mem_diameter_segment p hp hcol hmax k
    have hhull : convexHull ℝ (Set.range p) =
        segment ℝ (p ij.1) (p ij.2) := by
      apply Set.Subset.antisymm
      · exact convexHull_min hrange (convex_segment _ _)
      · exact segment_subset_convexHull
          (Set.mem_range_self ij.1) (Set.mem_range_self ij.2)
    have hsubset : hullVertexIndices p ⊆ ({ij.1, ij.2} : Finset (Fin n)) := by
      intro k hk
      have hext : p k ∈
          (segment ℝ (p ij.1) (p ij.2)).extremePoints ℝ := by
        simpa only [hullVertexIndices, Finset.mem_filter, Finset.mem_univ,
          true_and, hhull] using hk
      have hchoice := (mem_extremePoints_iff_forall_segment.mp hext).2
        (p ij.1) (by exact left_mem_segment ℝ _ _)
        (p ij.2) (by exact right_mem_segment ℝ _ _)
        (collinear_mem_diameter_segment p hp hcol hmax k)
      rcases hchoice with hka | hkb
      · simp [((hp hka).symm)]
      · simp [((hp hkb).symm)]
    have hcard := Finset.card_le_card hsubset
    have htwo : ({ij.1, ij.2} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    exact hcard.trans htwo
  · have hsmall : n ≤ 1 := by omega
    exact (hullVertexCount_le p).trans (by omega)

/-- In a collinear configuration, at most two vertices are diameter endpoints. -/
theorem diameterEndpointCount_le_two_of_collinear {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p)) :
    diameterEndpointCount p ≤ 2 :=
  (diameterEndpointCount_le_hullVertexCount p hp).trans
    (hullVertexCount_le_two_of_collinear p hp hcol)

/-- In a collinear configuration the maximum-distance unordered pair is
unique. -/
theorem collinear_isMaxPair_unique {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p))
    {ij kl : Fin n × Fin n} (hij : isMaxPair p ij)
    (hkl : isMaxPair p kl) : ij = kl := by
  have hrange : Set.range p ⊆ segment ℝ (p ij.1) (p ij.2) := by
    rintro x ⟨k, rfl⟩
    exact collinear_mem_diameter_segment p hp hcol hij k
  have hhull : convexHull ℝ (Set.range p) =
      segment ℝ (p ij.1) (p ij.2) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hrange (convex_segment _ _)
    · exact segment_subset_convexHull
        (Set.mem_range_self ij.1) (Set.mem_range_self ij.2)
  have hindex (k : Fin n)
      (hk : p k ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ) :
      k = ij.1 ∨ k = ij.2 := by
    rw [hhull] at hk
    have hchoice := (mem_extremePoints_iff_forall_segment.mp hk).2
      (p ij.1) (left_mem_segment ℝ _ _)
      (p ij.2) (right_mem_segment ℝ _ _)
      (collinear_mem_diameter_segment p hp hcol hij k)
    rcases hchoice with ha | hb
    · exact Or.inl (hp ha).symm
    · exact Or.inr (hp hb).symm
  obtain ⟨hkle, hkre⟩ := isMaxPair_endpoints_extreme p hp hkl
  have hl := hindex kl.1 hkle
  have hr := hindex kl.2 hkre
  have hklne : kl.1 ≠ kl.2 := ne_of_lt (mem_pairs_iff.mp hkl.1)
  have hijlt : ij.1 < ij.2 := mem_pairs_iff.mp hij.1
  have hkllt : kl.1 < kl.2 := mem_pairs_iff.mp hkl.1
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact False.elim (hklne (hl.trans hr.symm))
  · exact (Prod.ext hl hr).symm
  · have hrev : ij.2 < ij.1 := by simpa only [hl, hr] using hkllt
    exact False.elim (lt_asymm hijlt hrev)
  · exact False.elim (hklne (hl.trans hr.symm))

/-- There is at most one farthest pair in a collinear configuration. -/
theorem sMax_le_one_of_collinear {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p)) :
    sMax p ≤ 1 := by
  classical
  unfold sMax
  apply Finset.card_le_one.mpr
  intro ij hij kl hkl
  exact collinear_isMaxPair_unique p hp hcol
    (Finset.mem_filter.mp hij).2 (Finset.mem_filter.mp hkl).2

/-- Collinear configurations satisfy a stronger product estimate directly. -/
theorem collinear_product_bound {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p)) :
    sMin p * sMax p ≤ n ^ 2 := by
  classical
  have hmin : sMin p ≤ n * n := by
    calc
      sMin p = ((pairs n).filter (isMinPair p)).card := rfl
      _ ≤ (pairs n).card := Finset.card_filter_le _ _
      _ ≤ ((Finset.univ : Finset (Fin n)).product Finset.univ).card := by
        unfold pairs
        exact Finset.card_filter_le _ _
      _ = n * n := by simp
  have hmax := sMax_le_one_of_collinear p hp hcol
  have hprod := Nat.mul_le_mul_left (sMin p) hmax
  calc
    sMin p * sMax p ≤ sMin p := by simpa only [mul_one] using hprod
    _ ≤ n * n := hmin
    _ = n ^ 2 := by ring

/-- If the diameter-endpoint count is in the large regime, a collinear
configuration has at most six points. -/
theorem collinear_large_regime_card_le_six {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (hcol : Collinear ℝ (Set.range p))
    (hlarge : n ≤ 3 * diameterEndpointCount p) : n ≤ 6 := by
  have hd := diameterEndpointCount_le_two_of_collinear p hp hcol
  omega

end Erdos957
