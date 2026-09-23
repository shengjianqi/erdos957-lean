import DiameterGraph
import DiameterExtreme
import ExtremeSubsets
import PlanarRadon
import DiameterIntersectionMetric
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Any two diameter segments of a finite planar configuration intersect. -/

namespace Erdos957

/-- Two maximum-distance pairs of distinct planar points determine
intersecting closed segments, including when they share an endpoint. -/
theorem isMaxPair_segments_intersect {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {ij kl : Fin n × Fin n}
    (hij : isMaxPair p ij) (hkl : isMaxPair p kl) :
    (segment ℝ (p ij.1) (p ij.2) ∩
      segment ℝ (p kl.1) (p kl.2)).Nonempty := by
  classical
  by_cases hac : ij.1 = kl.1
  · exact ⟨p ij.1, left_mem_segment ℝ _ _, by
      simpa only [hac] using left_mem_segment ℝ (p kl.1) (p kl.2)⟩
  by_cases had : ij.1 = kl.2
  · exact ⟨p ij.1, left_mem_segment ℝ _ _, by
      simpa only [had] using right_mem_segment ℝ (p kl.1) (p kl.2)⟩
  by_cases hbc : ij.2 = kl.1
  · exact ⟨p ij.2, right_mem_segment ℝ _ _, by
      simpa only [hbc] using left_mem_segment ℝ (p kl.1) (p kl.2)⟩
  by_cases hbd : ij.2 = kl.2
  · exact ⟨p ij.2, right_mem_segment ℝ _ _, by
      simpa only [hbd] using right_mem_segment ℝ (p kl.1) (p kl.2)⟩
  have hab : ij.1 ≠ ij.2 := ne_of_lt (mem_pairs_iff.mp hij.1)
  have hcd : kl.1 ≠ kl.2 := ne_of_lt (mem_pairs_iff.mp hkl.1)
  let f : Fin 4 → Fin n := ![ij.1, ij.2, kl.1, kl.2]
  have hf : Function.Injective f := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let q : Fin 4 → Point := p ∘ f
  have hq : Function.Injective q := hp.comp hf
  have hvertices₁ := isMaxPair_endpoints_extreme p hp hij
  have hvertices₂ := isMaxPair_endpoints_extreme p hp hkl
  have hext : ∀ i, q i ∈ (convexHull ℝ (Set.range q)).extremePoints ℝ := by
    intro i
    apply extreme_in_subfamily p f i
    fin_cases i
    · exact hvertices₁.1
    · exact hvertices₁.2
    · exact hvertices₂.1
    · exact hvertices₂.2
  rcases four_extreme_points_have_crossing q hq hext with hcross | hcross | hcross
  · exact hcross
  · obtain ⟨x, hx₁, hx₂⟩ := hcross
    exact ⟨x, diameter_intersection_of_cross_intersection
      (p ij.1) (p ij.2) (p kl.1) (p kl.2) x (pairDist p ij)
      rfl (isMaxPair_pairDist_eq p hkl hij)
      (isMaxPair_dist_le p hij ij.1 kl.1)
      (isMaxPair_dist_le p hij ij.2 kl.2) hx₁ hx₂⟩
  · obtain ⟨x, hx₁, hx₂⟩ := hcross
    have heq : dist (p kl.2) (p kl.1) = pairDist p ij := by
      rw [dist_comm]
      exact isMaxPair_pairDist_eq p hkl hij
    have hmeet := diameter_intersection_of_cross_intersection
      (p ij.1) (p ij.2) (p kl.2) (p kl.1) x (pairDist p ij)
      rfl heq (isMaxPair_dist_le p hij ij.1 kl.2)
      (isMaxPair_dist_le p hij ij.2 kl.1) hx₁ hx₂
    exact ⟨x, hmeet.1, by rw [segment_symm]; exact hmeet.2⟩

/-- Every two edges of the diameter graph meet as closed planar segments. -/
theorem diameterGraph_segments_intersect {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {u v s t : Fin n}
    (huv : (diameterGraph p).Adj u v) (hst : (diameterGraph p).Adj s t) :
    (segment ℝ (p u) (p v) ∩ segment ℝ (p s) (p t)).Nonempty := by
  rcases (diameterGraph_adj_iff p u v).mp huv with huv | hvu
  · rcases (diameterGraph_adj_iff p s t).mp hst with hst | hts
    · exact isMaxPair_segments_intersect p hp (ij := (u, v)) (kl := (s, t)) huv hst
    · rw [segment_symm ℝ (p s) (p t)]
      exact isMaxPair_segments_intersect p hp (ij := (u, v)) (kl := (t, s)) huv hts
  · rcases (diameterGraph_adj_iff p s t).mp hst with hst | hts
    · rw [segment_symm ℝ (p u) (p v)]
      exact isMaxPair_segments_intersect p hp (ij := (v, u)) (kl := (s, t)) hvu hst
    · rw [segment_symm ℝ (p u) (p v), segment_symm ℝ (p s) (p t)]
      exact isMaxPair_segments_intersect p hp (ij := (v, u)) (kl := (t, s)) hvu hts

end Erdos957
