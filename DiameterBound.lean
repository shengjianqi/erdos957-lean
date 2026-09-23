import DiameterIntersection
import DiameterSelector
import GraphSelectorBound

/-!
The planar diameter graph bound, using a choice of a leftmost edge at each
diameter endpoint. If an edge were selected at neither endpoint, the two
selected edges would be disjoint, contrary to the diameter intersection
theorem.
-/

namespace Erdos957

/-- The number of maximum-distance pairs is at most the number of points
incident to such pairs. -/
theorem sMax_le_diameterEndpointCount {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) :
    sMax p ≤ diameterEndpointCount p := by
  classical
  have hchoose : ∀ u : Fin n, ∃ v : Fin n,
      u ∈ diameterEndpoints p →
        (diameterGraph p).Adj u v ∧
        ∀ w, (diameterGraph p).Adj u w → w ≠ v →
          0 < turn (p u) (p w) (p v) := by
    intro u
    by_cases hu : u ∈ diameterEndpoints p
    · obtain ⟨v, hv⟩ := exists_leftmost_diameter_neighbor p hp u hu
      exact ⟨v, fun _ => hv⟩
    · exact ⟨u, fun h => False.elim (hu h)⟩
  choose f hf using hchoose
  rw [sMax_eq_card_edgeFinset]
  apply card_edges_le_of_endpoint_selection (diameterGraph p) (diameterEndpoints p) f
  intro u v huv
  have hu : u ∈ diameterEndpoints p :=
    (mem_diameterEndpoints_iff_exists_adj p u).mpr ⟨v, huv⟩
  have hv : v ∈ diameterEndpoints p :=
    (mem_diameterEndpoints_iff_exists_adj p v).mpr ⟨u, huv.symm⟩
  by_cases hfu : f u = v
  · exact Or.inl ⟨hu, hfu⟩
  by_cases hfv : f v = u
  · exact Or.inr ⟨hv, hfv⟩
  have hu_choice := hf u hu
  have hv_choice := hf v hv
  have hdisjoint := segments_disjoint_of_opposite_left_turns
    (hu_choice.2 v huv (Ne.symm hfu))
    (hv_choice.2 u huv.symm (Ne.symm hfv))
  obtain ⟨x, hxu, hxv⟩ :=
    diameterGraph_segments_intersect p hp hu_choice.1 hv_choice.1
  exact False.elim (Set.disjoint_left.mp hdisjoint hxu hxv)

/-- In particular, at most `n` unordered pairs realize the diameter. -/
theorem sMax_le_card {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) : sMax p ≤ n :=
  (sMax_le_diameterEndpointCount p hp).trans (diameterEndpointCount_le p)

end Erdos957
