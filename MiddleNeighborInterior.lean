import MiddleTriangle
import BoundaryNeighborOrder
import InteriorExclusion
import Mathlib.Tactic.Abel

/-! The middle of three nearest neighbors at a sufficiently long diameter
endpoint belongs to the interior of the full configuration hull. -/

namespace Erdos957

/-- The central nearest neighbor of a degree-three diameter endpoint is an
interior point whenever the diameter is more than twice the nearest distance.
The two outer nearest neighbors and the diameter partner witness an open
triangle containing it. -/
theorem diameter_degree_three_middle_neighbor_mem_interior {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j)) :
    ∃ k : Fin n, (nearestGraph p).Adj u k ∧
      -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p k) ∧
      halfplaneArg (p u) (p j - p u) (p k) < Real.pi / 6 ∧
      p k ∈ interior (convexHull ℝ (Set.range p)) := by
  obtain ⟨v, _hvinj, _hrange, hadj, _hmono, hgap01, hgap12, hβlo, hβhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp hdiam hdeg
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have ha : dist (p u) (p (v 0)) = r :=
    nearestGraph_adj_dist_eq p hmin (hadj 0)
  have hb : dist (p u) (p (v 1)) = r :=
    nearestGraph_adj_dist_eq p hmin (hadj 1)
  have hc : dist (p u) (p (v 2)) = r :=
    nearestGraph_adj_dist_eq p hmin (hadj 2)
  have hhalf0 : 0 < inner ℝ (p j - p u) (p (v 0) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj (hadj 0))
  have hhalf2 : 0 < inner ℝ (p j - p u) (p (v 2) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj (hadj 2))
  have hα : -Real.pi / 2 < halfplaneArg (p u) (p j - p u) (p (v 0)) :=
    (halfplaneArg_mem_Ioo hhalf0).1
  have hγ : halfplaneArg (p u) (p j - p u) (p (v 2)) < Real.pi / 2 :=
    (halfplaneArg_mem_Ioo hhalf2).2
  have hlarge : 2 * r < ‖p j - p u‖ := by
    simpa only [r, dist_eq_norm, norm_sub_rev] using hscale
  have hinside : p (v 1) ∈ interior
      (convexHull ℝ ({p (v 0), p u + (p j - p u), p (v 2)} : Set Point)) :=
    circle_middle_mem_interior_triangle (p u) (p j - p u)
      (p (v 0)) (p (v 1)) (p (v 2)) r hr ha hb hc
      hα hγ hgap01 hgap12 hlarge
  have htri :
      ({p (v 0), p u + (p j - p u), p (v 2)} : Set Point) ⊆ Set.range p := by
    have haxis : p u + (p j - p u) = p j := by abel
    intro z hz
    simp only [haxis, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · exact h ▸ Set.mem_range_self (v 0)
    · exact h ▸ Set.mem_range_self j
    · exact h ▸ Set.mem_range_self (v 2)
  refine ⟨v 1, hadj 1, hβlo, hβhi, ?_⟩
  exact interior_mono (convexHull_mono htri) hinside

/-- The central cone has a unique nearest neighbor, so every nearest
neighbor satisfying its angular bounds is the interior point above. -/
theorem diameter_degree_three_central_neighbor_mem_interior {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j))
    (k : Fin n) (hk : (nearestGraph p).Adj u k)
    (hklo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p k))
    (hkhi : halfplaneArg (p u) (p j - p u) (p k) < Real.pi / 6) :
    p k ∈ interior (convexHull ℝ (Set.range p)) := by
  obtain ⟨m, hm, hmlo, hmhi, hinside⟩ :=
    diameter_degree_three_middle_neighbor_mem_interior p hn hp hdiam hdeg ij hmin hscale
  obtain ⟨w, _hw, hunique⟩ :=
    degree_three_middle_neighbor_unique p hn hp hdiam hdeg
  have hkm : k = m :=
    (hunique k ⟨hk, hklo, hkhi⟩).trans
      (hunique m ⟨hm, hmlo, hmhi⟩).symm
  exact hkm ▸ hinside

/-- The middle nearest neighbor is available as a receiver outside the set
of diameter endpoints. -/
theorem diameter_degree_three_central_receiver_exists {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j)) :
    ∃ k : Fin n, (nearestGraph p).Adj u k ∧
      -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p k) ∧
      halfplaneArg (p u) (p j - p u) (p k) < Real.pi / 6 ∧
      k ∉ diameterEndpoints p := by
  obtain ⟨k, hk, hklo, hkhi, hinner⟩ :=
    diameter_degree_three_middle_neighbor_mem_interior p hn hp hdiam hdeg ij hmin hscale
  exact ⟨k, hk, hklo, hkhi, interior_not_diameterEndpoints p hp k hinner⟩

end Erdos957
