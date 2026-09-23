import SixCentralNeighbor
import CentralAntipodes
import LargeScaleReduction
import SixNeighborDistances
import TightFlatChord

/-! Diameter endpoints cannot occupy opposite vertices of a degree-six
nearest-neighbor hexagon when the configuration is sufficiently large. -/

namespace Erdos957

/-- Exclude antipodal diameter neighbors using their forced central
directions and the actual large-configuration diameter bound. -/
theorem degree_six_diameter_neighbors_not_antipodal {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {u w q : Fin n}
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (hqdegree : (nearestGraph p).degree q = 6) :
    p u + p w ≠ 2 • p q := by
  intro hmid
  have hn2 : 2 ≤ n := by omega
  obtain ⟨j, huj⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  obtain ⟨k, hwk⟩ := (mem_diameterEndpoints_iff_exists_adj p w).mp hw
  obtain ⟨hulo, huhi⟩ := degree_six_neighbor_central_angles p hn2 hp huj hqu.symm hqdegree
  obtain ⟨hwlo, hwhi⟩ := degree_six_neighbor_central_angles p hn2 hp hwk hqw.symm hqdegree
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn2
  obtain ⟨kl, hmax⟩ := exists_max_pair p hn2
  have hscale : 10 * pairDist p ij < dist (p u) (p j) := by
    rw [(diameterGraph_adj_iff_dist_eq p hp hmax u j).mp huj]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact no_two_central_antipodes_at_large_scale p hn2 hp hmin huj hwk
    hqu.symm hqw.symm hmid hulo huhi hwlo hwhi hscale

/-- Distinct diameter endpoints adjacent to one degree-six center have
distance at most `1.9` minimum lengths in a large configuration. -/
theorem degree_six_diameter_neighbors_dist_le {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {u w q : Fin n}
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (hqdegree : (nearestGraph p).degree q = 6) (huw : u ≠ w)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij) :
    dist (p u) (p w) ≤ (19 / 10 : ℝ) * pairDist p ij :=
  degree_six_nonantipodal_neighbor_dist_le p (by omega) hp hqdegree hqu hqw huw
    (degree_six_diameter_neighbors_not_antipodal p hp hn hu hw hqu hqw hqdegree)
    ij hmin

/-- Even without assuming a nearest edge between the two endpoints, a
degree-six shared center is impossible at either local two-step position. -/
theorem tight_flat_two_step_no_shared_six {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (w : Fin n) (hw : w ∈ diameterEndpoints p)
    (hwhere : w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1)) :
    ¬ ∃ q, (nearestGraph p).degree q = 6 ∧
      (nearestGraph p).Adj q (v i) ∧ (nearestGraph p).Adj q w := by
  have hb := tight_flat_hull_chord_bounds p hp v hv hh ij hmin i hpos hgood
  have hr := pairDist_pos p hp hmin.1
  have hbound : (198 / 100 : ℝ) * pairDist p ij ≤ dist (p (v i)) (p w) := by
    rcases hwhere with rfl | rfl
    · exact hb.1
    · exact hb.2.2.1
  have huw : v i ≠ w := by
    intro heq
    rw [heq, dist_self] at hbound
    linarith
  rintro ⟨q, hqdegree, hqu, hqw⟩
  have hupper := degree_six_diameter_neighbors_dist_le p hp hn hu hw
    hqu hqw hqdegree huw ij hmin
  linarith

end Erdos957
