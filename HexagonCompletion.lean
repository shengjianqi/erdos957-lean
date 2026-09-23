import SixNeighborStructure
import EquilateralRhombus

/-! Complete a given equilateral triangle along an edge incident to a degree-six vertex. -/

namespace Erdos957

theorem degree_six_triangle_completion {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) {u j a : Fin n}
    (hdeg : (nearestGraph p).degree u = 6)
    (huj : (nearestGraph p).Adj u j)
    (hua : (nearestGraph p).Adj u a)
    (hja : (nearestGraph p).Adj j a) :
    ∃ b : Fin n, b ≠ a ∧
      (nearestGraph p).Adj u b ∧ (nearestGraph p).Adj j b ∧
      p a + p b = p u + p j := by
  obtain ⟨a₀, b₀, hab, hua₀, hja₀, hub₀, hjb₀⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp hdeg huj
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have huj_dist : dist (p u) (p j) = r := nearestGraph_adj_dist_eq p hmin huj
  have hua_dist : dist (p u) (p a) = r := nearestGraph_adj_dist_eq p hmin hua
  have hja_dist : dist (p j) (p a) = r := nearestGraph_adj_dist_eq p hmin hja
  have hua₀_dist : dist (p u) (p a₀) = r := nearestGraph_adj_dist_eq p hmin hua₀
  have hja₀_dist : dist (p j) (p a₀) = r := nearestGraph_adj_dist_eq p hmin hja₀
  have hub₀_dist : dist (p u) (p b₀) = r := nearestGraph_adj_dist_eq p hmin hub₀
  have hjb₀_dist : dist (p j) (p b₀) = r := nearestGraph_adj_dist_eq p hmin hjb₀
  have hcircle : p a = p a₀ ∨ p a = p b₀ := by
    exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (by simp [Point]) (fun h => huj.ne (hp h)) (fun h => hab (hp h))
      (by simpa only [dist_comm] using hua₀_dist)
      (by simpa only [dist_comm] using hub₀_dist)
      (by simpa only [dist_comm] using hua_dist)
      (by simpa only [dist_comm] using hja₀_dist)
      (by simpa only [dist_comm] using hjb₀_dist)
      (by simpa only [dist_comm] using hja_dist)
  have hrob : p a₀ + p b₀ = p u + p j := by
    exact equilateral_rhombus (p u) (p j) (p a₀) (p b₀) r hr
      huj_dist hua₀_dist hja₀_dist hub₀_dist hjb₀_dist
      (fun h => hab (hp h))
  rcases hcircle with ha₀ | hb₀
  · have ha : a = a₀ := hp ha₀
    subst a
    exact ⟨b₀, hab.symm, hub₀, hjb₀, hrob⟩
  · have ha : a = b₀ := hp hb₀
    subst a
    exact ⟨a₀, hab, hua₀, hja₀, by simpa only [add_comm] using hrob⟩

end Erdos957
