import BoundaryDegree
import HexagonCompletion

/-! Local degree slack next to a diameter endpoint and a degree-six neighbor. -/

namespace Erdos957

/-- A diameter endpoint cannot be the midpoint of two other configuration
points, because both lie strictly inside its supporting half-plane. -/
theorem diameterEndpoint_not_midpoint {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {u j k : Fin n}
    (hu : u ∈ diameterEndpoints p) (huj : u ≠ j) (huk : u ≠ k) :
    p j + p k ≠ 2 • p u := by
  intro hmid
  obtain ⟨v, huv⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  have hj := diameter_neighbor_inner_pos_of_other p hp huv huj
  have hk := diameter_neighbor_inner_pos_of_other p hp huv huk
  have hsum : (p j - p u) + (p k - p u) = 0 := by
    calc
      (p j - p u) + (p k - p u) = p j + p k - 2 • p u := by
        rw [two_smul]
        abel
      _ = 0 := by rw [hmid]; simp
  have hzero : inner ℝ (p v - p u) (p j - p u) +
      inner ℝ (p v - p u) (p k - p u) = 0 := by
    rw [← inner_add_right, hsum, inner_zero_right]
  linarith

/-- If a diameter endpoint is adjacent to a degree-six closest-pair vertex,
each of their common closest-pair neighbors has degree at most five.
This supplies local receiving capacity used by the charging construction. -/
theorem common_neighbor_degree_le_five {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) {u v a : Fin n}
    (hu : u ∈ diameterEndpoints p)
    (huv : (nearestGraph p).Adj u v)
    (hvdegree : (nearestGraph p).degree v = 6)
    (hua : (nearestGraph p).Adj u a)
    (hva : (nearestGraph p).Adj v a) :
    (nearestGraph p).degree a ≤ 5 := by
  by_contra ha
  have hadegree : (nearestGraph p).degree a = 6 := by
    have hle := nearestGraph_degree_le_six p hn hp a
    omega
  obtain ⟨b, _hba, _hvb, hub, hbsum⟩ :=
    degree_six_triangle_completion p hn hp hvdegree huv.symm hva hua
  obtain ⟨w, _hwv, _haw, huw, hwsum⟩ :=
    degree_six_triangle_completion p hn hp hadegree hua.symm hva.symm huv
  have hmid : p b + p w = 2 • p u := by
    calc
      p b + p w = (p a + p b) + (p v + p w) - p a - p v := by abel
      _ = (p v + p u) + (p a + p u) - p a - p v := by rw [hbsum, hwsum]
      _ = 2 • p u := by rw [two_smul]; abel
  exact diameterEndpoint_not_midpoint p hp hu
    ((nearestGraph p).ne_of_adj hub) ((nearestGraph p).ne_of_adj huw) hmid

/-- A diameter endpoint next to a degree-six closest-pair vertex has degree
exactly three: the shared edge lies in two distinct equilateral triangles. -/
theorem diameterEndpoint_next_to_six_degree_eq_three {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u v : Fin n} (hu : u ∈ diameterEndpoints p)
    (huv : (nearestGraph p).Adj u v)
    (hvdegree : (nearestGraph p).degree v = 6) :
    (nearestGraph p).degree u = 3 := by
  classical
  obtain ⟨a, b, hab, hva, hua, hvb, hub⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp hvdegree huv.symm
  have hsub : ({v, a, b} : Finset (Fin n)) ⊆
      (nearestGraph p).neighborFinset u := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr huv
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr hua
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr hub
  have hcard : ({v, a, b} : Finset (Fin n)).card = 3 := by
    simp [hva.ne, hvb.ne, hab]
  have hge : 3 ≤ (nearestGraph p).degree u := by
    rw [← (nearestGraph p).card_neighborFinset_eq_degree u, ← hcard]
    exact Finset.card_le_card hsub
  exact le_antisymm
    (nearestGraph_degree_le_three_of_diameterEndpoint p hn hp u hu) hge

/-- The two common neighbors next to such a boundary edge each have at least
one unit of degree capacity below the universal degree bound six. -/
theorem diameterEndpoint_six_neighbor_common_degree_bounds {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u v : Fin n} (hu : u ∈ diameterEndpoints p)
    (huv : (nearestGraph p).Adj u v)
    (hvdegree : (nearestGraph p).degree v = 6) :
    ∃ a b : Fin n, a ≠ b ∧
      (nearestGraph p).Adj u a ∧ (nearestGraph p).Adj v a ∧
      (nearestGraph p).degree a ≤ 5 ∧
      (nearestGraph p).Adj u b ∧ (nearestGraph p).Adj v b ∧
      (nearestGraph p).degree b ≤ 5 := by
  obtain ⟨a, b, hab, hva, hua, hvb, hub⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp hvdegree huv.symm
  exact ⟨a, b, hab, hua, hva, common_neighbor_degree_le_five p hn hp hu huv hvdegree hua hva,
    hub, hvb, common_neighbor_degree_le_five p hn hp hu huv hvdegree hub hvb⟩

end Erdos957
