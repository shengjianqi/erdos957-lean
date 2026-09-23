import BoundaryNeighborOrder
import CentralCommonNeighbors
import BoundarySixNeighbors

/-! At a diameter endpoint, any degree-six nearest neighbor occupies the
unique central direction among the endpoint's three nearest neighbors. -/

namespace Erdos957

/-- A degree-six nearest neighbor of a diameter endpoint is its unique
central nearest neighbor for the direction of every diameter partner. -/
theorem degree_six_neighbor_central_angles {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j q : Fin n}
    (hdiam : (diameterGraph p).Adj u j)
    (huq : (nearestGraph p).Adj u q)
    (hqdegree : (nearestGraph p).degree q = 6) :
    -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p q) ∧
      halfplaneArg (p u) (p j - p u) (p q) < Real.pi / 6 := by
  classical
  have hu : u ∈ diameterEndpoints p :=
    (mem_diameterEndpoints_iff_exists_adj p u).mpr ⟨j, hdiam⟩
  have hudeg : (nearestGraph p).degree u = 3 :=
    diameterEndpoint_next_to_six_degree_eq_three p hn hp hu huq hqdegree
  obtain ⟨a, b, hab, hqa, hua, hqb, hub⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp hqdegree huq.symm
  have hsub : ({q, a, b} : Finset (Fin n)) ⊆
      (nearestGraph p).neighborFinset u := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr huq
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr hua
    · exact ((nearestGraph p).mem_neighborFinset u _).mpr hub
  have hcard : ({q, a, b} : Finset (Fin n)).card = 3 := by
    simp [hqa.ne, hqb.ne, hab]
  have hseteq : ({q, a, b} : Finset (Fin n)) =
      (nearestGraph p).neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [(nearestGraph p).card_neighborFinset_eq_degree u, hudeg, hcard]
  obtain ⟨r, ⟨hur, hrlo, hrhi⟩, _hrunique⟩ :=
    degree_three_middle_neighbor_unique p hn hp hdiam hudeg
  have hrmem : r ∈ ({q, a, b} : Finset (Fin n)) := by
    rw [hseteq]
    exact ((nearestGraph p).mem_neighborFinset u r).mpr hur
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrmem
  have hrq : r = q := by
    rcases hrmem with hrq | hra | hrb
    · exact hrq
    · have hrqadj : (nearestGraph p).Adj r q := by
        simpa only [hra] using hqa.symm
      have hle := common_neighbor_degree_le_five_of_central
        p hn hp hdiam hur hrlo hrhi huq hrqadj
      omega
    · have hrqadj : (nearestGraph p).Adj r q := by
        simpa only [hrb] using hqb.symm
      have hle := common_neighbor_degree_le_five_of_central
        p hn hp hdiam hur hrlo hrhi huq hrqadj
      omega
  rw [hrq] at hrlo hrhi
  exact ⟨hrlo, hrhi⟩

end Erdos957
