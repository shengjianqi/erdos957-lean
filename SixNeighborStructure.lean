import SixCircleRigidity
import NearestMetric
import Antipodal
import Mathlib.Tactic.FinCases

/-! The regular hexagon forced by a degree-six closest-pair vertex. -/

namespace Erdos957

/-- A vertex with six closest-pair neighbors has a cyclic enumeration of
exactly those neighbors. Their directions increase by sixty degrees, and
successive neighbors are themselves connected by minimum-distance edges. -/
theorem nearestGraph_degree_six_regular {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) (u : Fin n)
    (hdegree : (nearestGraph p).degree u = 6) :
    ∃ v : Fin 6 → Fin n, Function.Injective v ∧
      (∀ j, (nearestGraph p).Adj u j ↔ ∃ k, v k = j) ∧
      (∀ k, (nearestGraph p).Adj (v k) (v (k + 1))) ∧
      (∀ k, directionArg (p u) (p (v k)) =
        directionArg (p u) (p (v 0)) + (k : ℝ) * (Real.pi / 3)) := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  let N := ((nearestGraph p).neighborFinset u).image p
  have hcard : N.card = 6 := by
    dsimp [N]
    rw [Finset.card_image_of_injective _ hp]
    exact ((nearestGraph p).card_neighborFinset_eq_degree u).trans hdegree
  have hradius : ∀ y ∈ N, dist (p u) y = r := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact nearestGraph_adj_dist_eq p hmin
      (((nearestGraph p).mem_neighborFinset u j).mp hj)
  have hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact isMinPair_le_dist p hmin (fun heq => hyz (congrArg p heq))
  obtain ⟨q, hqinj, hqrange, hqradius, hqargs, hqsides⟩ :=
    circle_six_regular N (p u) r hr hradius hsep hcard
  have hindices : ∀ k : Fin 6, ∃ j : Fin n,
      j ∈ (nearestGraph p).neighborFinset u ∧ p j = q k := by
    intro k
    have hqmem : q k ∈ N := by
      change q k ∈ (N : Set Point)
      rw [← hqrange]
      exact ⟨k, rfl⟩
    exact Finset.mem_image.mp hqmem
  choose v hv hvq using hindices
  have hvinj : Function.Injective v := by
    intro i j hij
    apply hqinj
    rw [← hvq i, ← hvq j, hij]
  have hcover : ∀ j, (nearestGraph p).Adj u j ↔ ∃ k, v k = j := by
    intro j
    constructor
    · intro hadj
      have hpj : p j ∈ (N : Set Point) := Finset.mem_image.mpr
        ⟨j, ((nearestGraph p).mem_neighborFinset u j).mpr hadj, rfl⟩
      rw [← hqrange] at hpj
      obtain ⟨k, hk⟩ := hpj
      exact ⟨k, hp ((hvq k).trans hk)⟩
    · rintro ⟨k, rfl⟩
      exact ((nearestGraph p).mem_neighborFinset u (v k)).mp (hv k)
  refine ⟨v, hvinj, hcover, ?_, ?_⟩
  · intro k
    apply (nearestGraph_adj_iff_dist_eq p hp hmin (v k) (v (k + 1))).mpr
    simpa only [hvq] using hqsides k
  · intro k
    simpa only [hvq] using hqargs k

/-- An edge incident to a degree-six vertex belongs to two distinct
equilateral triangles in the closest-pair graph. -/
theorem degree_six_edge_has_two_common_neighbors {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) {u j : Fin n}
    (hdegree : (nearestGraph p).degree u = 6)
    (huj : (nearestGraph p).Adj u j) :
    ∃ a b : Fin n, a ≠ b ∧
      (nearestGraph p).Adj u a ∧ (nearestGraph p).Adj j a ∧
      (nearestGraph p).Adj u b ∧ (nearestGraph p).Adj j b := by
  obtain ⟨v, hvinj, hcover, hcycle, _hargs⟩ :=
    nearestGraph_degree_six_regular p hn hp u hdegree
  obtain ⟨k, rfl⟩ := (hcover j).mp huj
  have hneq : (k + 1 : Fin 6) ≠ k + 5 := by
    fin_cases k <;> decide
  have hwrap : (k + 5 + 1 : Fin 6) = k := by
    fin_cases k <;> decide
  refine ⟨v (k + 1), v (k + 5), hvinj.ne hneq, ?_, hcycle k, ?_, ?_⟩
  · exact (hcover _).mpr ⟨k + 1, rfl⟩
  · exact (hcover _).mpr ⟨k + 5, rfl⟩
  · have h := (hcycle (k + 5)).symm
    simpa only [hwrap] using h

/-- In a degree-six closest-pair neighborhood, each neighbor has its
opposite point in the same neighborhood. -/
theorem degree_six_neighbor_has_antipode {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) {u j : Fin n}
    (hdegree : (nearestGraph p).degree u = 6)
    (huj : (nearestGraph p).Adj u j) :
    ∃ k : Fin n, (nearestGraph p).Adj u k ∧ k ≠ j ∧
      p j + p k = 2 • p u := by
  obtain ⟨v, hvinj, hcover, _hcycle, hargs⟩ :=
    nearestGraph_degree_six_regular p hn hp u hdegree
  obtain ⟨t, rfl⟩ := (hcover j).mp huj
  have hadj : (nearestGraph p).Adj u (v (t + 3)) :=
    (hcover _).mpr ⟨t + 3, rfl⟩
  have hne : (t + 3 : Fin 6) ≠ t := by
    fin_cases t <;> decide
  refine ⟨v (t + 3), hadj, hvinj.ne hne, ?_⟩
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  apply equal_radius_arg_gap_pi_antipodal (p u) (p (v t)) (p (v (t + 3)))
    (pairDist p ij) (pairDist_pos p hp hmin.1)
    (nearestGraph_adj_dist_eq p hmin huj)
    (nearestGraph_adj_dist_eq p hmin hadj)
  rw [hargs t, hargs (t + 3)]
  fin_cases t <;> norm_num
  all_goals
    first
    | rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]; ring
    | rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]; ring

end Erdos957
