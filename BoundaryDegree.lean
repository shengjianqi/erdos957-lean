import NearestBound
import DiameterGraph
import DiameterSupport
import HalfplanePacking
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
The first degree-counting step toward the product estimate: diameter endpoints
receive the stronger closest-pair degree bound three, while all vertices have
degree at most six.
-/

namespace Erdos957

/-- Every other point lies in the open half-plane based at a diameter
endpoint, with inward normal pointing toward one of its diameter partners. -/
theorem diameter_neighbor_inner_pos_of_other {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {i j k : Fin n}
    (hdiam : (diameterGraph p).Adj i j) (hik : i ≠ k) :
    0 < inner ℝ (p j - p i) (p k - p i) := by
  have hdist : dist (p j) (p k) ≤ dist (p j) (p i) := by
    rcases (diameterGraph_adj_iff p i j).mp hdiam with hmax | hmax
    · have h := isMaxPair_dist_le p hmax j k
      simpa only [pairDist, dist_comm] using h
    · have h := isMaxPair_dist_le p hmax j k
      simpa only [pairDist] using h
  have hki : p k ≠ p i := by
    intro heq
    exact hik (hp heq).symm
  have hinner := farthest_inner_strict (p i) (p j) (p k) hdist hki
  have hsub : p i - p j = -(p j - p i) := by abel
  rw [hsub, inner_neg_left] at hinner
  linarith

/-- Conditional weighted handshaking. Every vertex contributes at most six,
with an additional credit of three at each diameter endpoint. -/
theorem nearestGraph_weighted_handshake {n : ℕ} (p : Fin n → Point)
    (hdeg6 : ∀ i : Fin n, (nearestGraph p).degree i ≤ 6)
    (hdeg3 : ∀ i ∈ diameterEndpoints p, (nearestGraph p).degree i ≤ 3) :
    2 * sMin p + 3 * diameterEndpointCount p ≤ 6 * n := by
  classical
  let A := diameterEndpoints p
  have hpoint (i : Fin n) :
      (nearestGraph p).degree i + (if i ∈ A then 3 else 0) ≤ 6 := by
    by_cases hi : i ∈ A
    · simp only [hi, ↓reduceIte]
      have h3 : (nearestGraph p).degree i ≤ 3 := hdeg3 i (by simpa [A] using hi)
      omega
    · simpa only [hi, ↓reduceIte, add_zero] using hdeg6 i
  have hsum :
      (∑ i : Fin n,
        ((nearestGraph p).degree i + (if i ∈ A then 3 else 0))) ≤
      ∑ _i : Fin n, (6 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    exact hpoint i
  have hcredit : (∑ i : Fin n, if i ∈ A then (3 : ℕ) else 0) =
      3 * A.card := by
    simp
    omega
  rw [Finset.sum_add_distrib, nearestGraph_handshake p, hcredit] at hsum
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  simpa [A, diameterEndpointCount, mul_comm] using hsum

/-- A diameter endpoint has at most three nearest neighbors. Its diameter
partner supplies a strict supporting half-plane, and neighboring points at
the minimum distance are separated on the corresponding semicircle. -/
theorem nearestGraph_degree_le_three_of_diameterEndpoint {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (i : Fin n) (hi : i ∈ diameterEndpoints p) :
    (nearestGraph p).degree i ≤ 3 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  let N := ((nearestGraph p).neighborFinset i).image p
  have hcard : N.card = (nearestGraph p).degree i := by
    dsimp [N]
    rw [Finset.card_image_of_injective _ hp]
    exact (nearestGraph p).card_neighborFinset_eq_degree i
  have hradius : ∀ y ∈ N, dist (p i) y = r := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    exact nearestGraph_adj_dist_eq p hmin
      (((nearestGraph p).mem_neighborFinset i k).mp hk)
  have hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hjk : j ≠ k := fun heq => hyz (congrArg p heq)
    exact isMinPair_le_dist p hmin hjk
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p i).mp hi
  have hhalf : ∀ y ∈ N, 0 < inner ℝ (p j - p i) (y - p i) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hadj : (nearestGraph p).Adj i k :=
      ((nearestGraph p).mem_neighborFinset i k).mp hk
    exact diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj hadj)
  rw [← hcard]
  exact circle_card_le_three_in_halfplane N (p i) (p j - p i)
    r hr hradius hsep hhalf

/-- The first unconditional improvement over the basic `3n` closest-pair
bound, before the paper's charging argument supplies one more unit per
diameter endpoint. -/
theorem nearestGraph_weighted_handshake_of_injective {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p) :
    2 * sMin p + 3 * diameterEndpointCount p ≤ 6 * n :=
  nearestGraph_weighted_handshake p
    (nearestGraph_degree_le_six p hn hp)
    (nearestGraph_degree_le_three_of_diameterEndpoint p hn hp)

end Erdos957
