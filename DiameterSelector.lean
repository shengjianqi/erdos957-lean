import DiameterGraph
import DiameterSupport
import PlanarOrientation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Selecting an extremal diameter edge at each diameter vertex

The vectors from a diameter endpoint to all of its diameter neighbors lie in
one open half-plane. This is the geometric input needed to order those rays
by a real-valued slope and select an extremal incident edge.
-/

namespace Erdos957

/-- Fix one diameter neighbor `w₀` of `u`. All other diameter-neighbor
vectors have strictly positive projection onto the axis `p w₀ - p u`. -/
theorem diameter_neighbor_inner_pos {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {u w₀ w : Fin n}
    (h₀ : (diameterGraph p).Adj u w₀)
    (hw : (diameterGraph p).Adj u w) :
    0 < inner ℝ (p w₀ - p u) (p w - p u) := by
  have hdist : dist (p w₀) (p w) ≤ dist (p w₀) (p u) := by
    rcases (diameterGraph_adj_iff p u w₀).mp h₀ with hmax | hmax
    · have h := isMaxPair_dist_le p hmax w₀ w
      simpa only [pairDist, dist_comm] using h
    · have h := isMaxPair_dist_le p hmax w₀ w
      simpa only [pairDist] using h
  have hwu : p w ≠ p u := by
    intro h
    have heq : w = u := hp h
    exact ((diameterGraph p).ne_of_adj hw) heq.symm
  have hinner := farthest_inner_strict (p u) (p w₀) (p w) hdist hwu
  have hsub : p u - p w₀ = -(p w₀ - p u) := by abel
  rw [hsub, inner_neg_left] at hinner
  linarith

private theorem selector_inner_coords (p q : Point) :
    inner ℝ p q = p 0 * q 0 + p 1 * q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The determinant identity that converts a comparison of slopes based at
`b` into the orientation of two rays based at `a`. -/
theorem turn_inner_identity (a b c d : Point) :
    turn a c d * inner ℝ (b - a) (b - a) =
      turn a b d * inner ℝ (b - a) (c - a) -
        turn a b c * inner ℝ (b - a) (d - a) := by
  simp only [turn, selector_inner_coords]
  simp only [PiLp.sub_apply]
  ring

private theorem point_norm_sq_coords (v : Point) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq v

/-- The two-dimensional Lagrange identity for the coordinate determinant. -/
theorem turn_sq_add_inner_sq (a b c : Point) :
    turn a b c ^ 2 + (inner ℝ (b - a) (c - a)) ^ 2 =
      ‖b - a‖ ^ 2 * ‖c - a‖ ^ 2 := by
  rw [point_norm_sq_coords, point_norm_sq_coords]
  simp only [turn, selector_inner_coords, PiLp.sub_apply]
  ring

/-- Any two edges incident to the same vertex in the diameter graph have the
same geometric length. -/
theorem diameter_neighbors_dist_eq {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {u w v : Fin n}
    (hw : (diameterGraph p).Adj u w)
    (hv : (diameterGraph p).Adj u v) :
    dist (p u) (p w) = dist (p u) (p v) := by
  rcases (diameterGraph_adj_iff p u w).mp hw with hmax | hmax
  · have h := (diameterGraph_adj_iff_dist_eq p hp hmax u v).mp hv
    simpa only [pairDist] using h.symm
  · have h := (diameterGraph_adj_iff_dist_eq p hp hmax u v).mp hv
    simpa only [pairDist, dist_comm] using h.symm

/-- Distinct diameter neighbors determine different rays from their common
center; the signed area of those rays cannot vanish. -/
theorem turn_ne_zero_of_diameter_neighbors_ne {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {u w v : Fin n}
    (hw : (diameterGraph p).Adj u w)
    (hv : (diameterGraph p).Adj u v)
    (hwv : w ≠ v) : turn (p u) (p w) (p v) ≠ 0 := by
  intro hturn
  let y : Point := p w - p u
  let z : Point := p v - p u
  have hlen : ‖y‖ = ‖z‖ := by
    simpa only [y, z, dist_eq_norm, norm_sub_rev] using
      diameter_neighbors_dist_eq p hp hw hv
  have hdotpos : 0 < inner ℝ y z := diameter_neighbor_inner_pos p hp hw hv
  have hid := turn_sq_add_inner_sq (p u) (p w) (p v)
  change turn (p u) (p w) (p v) ^ 2 + (inner ℝ y z) ^ 2 =
    ‖y‖ ^ 2 * ‖z‖ ^ 2 at hid
  rw [hturn, zero_pow (by norm_num : 2 ≠ 0), zero_add, ← hlen] at hid
  have hdot : inner ℝ y z = ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖, sq_nonneg (inner ℝ y z - ‖y‖ ^ 2)]
  have hdiff := norm_sub_sq_real y z
  rw [← hlen, hdot] at hdiff
  have hnormzero : ‖y - z‖ = 0 := by
    nlinarith [norm_nonneg (y - z)]
  have hyz : y = z := sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  have hpwv : p w = p v := sub_left_inj.mp hyz
  exact hwv (hp hpwv)

/-- At each diameter endpoint, an incident edge is strictly to one side of
all other incident diameter edges. This is the local selection step of Perles'
proof of the Hopf--Pannwitz edge bound. -/
theorem exists_leftmost_diameter_neighbor {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (u : Fin n)
    (hu : u ∈ diameterEndpoints p) :
    ∃ v : Fin n, (diameterGraph p).Adj u v ∧
      ∀ w : Fin n, (diameterGraph p).Adj u w → w ≠ v →
        0 < turn (p u) (p w) (p v) := by
  classical
  let G := diameterGraph p
  obtain ⟨w₀, h₀⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  have h₀mem : w₀ ∈ G.neighborFinset u := (G.mem_neighborFinset u w₀).mpr h₀
  have hN : (G.neighborFinset u).Nonempty := ⟨w₀, h₀mem⟩
  let axis : Point := p w₀ - p u
  let score : Fin n → ℝ := fun w =>
    turn (p u) (p w₀) (p w) / inner ℝ axis (p w - p u)
  obtain ⟨v, hv, hmax⟩ := (G.neighborFinset u).exists_max_image score hN
  have hadjv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
  refine ⟨v, hadjv, ?_⟩
  intro w hadjw hwv
  have hmemw : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hadjw
  have hscore : score w ≤ score v := hmax w hmemw
  have hdenw : 0 < inner ℝ axis (p w - p u) :=
    diameter_neighbor_inner_pos p hp h₀ hadjw
  have hdenv : 0 < inner ℝ axis (p v - p u) :=
    diameter_neighbor_inner_pos p hp h₀ hadjv
  have hmul :
      turn (p u) (p w₀) (p w) * inner ℝ axis (p v - p u) ≤
        turn (p u) (p w₀) (p v) * inner ℝ axis (p w - p u) := by
    exact (div_le_div_iff₀ hdenw hdenv).mp hscore
  have haxis : 0 < inner ℝ axis axis :=
    diameter_neighbor_inner_pos p hp h₀ h₀
  have hid := turn_inner_identity (p u) (p w₀) (p w) (p v)
  have hproduct :
      0 ≤ turn (p u) (p w) (p v) * inner ℝ axis axis := by
    linarith
  have hnonneg : 0 ≤ turn (p u) (p w) (p v) := by
    by_contra h
    have hneg : turn (p u) (p w) (p v) < 0 := lt_of_not_ge h
    exact (not_lt_of_ge hproduct) (mul_neg_of_neg_of_pos hneg haxis)
  have hne : turn (p u) (p w) (p v) ≠ 0 :=
    turn_ne_zero_of_diameter_neighbors_ne p hp hadjw hadjv hwv
  exact lt_of_le_of_ne hnonneg hne.symm

end Erdos957
