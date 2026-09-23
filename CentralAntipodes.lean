import CentralProjection
import NearestBound
import DiameterGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Opposite closest-pair neighbors of a degree-six vertex cannot both point
centrally toward long diameter partners. -/

namespace Erdos957

/-- A direction inside the central thirty-degree cone retains at least three
quarters of its full axial projection. -/
theorem central_inner_ge_three_quarters (x axis y : Point) (r : ℝ)
    (hr : 0 ≤ r) (hxy : dist x y = r)
    (hlo : -Real.pi / 6 < halfplaneArg x axis y)
    (hhi : halfplaneArg x axis y < Real.pi / 6) :
    (3 / 4 : ℝ) * (‖axis‖ * r) ≤ inner ℝ axis (y - x) := by
  let θ := halfplaneArg x axis y
  have habs : |θ| < Real.pi / 6 :=
    abs_lt.mpr ⟨by dsimp [θ]; linarith, hhi⟩
  have hπ := Real.pi_le_four
  have hcap : |θ| < (2 / 3 : ℝ) := by linarith
  have hu : θ ≤ (2 / 3 : ℝ) := (le_abs_self θ).trans hcap.le
  have hl : -(2 / 3 : ℝ) ≤ θ := by
    have h := neg_le_of_abs_le hcap.le
    linarith
  have hprod : 0 ≤ ((2 / 3 : ℝ) - θ) * ((2 / 3 : ℝ) + θ) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : θ ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by nlinarith
  have hcos0 := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hcos : (3 / 4 : ℝ) ≤ Real.cos θ := by nlinarith
  rw [← rotatedCoordinate_re_eq_inner, rotatedCoordinate_re_of_dist x axis y r hxy]
  calc
    (3 / 4 : ℝ) * (‖axis‖ * r) = (‖axis‖ * r) * (3 / 4 : ℝ) := by ring
    _ ≤ (‖axis‖ * r) * Real.cos θ :=
      mul_le_mul_of_nonneg_left hcos (mul_nonneg (norm_nonneg axis) hr)

/-- If two nearest neighbors are opposite about their common center and both
are central directions to diameter partners, then the diameter is at most four
times their nearest-neighbor radius. -/
theorem central_antipodes_diameter_le_four_min {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {u w q j k : Fin n}
    (huj : (diameterGraph p).Adj u j)
    (hwk : (diameterGraph p).Adj w k)
    (huq : (nearestGraph p).Adj u q)
    (hwq : (nearestGraph p).Adj w q)
    (hmid : p u + p w = 2 • p q)
    (hulo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p q))
    (huhi : halfplaneArg (p u) (p j - p u) (p q) < Real.pi / 6)
    (hwlo : -Real.pi / 6 < halfplaneArg (p w) (p k - p w) (p q))
    (hwhi : halfplaneArg (p w) (p k - p w) (p q) < Real.pi / 6) :
    dist (p u) (p j) ≤ 4 * pairDist p ij := by
  let r := pairDist p ij
  let D := dist (p u) (p j)
  let a := p u - p q
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hru : dist (p u) (p q) = r := nearestGraph_adj_dist_eq p hmin huq
  have hrw : dist (p w) (p q) = r := nearestGraph_adj_dist_eq p hmin hwq
  have har : ‖a‖ = r := by simpa only [a, dist_eq_norm] using hru
  obtain ⟨kl, hmax⟩ := exists_max_pair p hn
  have hD : D = pairDist p kl :=
    (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp huj
  have hDk : dist (p w) (p k) = D := by
    rw [hD]
    exact (diameterGraph_adj_iff_dist_eq p hp hmax w k).mp hwk
  have hjk : dist (p j) (p k) ≤ D := by
    rw [hD]
    exact isMaxPair_dist_le p hmax j k
  have hinneru := central_inner_ge_three_quarters (p u) (p j - p u)
    (p q) r hr.le hru hulo huhi
  have hinnerw := central_inner_ge_three_quarters (p w) (p k - p w)
    (p q) r hr.le hrw hwlo hwhi
  have hnormuj : ‖p j - p u‖ = D := by simp [D, dist_eq_norm, norm_sub_rev]
  have hnormwk : ‖p k - p w‖ = D := by
    simpa only [dist_eq_norm, norm_sub_rev] using hDk
  rw [hnormuj] at hinneru
  rw [hnormwk] at hinnerw
  have hqwu : p q - p w = a := by
    have hpw : p w = p q + p q - p u := by
      calc
        p w = (p u + p w) - p u := by abel
        _ = (2 • p q) - p u := by rw [hmid]
        _ = p q + p q - p u := by rw [two_smul]
    rw [hpw]
    dsimp [a]
    abel
  have huw : p u - p w = 2 • a := by
    have hpw : p w = p q + p q - p u := by
      calc
        p w = (p u + p w) - p u := by abel
        _ = (2 • p q) - p u := by rw [hmid]
        _ = p q + p q - p u := by rw [two_smul]
    rw [hpw]
    dsimp [a]
    rw [two_smul]
    abel
  have hinneru' : (3 / 4 : ℝ) * (D * r) ≤ inner ℝ (p u - p j) a := by
    simpa only [show p q - p u = -a by dsimp [a]; abel,
      show p j - p u = -(p u - p j) by abel,
      inner_neg_left, inner_neg_right, neg_neg] using hinneru
  have hinnerw' : (3 / 4 : ℝ) * (D * r) ≤ inner ℝ (p k - p w) a := by
    simpa only [hqwu] using hinnerw
  have hvec : (p u - p j) + (p k - p w) = (p k - p j) + 2 • a := by
    rw [← huw]
    abel
  have hsum : inner ℝ (p u - p j) a + inner ℝ (p k - p w) a =
      inner ℝ (p k - p j) a + 2 * ‖a‖ ^ 2 := by
    rw [← inner_add_left, hvec, inner_add_left]
    rw [two_smul, inner_add_left, real_inner_self_eq_norm_sq]
    ring
  have hbound : (3 / 2 : ℝ) * (D * r) ≤
      inner ℝ (p k - p j) a + 2 * r ^ 2 := by
    rw [har] at hsum
    linarith
  have hnormjk : ‖p k - p j‖ ≤ D := by
    simpa only [dist_eq_norm, norm_sub_rev] using hjk
  have hcauchy : inner ℝ (p k - p j) a ≤ D * r := by
    calc
      inner ℝ (p k - p j) a ≤ ‖p k - p j‖ * ‖a‖ :=
        real_inner_le_norm _ _
      _ ≤ D * r := by rw [har]; exact mul_le_mul_of_nonneg_right hnormjk hr.le
  dsimp [D, r] at *
  nlinarith [sq_nonneg (pairDist p ij)]

/-- At diameter greater than ten nearest-neighbor radii, opposite central
neighbors cannot both be diameter endpoints. -/
theorem no_two_central_antipodes_at_large_scale {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {u w q j k : Fin n}
    (huj : (diameterGraph p).Adj u j)
    (hwk : (diameterGraph p).Adj w k)
    (huq : (nearestGraph p).Adj u q)
    (hwq : (nearestGraph p).Adj w q)
    (hmid : p u + p w = 2 • p q)
    (hulo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p q))
    (huhi : halfplaneArg (p u) (p j - p u) (p q) < Real.pi / 6)
    (hwlo : -Real.pi / 6 < halfplaneArg (p w) (p k - p w) (p q))
    (hwhi : halfplaneArg (p w) (p k - p w) (p q) < Real.pi / 6)
    (hscale : 10 * pairDist p ij < dist (p u) (p j)) : False := by
  have hfour := central_antipodes_diameter_le_four_min p hn hp hmin
    huj hwk huq hwq hmid hulo huhi hwlo hwhi
  have hr := pairDist_pos p hp hmin.1
  linarith

end Erdos957
