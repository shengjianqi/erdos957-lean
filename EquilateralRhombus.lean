import Foundations
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Two equilateral triangles on opposite sides of a common edge form a rhombus. -/

namespace Erdos957

/-- There are only two equal-radius intersections of circles centered at the
endpoints of an edge. When both triangles are equilateral and have different
third vertices, the vertices are opposite across the edge midpoint. -/
theorem equilateral_rhombus (u v a b : Point) (r : ℝ) (hr : 0 < r)
    (huv : dist u v = r)
    (hua : dist u a = r) (hva : dist v a = r)
    (hub : dist u b = r) (hvb : dist v b = r)
    (hab : a ≠ b) :
    a + b = u + v := by
  let c : Point := u + v - a
  have hcu : dist c u = r := by
    have hvec : c - u = v - a := by dsimp [c]; abel
    rw [dist_eq_norm, hvec]
    simpa only [dist_eq_norm, norm_sub_rev] using hva
  have hcv : dist c v = r := by
    have hvec : c - v = u - a := by dsimp [c]; abel
    rw [dist_eq_norm, hvec]
    simpa only [dist_eq_norm, norm_sub_rev] using hua
  have huv_ne : u ≠ v := by
    intro h
    simp [h] at huv
    linarith
  have hc_ne_a : c ≠ a := by
    intro hca
    have hvec : v - a = a - u := by
      have htmp : v - a = c - u := by dsimp [c]; abel
      rw [hca] at htmp
      exact htmp
    have hdouble : v - u = (a - u) + (a - u) := by
      calc
        v - u = (v - a) + (a - u) := by abel
        _ = (a - u) + (a - u) := by rw [hvec]
    have hnorm : ‖v - u‖ = 2 * ‖a - u‖ := by
      rw [hdouble, ← two_smul ℝ (a - u), norm_smul]
      simp
    have hru : ‖a - u‖ = r := by simpa only [dist_eq_norm, norm_sub_rev] using hua
    have hrv : ‖v - u‖ = r := by simpa only [dist_eq_norm, norm_sub_rev] using huv
    rw [hru, hrv] at hnorm
    linarith
  have hfinrank : Module.finrank ℝ Point = 2 := by simp [Point]
  have hcircle := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    hfinrank huv_ne hab
    (by simpa only [dist_comm] using hua)
    (by simpa only [dist_comm] using hub)
    hcu
    (by simpa only [dist_comm] using hva)
    (by simpa only [dist_comm] using hvb)
    hcv
  rcases hcircle with h | h
  · exact False.elim (hc_ne_a h)
  · dsimp [c] at h
    calc
      a + b = a + (u + v - a) := by rw [h]
      _ = u + v := by abel

end Erdos957
