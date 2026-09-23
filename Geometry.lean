import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Elementary geometric prerequisites for the minimum-distance graph in
Erdős problem 957.  These statements are valid in any real inner product
space; the main project specializes them to the Euclidean plane.
-/

namespace Erdos957

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two points at the same distance `r` from `x`, and at least `r` apart from
each other, subtend an angle of at least 60 degrees at `x`.  The inner-product
inequality is the algebraic form of that assertion. -/
theorem equal_radius_inner_le_half_sq
    (x y z : E) (r : ℝ)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : r ≤ dist y z) :
    2 * inner ℝ (x - y) (x - z) ≤ r ^ 2 := by
  have hxy_norm : ‖x - y‖ = r := by
    simpa only [dist_eq_norm] using hxy
  have hxz_norm : ‖x - z‖ = r := by
    simpa only [dist_eq_norm] using hxz
  have hdiff : ‖(x - y) - (x - z)‖ = dist y z := by
    calc
      ‖(x - y) - (x - z)‖ = ‖z - y‖ := by
        congr 1
        abel
      _ = dist z y := by simp only [dist_eq_norm]
      _ = dist y z := dist_comm z y
  have hsq := norm_sub_sq_real (x - y) (x - z)
  rw [hxy_norm, hxz_norm, hdiff] at hsq
  have hr : 0 ≤ r := by
    rw [← hxy]
    exact dist_nonneg
  have hsq_le : r ^ 2 ≤ (dist y z) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hyz)
      (add_nonneg (show (0 : ℝ) ≤ dist y z from dist_nonneg) hr)
    nlinarith
  nlinarith

/-- Applied to a separated finite point set, nearest neighbors of the same
vertex have pairwise angular separation at least 60 degrees. -/
theorem nearest_neighbors_inner_le_half_sq
    (A : Finset E) (x y z : E) (r : ℝ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → r ≤ dist a b)
    (hy : y ∈ A) (hz : z ∈ A) (hyz : y ≠ z)
    (hxy : dist x y = r) (hxz : dist x z = r) :
    2 * inner ℝ (x - y) (x - z) ≤ r ^ 2 :=
  equal_radius_inner_le_half_sq x y z r hxy hxz (hsep y hy z hz hyz)

/-- The same separation statement expressed as a genuine angle bound. -/
theorem equal_radius_angle_ge_pi_div_three
    (x y z : E) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : r ≤ dist y z) :
    Real.pi / 3 ≤ InnerProductGeometry.angle (x - y) (x - z) := by
  have hxy_norm : ‖x - y‖ = r := by
    simpa only [dist_eq_norm] using hxy
  have hxz_norm : ‖x - z‖ = r := by
    simpa only [dist_eq_norm] using hxz
  have hinner := equal_radius_inner_le_half_sq x y z r hxy hxz hyz
  have hcos : Real.cos (InnerProductGeometry.angle (x - y) (x - z)) ≤ 1 / 2 := by
    rw [InnerProductGeometry.cos_angle, hxy_norm, hxz_norm]
    apply (div_le_iff₀ (mul_pos hr hr)).2
    nlinarith
  by_contra hnot
  have hlt : InnerProductGeometry.angle (x - y) (x - z) < Real.pi / 3 :=
    lt_of_not_ge hnot
  have hangle_mem : InnerProductGeometry.angle (x - y) (x - z) ∈
      Set.Icc (0 : ℝ) Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hthird_mem : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hcos_gt := Real.strictAntiOn_cos hangle_mem hthird_mem hlt
  rw [Real.cos_pi_div_three] at hcos_gt
  linarith

/-- Pairwise 60-degree separation among the neighbors in a minimum-distance
graph of a finite point set. -/
theorem nearest_neighbors_angle_ge_pi_div_three
    (A : Finset E) (x y z : E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → r ≤ dist a b)
    (hy : y ∈ A) (hz : z ∈ A) (hyz : y ≠ z)
    (hxy : dist x y = r) (hxz : dist x z = r) :
    Real.pi / 3 ≤ InnerProductGeometry.angle (x - y) (x - z) :=
  equal_radius_angle_ge_pi_div_three x y z r hr hxy hxz (hsep y hy z hz hyz)

end Erdos957
