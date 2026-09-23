import NormalizedEdgeGeometry
import CircleTriangle
import TriangleInterior

/-! Transfer strict triangle containment through normalized edge coordinates. -/

namespace Erdos957

open scoped ComplexConjugate

theorem edgeCoordinate_sub (u v a b : Point) :
    edgeCoordinate u v b - edgeCoordinate u v a =
      pointToComplex (b - a) / pointToComplex (v - u) := by
  simp only [edgeCoordinate, ← sub_div, ← map_sub, sub_sub_sub_cancel_right]

theorem edgeCoordinate_complexTurn_mul_dist_sq (u v a b c : Point)
    (hne : u ≠ v) :
    complexTurn (edgeCoordinate u v a) (edgeCoordinate u v b)
      (edgeCoordinate u v c) * dist u v ^ 2 = turn a b c := by
  have hnorm : Complex.normSq (pointToComplex (v - u)) = dist u v ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [complexTurn, edgeCoordinate_sub, edgeCoordinate_sub, map_div₀,
    div_mul_div_comm, ← Complex.normSq_eq_conj_mul_self, hnorm,
    turn_eq_im_conj_mul]
  simp only [Complex.div_im, Complex.normSq_apply, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, add_zero]
  field_simp [dist_ne_zero.mpr hne]
  ring

theorem edgeCoordinate_complexTurn_pos_iff (u v a b c : Point)
    (hne : u ≠ v) :
    0 < complexTurn (edgeCoordinate u v a) (edgeCoordinate u v b)
      (edgeCoordinate u v c) ↔ 0 < turn a b c := by
  rw [← edgeCoordinate_complexTurn_mul_dist_sq u v a b c hne]
  exact (mul_pos_iff_of_pos_right (sq_pos_of_pos (dist_pos.mpr hne))).symm

/-- Three strict normalized side tests place an actual configuration point
in the interior of the full hull. The triangle vertices are actual points. -/
theorem normalized_triangle_mem_interior_configuration {n : ℕ}
    (p : Fin n → Point) {u v a b c k : Fin n}
    (hne : p u ≠ p v)
    (hab : 0 < complexTurn (edgeCoordinate (p u) (p v) (p a))
      (edgeCoordinate (p u) (p v) (p b)) (edgeCoordinate (p u) (p v) (p k)))
    (hbc : 0 < complexTurn (edgeCoordinate (p u) (p v) (p b))
      (edgeCoordinate (p u) (p v) (p c)) (edgeCoordinate (p u) (p v) (p k)))
    (hca : 0 < complexTurn (edgeCoordinate (p u) (p v) (p c))
      (edgeCoordinate (p u) (p v) (p a)) (edgeCoordinate (p u) (p v) (p k))) :
    p k ∈ interior (convexHull ℝ (Set.range p)) := by
  have hab' := (edgeCoordinate_complexTurn_pos_iff _ _ _ _ _ hne).mp hab
  have hbc' := (edgeCoordinate_complexTurn_pos_iff _ _ _ _ _ hne).mp hbc
  have hca' := (edgeCoordinate_complexTurn_pos_iff _ _ _ _ _ hne).mp hca
  have hsum : turn (p a) (p b) (p k) + turn (p b) (p c) (p k) +
      turn (p c) (p a) (p k) = turn (p a) (p b) (p c) := by
    unfold turn
    ring
  have hinside := triangle_strict_turns_mem_interior (p a) (p b) (p c) (p k)
    (by linarith) hab' hbc' hca'
  apply interior_mono (convexHull_mono ?_) hinside
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl <;> exact Set.mem_range_self _

/-- Triangle witnesses may lie on hull segments; they need not be original
configuration points. This allows long hull edges to be interpolated. -/
theorem normalized_triangle_mem_interior_convexHull (s : Set Point)
    (u v a b c q : Point) (hne : u ≠ v)
    (ha : a ∈ convexHull ℝ s) (hb : b ∈ convexHull ℝ s)
    (hc : c ∈ convexHull ℝ s)
    (hab : 0 < complexTurn (edgeCoordinate u v a)
      (edgeCoordinate u v b) (edgeCoordinate u v q))
    (hbc : 0 < complexTurn (edgeCoordinate u v b)
      (edgeCoordinate u v c) (edgeCoordinate u v q))
    (hca : 0 < complexTurn (edgeCoordinate u v c)
      (edgeCoordinate u v a) (edgeCoordinate u v q)) :
    q ∈ interior (convexHull ℝ s) := by
  have hab' := (edgeCoordinate_complexTurn_pos_iff u v a b q hne).mp hab
  have hbc' := (edgeCoordinate_complexTurn_pos_iff u v b c q hne).mp hbc
  have hca' := (edgeCoordinate_complexTurn_pos_iff u v c a q hne).mp hca
  have hsum : turn a b q + turn b c q + turn c a q = turn a b c := by
    unfold turn
    ring
  have hinside := triangle_strict_turns_mem_interior a b c q
    (by linarith) hab' hbc' hca'
  apply interior_mono (convexHull_min ?_ (convex_convexHull ℝ s)) hinside
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

end Erdos957
