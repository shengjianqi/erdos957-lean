import ShortHullChord
import TightHullDirections
import TightFlatOffsets

/-! Tight-flat hull neighborhoods exclude short chords across two or three
local edges. No upper bound on edge lengths or nearest base edge is assumed. -/

namespace Erdos957

/-- Actual two-step and three-step chords on both sides of a tight-flat
vertex have length at least `1.98 δ` and `2.97 δ`, respectively. -/
theorem tight_flat_hull_chord_bounds {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v) :
    (198 / 100 : ℝ) * pairDist p ij ≤
        dist (p (v i)) (p (v ((i + 1) + 1))) ∧
    (297 / 100 : ℝ) * pairDist p ij ≤
        dist (p (v i)) (p (v (((i + 1) + 1) + 1))) ∧
    (198 / 100 : ℝ) * pairDist p ij ≤
        dist (p (v i)) (p (v ((i - 1) - 1))) ∧
    (297 / 100 : ℝ) * pairDist p ij ≤
        dist (p (v i)) (p (v (((i - 1) - 1) - 1))) := by
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i hgood
  have ha := tight_hull_nearby_edge_args p hp v hv hh i hpos hi hm1 hm2 hp1 hp2
  let b := hullEdgeDirection p v i
  have hb : b ≠ 0 := hullEdgeDirection_ne_zero p hp v hv hh i
  have hedge (j : Fin h) : pairDist p ij ≤ dist (p (v j)) (p (v (j + 1))) :=
    isMinPair_le_dist p hmin (hv.ne (cyclic_three_distinct hh j).1)
  have h0 : |(hullEdgeDirection p v i / b).arg| ≤ Real.pi / 600 := by
    change |(b / b).arg| ≤ Real.pi / 600
    rw [div_self hb, Complex.arg_one, abs_zero]
    positivity
  have h1 := ha (i + 1) (Or.inl rfl)
  have h2 := ha ((i + 1) + 1) (Or.inr (Or.inl rfl))
  have hm1 := ha (i - 1) (Or.inr (Or.inr (Or.inl rfl)))
  have hm2 := ha ((i - 1) - 1) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hm3 := ha (((i - 1) - 1) - 1) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact short_hull_two_edge_chord p v i b hb (pairDist p ij)
      (hedge i) (hedge (i + 1)) h0 h1
  · exact short_hull_three_edge_chord p v i b hb (pairDist p ij)
      (hedge i) (hedge (i + 1)) (hedge ((i + 1) + 1)) h0 h1 h2
  · rw [dist_comm]
    simpa only [sub_add_cancel] using
      short_hull_two_edge_chord p v ((i - 1) - 1) b hb (pairDist p ij)
        (hedge _) (hedge _) hm2 (by simpa only [sub_add_cancel] using hm1)
  · rw [dist_comm]
    simpa only [sub_add_cancel] using
      short_hull_three_edge_chord p v (((i - 1) - 1) - 1) b hb (pairDist p ij)
        (hedge _) (hedge _) (hedge _) hm3
        (by simpa only [sub_add_cancel] using hm2)
        (by simpa only [sub_add_cancel] using hm1)

/-- Neither local two-step hull position is a nearest neighbor of a
tight-flat vertex. -/
theorem tight_flat_two_step_not_nearest {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v) (w : Fin n)
    (hw : w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1)) :
    ¬ (nearestGraph p).Adj (v i) w := by
  have hb := tight_flat_hull_chord_bounds p hp v hv hh ij hmin i hpos hgood
  have hr := pairDist_pos p hp hmin.1
  intro hadj
  have hd := nearestGraph_adj_dist_eq p hmin hadj
  rcases hw with rfl | rfl
  · linarith [hb.1]
  · linarith [hb.2.2.1]

/-- A tight-flat vertex and either local three-step hull vertex cannot
share a nearest neighbor: their distance is greater than two minimum lengths. -/
theorem tight_flat_three_step_no_common_nearest {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v) (w : Fin n)
    (hw : w = v (((i + 1) + 1) + 1) ∨ w = v (((i - 1) - 1) - 1)) :
    ¬ ∃ q, (nearestGraph p).Adj (v i) q ∧ (nearestGraph p).Adj q w := by
  have hb := tight_flat_hull_chord_bounds p hp v hv hh ij hmin i hpos hgood
  have hr := pairDist_pos p hp hmin.1
  rintro ⟨q, huq, hqw⟩
  have hd := dist_triangle (p (v i)) (p q) (p w)
  rw [nearestGraph_adj_dist_eq p hmin huq,
    nearestGraph_adj_dist_eq p hmin hqw] at hd
  rcases hw with rfl | rfl
  · linarith [hb.2.1]
  · linarith [hb.2.2.2]

end Erdos957
