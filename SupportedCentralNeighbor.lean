import DonorCases
import NearestMetric
import NormalizedEdgeGeometry

/-! A supporting chord through a donor and another neighbor of its center
must itself be a nearest edge. Support is an explicit premise here. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Signed areas in central-edge coordinates preserve their orientation. -/
theorem edgeCoordinate_cross_eq_turn_div (u v a b : Point) :
    (conj (edgeCoordinate u v a) * edgeCoordinate u v b).im =
      turn u a b / dist u v ^ 2 := by
  simp only [edgeCoordinate, map_div₀, div_mul_div_comm,
    ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_im]
  rw [← turn_eq_im_conj_mul, Complex.normSq_eq_norm_sq, pointToComplex.norm_map]
  simp only [dist_eq_norm, norm_sub_rev]

/-- On the unit circle centered at one, points farther than one from zero
have direction strictly between minus and plus sixty degrees. -/
theorem shifted_unit_circle_arg_lt_pi_div_three (z : ℂ)
    (hcircle : ‖z - 1‖ = 1) (hfar : 1 < ‖z‖) :
    -Real.pi / 3 < z.arg ∧ z.arg < Real.pi / 3 := by
  have hsq := Complex.normSq_eq_norm_sq z
  have hsq1 := Complex.normSq_eq_norm_sq (z - 1)
  rw [Complex.normSq_apply] at hsq hsq1
  rw [hcircle] at hsq1
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero] at hsq1
  have hcos := Complex.norm_mul_cos_arg z
  have hcosgt : 1 / 2 < Real.cos z.arg := by
    have hp := mul_pos (show 0 < ‖z‖ by linarith) (show 0 < ‖z‖ - 1 by linarith)
    nlinarith
  have habs : |z.arg| < Real.pi / 3 := by
    by_contra hnot
    have hle : Real.pi / 3 ≤ |z.arg| := le_of_not_gt hnot
    have harg : |z.arg| ≤ Real.pi := abs_le.mpr
      ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity) harg hle
    rw [Real.cos_abs, Real.cos_pi_div_three] at hc
    linarith
  exact ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2⟩

/-- If a line from a donor through another neighbor of its central point
supports the configuration, then that line segment is a nearest edge.
Neither flatness nor diameter membership of the other endpoint is assumed. -/
theorem central_common_neighbor_nearest_of_support {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u w : Fin n}
    (ctx : DonorContext p bad u) (huwne : u ≠ w)
    (hqw : (nearestGraph p).Adj ctx.q w)
    (hsupport : (∀ k, 0 ≤ turn (p u) (p w) (p k)) ∨
      (∀ k, 0 ≤ turn (p w) (p u) (p k))) :
    (nearestGraph p).Adj u w := by
  classical
  let r := pairDist p ctx.minPair
  have hr : 0 < r := pairDist_pos p hp ctx.minPair_spec.1
  have huqdist : dist (p u) (p ctx.q) = r :=
    nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj
  have hqwdist : dist (p ctx.q) (p w) = r :=
    nearestGraph_adj_dist_eq p ctx.minPair_spec hqw
  have hmindist : r ≤ dist (p u) (p w) :=
    isMinPair_le_dist p ctx.minPair_spec huwne
  apply (nearestGraph_adj_iff_dist_eq p hp ctx.minPair_spec u w).mpr
  change dist (p u) (p w) = r
  apply le_antisymm _ hmindist
  by_contra hnot
  have hfar : r < dist (p u) (p w) := lt_of_not_ge hnot
  obtain ⟨v, _hvinj, _hvrange, hvadj, hvmono, hgap01, hgap12, hvlo, hvhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp ctx.diameter_adj ctx.degree_three
  have hmiddle : v 1 = ctx.q := ctx.central_unique (v 1) (hvadj 1) hvlo hvhi
  have hhalf (i : Fin 3) :
      0 < inner ℝ (p ctx.j - p u) (p (v i) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp ctx.diameter_adj (hvadj i).ne
  have hqhalf : 0 < inner ℝ (p ctx.j - p u) (p ctx.q - p u) := by
    simpa only [hmiddle] using hhalf 1
  have hne : p u ≠ p ctx.q := hp.ne ctx.central_adj.ne
  let A := edgeCoordinate (p u) (p ctx.q) (p (v 0))
  let C := edgeCoordinate (p u) (p ctx.q) (p (v 2))
  let W := edgeCoordinate (p u) (p ctx.q) (p w)
  have hAarg : A.arg = halfplaneArg (p u) (p ctx.j - p u) (p (v 0)) -
      halfplaneArg (p u) (p ctx.j - p u) (p ctx.q) :=
    edgeCoordinate_arg (p u) (p ctx.q) (p (v 0)) (p ctx.j - p u) hqhalf (hhalf 0)
  have hCarg : C.arg = halfplaneArg (p u) (p ctx.j - p u) (p (v 2)) -
      halfplaneArg (p u) (p ctx.j - p u) (p ctx.q) :=
    edgeCoordinate_arg (p u) (p ctx.q) (p (v 2)) (p ctx.j - p u) hqhalf (hhalf 2)
  have hAleft : A.arg ≤ -Real.pi / 3 := by
    rw [hAarg]
    rw [hmiddle] at hgap01
    linarith
  have hCright : Real.pi / 3 ≤ C.arg := by
    rw [hCarg]
    rw [hmiddle] at hgap12
    exact hgap12
  have hspan : C.arg - A.arg < Real.pi := by
    rw [hAarg, hCarg]
    have hlo := (halfplaneArg_mem_Ioo (hhalf 0)).1
    have hhi := (halfplaneArg_mem_Ioo (hhalf 2)).2
    linarith
  have hAunit : ‖A‖ = 1 := by
    dsimp [A]
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj 0), huqdist, div_self hr.ne']
  have hCunit : ‖C‖ = 1 := by
    dsimp [C]
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj 2), huqdist, div_self hr.ne']
  have hWcircle : ‖W - 1‖ = 1 := by
    dsimp [W]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, hqwdist, huqdist, div_self hr.ne']
  have hWfar : 1 < ‖W‖ := by
    dsimp [W]
    rw [edgeCoordinate_norm _ _ _ hne, huqdist]
    exact (one_lt_div hr).mpr hfar
  obtain ⟨hWlo, hWhi⟩ := shifted_unit_circle_arg_lt_pi_div_three W hWcircle hWfar
  have hAWarg : A.arg < W.arg := by linarith
  have hWCarg : W.arg < C.arg := by linarith
  have hAW : 0 < (conj A * W).im := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub, hAunit, one_mul]
    exact mul_pos (by linarith : 0 < ‖W‖)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hWC : 0 < (conj W * C).im := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub, hCunit, mul_one]
    exact mul_pos (by linarith : 0 < ‖W‖)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hscale : 0 < dist (p u) (p ctx.q) ^ 2 := by rw [huqdist]; positivity
  have hturnAW : 0 < turn (p u) (p (v 0)) (p w) := by
    change 0 < (conj (edgeCoordinate (p u) (p ctx.q) (p (v 0))) *
      edgeCoordinate (p u) (p ctx.q) (p w)).im at hAW
    rw [edgeCoordinate_cross_eq_turn_div] at hAW
    exact (div_pos_iff_of_pos_right hscale).mp hAW
  have hturnWC : 0 < turn (p u) (p w) (p (v 2)) := by
    change 0 < (conj (edgeCoordinate (p u) (p ctx.q) (p w)) *
      edgeCoordinate (p u) (p ctx.q) (p (v 2))).im at hWC
    rw [edgeCoordinate_cross_eq_turn_div] at hWC
    exact (div_pos_iff_of_pos_right hscale).mp hWC
  rcases hsupport with hsupport | hsupport
  · have hs := hsupport (v 0)
    rw [turn_swap] at hs
    linarith
  · have hs := hsupport (v 2)
    rw [turn_reverse] at hs
    linarith

end Erdos957
