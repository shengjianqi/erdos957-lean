import FourDeltaDiameterLocality

/-! A sufficiently deep receiver has no minimum-distance edge to a diameter
endpoint. This excludes direct cocharges, without asserting a bound on sums
of indirect charges. -/

namespace Erdos957

private theorem shallow_cone_add {z w : ℂ}
    (hz : |z.im| ≤ z.re / 30) (hw : |w.im| ≤ w.re / 30) :
    |(z + w).im| ≤ (z + w).re / 30 := by
  simp only [Complex.add_im, Complex.add_re]
  calc
    |z.im + w.im| ≤ |z.im| + |w.im| := abs_add_le _ _
    _ ≤ (z.re + w.re) / 30 := by linarith

private theorem shallow_cone_abs {z : ℂ} (hz : |z.im| ≤ z.re / 30) :
    |z.im| ≤ |z.re| / 30 := by
  have hx : 0 ≤ z.re := by linarith [abs_nonneg z.im]
  simpa only [abs_of_nonneg hx] using hz

/-- All seven local vertices lie in the shallow horizontal double cone in
the actual outgoing-edge coordinates. No bound on edge lengths is needed. -/
theorem tight_flat_seven_vertex_im_bound {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (w : Fin n)
    (hw : w = v i ∨ w = v (i + 1) ∨ w = v (i - 1) ∨
      w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1) ∨
      w = v (((i + 1) + 1) + 1) ∨ w = v (((i - 1) - 1) - 1)) :
    |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p w)).im| ≤
      |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p w)).re| / 30 := by
  let M := fun k => edgeCoordinate (p (v i)) (p (v (i + 1))) (p k)
  let Z := fun j => hullEdgeDirection p v j / hullEdgeDirection p v i
  have hzero : M (v i) = 0 := edgeCoordinate_self _ _
  have hdiff (j : Fin h) : M (v (j + 1)) - M (v j) = Z j := by
    dsimp [M, Z]
    rw [edgeCoordinate_sub]
    rfl
  have hargs := tight_hull_eight_edge_args p hp v hv hh i hpos hgood
  have hz (j : Fin h)
      (hj : j = (((i - 1) - 1) - 1) - 1 ∨ j = ((i - 1) - 1) - 1 ∨
        j = (i - 1) - 1 ∨ j = i - 1 ∨ j = i ∨ j = i + 1 ∨
        j = (i + 1) + 1 ∨ j = ((i + 1) + 1) + 1) :
      |(Z j).im| ≤ (Z j).re / 30 :=
    (extended_small_arg_projection (Z j) (hargs j hj)).2
  have hp1 : M (v (i + 1)) = Z i := by
    simpa only [hzero, sub_zero] using hdiff i
  have hp2 : M (v ((i + 1) + 1)) = Z i + Z (i + 1) := by
    have ht := hdiff (i + 1)
    rw [hp1] at ht
    linear_combination ht
  have hp3 : M (v (((i + 1) + 1) + 1)) =
      (Z i + Z (i + 1)) + Z ((i + 1) + 1) := by
    have ht := hdiff ((i + 1) + 1)
    rw [hp2] at ht
    linear_combination ht
  have hm1 : M (v (i - 1)) = -Z (i - 1) := by
    have ht := hdiff (i - 1)
    simp only [sub_add_cancel, hzero, zero_sub] at ht
    linear_combination -ht
  have hm2 : M (v ((i - 1) - 1)) = -(Z ((i - 1) - 1) + Z (i - 1)) := by
    have ht := hdiff ((i - 1) - 1)
    simp only [sub_add_cancel, hm1] at ht
    linear_combination -ht
  have hm3 : M (v (((i - 1) - 1) - 1)) =
      -((Z (((i - 1) - 1) - 1) + Z ((i - 1) - 1)) + Z (i - 1)) := by
    have ht := hdiff (((i - 1) - 1) - 1)
    simp only [sub_add_cancel, hm2] at ht
    linear_combination -ht
  change |(M w).im| ≤ |(M w).re| / 30
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [hzero, Complex.zero_im, Complex.zero_re, abs_zero, zero_div, le_refl]
  · rw [hp1]
    exact shallow_cone_abs (hz i (by tauto))
  · rw [hm1]
    simpa only [Complex.neg_im, Complex.neg_re, abs_neg] using
      shallow_cone_abs (hz (i - 1) (by tauto))
  · rw [hp2]
    exact shallow_cone_abs (shallow_cone_add (hz i (by tauto)) (hz (i + 1) (by tauto)))
  · rw [hm2]
    simpa only [Complex.neg_im, Complex.neg_re, abs_neg] using
      shallow_cone_abs (shallow_cone_add (hz ((i - 1) - 1) (by tauto)) (hz (i - 1) (by tauto)))
  · rw [hp3]
    exact shallow_cone_abs (shallow_cone_add
      (shallow_cone_add (hz i (by tauto)) (hz (i + 1) (by tauto)))
      (hz ((i + 1) + 1) (by tauto)))
  · rw [hm3]
    simpa only [Complex.neg_im, Complex.neg_re, abs_neg] using
      shallow_cone_abs (shallow_cone_add
        (shallow_cone_add (hz (((i - 1) - 1) - 1) (by tauto))
          (hz ((i - 1) - 1) (by tauto))) (hz (i - 1) (by tauto)))

/-- A receiver at least three halves of a minimum distance inward from the
outgoing supporting line has no nearest neighbor among diameter endpoints. -/
theorem tight_flat_deep_receiver_no_diameter_neighbor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (x : Fin n) (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im) :
    ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p := by
  let M := fun k => edgeCoordinate (p (v i)) (p (v (i + 1))) (p k)
  let L := dist (p (v i)) (p (v (i + 1)))
  let r := pairDist p ij / L
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL : 0 < L := dist_pos.mpr hne
  have hr : 0 < r := div_pos (pairDist_pos p hp hmin.1) hL
  intro a hxa haD
  have hxaDist := nearestGraph_adj_dist_eq p hmin hxa
  have huaDist : dist (p (v i)) (p a) ≤ 3 * pairDist p ij := by
    have ht := dist_triangle (p (v i)) (p x) (p a)
    linarith
  have haNorm : ‖M a‖ ≤ 3 * r := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne]
    have ht := div_le_div_of_nonneg_right huaDist hL.le
    simpa only [r, L, mul_div_assoc] using ht
  have haRe : |(M a).re| ≤ 3 * r := (Complex.abs_re_le_norm _).trans haNorm
  have haLocal := tight_flat_four_distance_diameter_endpoint_local
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu a haD
    (by linarith [pairDist_pos p hp hmin.1]) (by change |(M a).re| ≤ _; dsimp [r, L] at haRe ⊢; linarith [hr])
  have haSlope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood a haLocal
  change |(M a).im| ≤ |(M a).re| / 30 at haSlope
  have haIm : (M a).im ≤ r / 10 := by linarith [le_abs_self (M a).im]
  have hdiffNorm : ‖M x - M a‖ = r := by
    rw [← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, hxaDist]
  have hdiffIm : (M x).im - (M a).im ≤ r := by
    have ht := Complex.im_le_norm (M x - M a)
    simpa only [Complex.sub_im, hdiffNorm] using ht
  change (3 / 2 : ℝ) * r ≤ (M x).im at hdeep
  linarith

end Erdos957
