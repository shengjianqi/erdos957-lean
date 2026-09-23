import FlatDiameterLocality
import ExtendedFlatDirections
import LargeScaleReduction
import SmallAngleProjection
import Mathlib.Tactic.IntervalCases

/-! Four-distance locality under the original seven-position flatness
certificate. An additional horizontal bound gives exactly the seven central
hull positions, without enlarging the exceptional set. -/

namespace Erdos957

open scoped ComplexConjugate

/-- The sharper one-hundredth cone permits an axis gap below seven fifths
of the diameter. This is the margin needed at four minimum distances. -/
theorem four_distance_diameter_axis_im_pos (A B : ℂ) (D : ℝ)
    (hD : 0 < D) (hA : ‖A‖ = D) (hB : ‖B‖ = D)
    (hgap : ‖A - B‖ < 7 * D / 5)
    (hAx : 0 ≤ A.re) (hcone : 100 * A.re ≤ A.im) :
    0 < B.im := by
  have hsquare (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z
  have hAy : A.im ≤ D := by simpa only [hA] using Complex.im_le_norm A
  have hBx : B.re ≤ D := by simpa only [hB] using Complex.re_le_norm B
  have hAypos : 0 ≤ A.im := by linarith
  have hAxbound : A.re ≤ D / 100 := by linarith
  have hAsq := hsquare A
  have hBsq := hsquare B
  have hABsq := hsquare (A - B)
  simp only [Complex.sub_re, Complex.sub_im, hA, hB] at hAsq hBsq hABsq
  have hgapSq : ‖A - B‖ ^ 2 < (7 * D / 5) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hgap
  have hdot : D ^ 2 / 50 < A.re * B.re + A.im * B.im := by
    nlinarith only [hAsq, hBsq, hABsq, hgapSq]
  by_contra hnot
  have hBy : B.im ≤ 0 := le_of_not_gt hnot
  have hyprod := mul_nonpos_of_nonneg_of_nonpos hAypos hBy
  have hxprod := mul_nonneg hAx (sub_nonneg.mpr hBx)
  have hxD := mul_nonneg hD.le (sub_nonneg.mpr hAxbound)
  nlinarith only [hdot, hyprod, hxprod, hxD, sq_pos_of_pos hD]

private theorem normalized_diameter_inward_strict {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    (a b : Fin n) (hab : p a ≠ p b)
    {u j x : Fin n} (hdiam : (diameterGraph p).Adj u j) (hxu : x ≠ u) :
    let M := fun k => edgeCoordinate (p a) (p b) (p k)
    0 < (M j - M u).re * (M x - M u).re +
      (M j - M u).im * (M x - M u).im := by
  let M := fun k => edgeCoordinate (p a) (p b) (p k)
  have hmetric : dist (M j) (M x) ≤ dist (M j) (M u) := by
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hab, edgeCoordinate_dist _ _ _ _ hab]
    apply div_le_div_of_nonneg_right _ dist_nonneg
    rcases (diameterGraph_adj_iff p u j).mp hdiam with hmax | hmax
    · simpa only [pairDist, dist_comm] using isMaxPair_dist_le p hmax j x
    · simpa only [pairDist] using isMaxPair_dist_le p hmax j x
  have hne : M x ≠ M u := fun heq =>
    hxu (hp (edgeCoordinate_injective (p a) (p b) hab heq))
  have hin := farthest_inner_strict (M u) (M j) (M x) hmetric hne
  rw [show M u - M j = -(M j - M u) by abel, inner_neg_left] at hin
  change 0 < (M j - M u).re * (M x - M u).re +
    (M j - M u).im * (M x - M u).im
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hin
  nlinarith only [hin]

/-- A diameter endpoint within four minimum distances and with horizontal
projection at most fifteen fourths of the minimum distance belongs to the
seven central hull positions. The original exception set suffices. -/
theorem tight_flat_four_distance_diameter_endpoint_local {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (w : Fin n) (hw : w ∈ diameterEndpoints p)
    (hclose : dist (p (v i)) (p w) ≤ 4 * pairDist p ij)
    (hhorizontal : |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p w)).re| ≤
      (15 / 4 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1))))) :
    w = v i ∨ w = v (i + 1) ∨ w = v (i - 1) ∨
      w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1) ∨
      w = v (((i + 1) + 1) + 1) ∨ w = v (((i - 1) - 1) - 1) := by
  let u := v i
  let s := v (i + 1)
  have hus : p u ≠ p s := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  let L := dist (p u) (p s)
  have hL : 0 < L := dist_pos.mpr hus
  let M := fun k => edgeCoordinate (p u) (p s) (p k)
  let r := pairDist p ij / L
  have hr : 0 < r := div_pos (pairDist_pos p hp hmin.1) hL
  have hMu : M u = 0 := edgeCoordinate_self _ _
  have hMs : M s = 1 := edgeCoordinate_axis _ _ hus
  have hMn (a : Fin n) : ‖M a‖ = dist (p u) (p a) / L :=
    edgeCoordinate_norm _ _ _ hus
  have hMd (a b : Fin n) : dist (M a) (M b) = dist (p a) (p b) / L :=
    edgeCoordinate_dist _ _ _ _ hus
  let e := hullEdgeDirection p v i
  let Z := fun j => hullEdgeDirection p v j / e
  have henorm : ‖e‖ = L := by
    change ‖pointToComplex (p s - p u)‖ = L
    rw [pointToComplex.norm_map]
    simp only [L, dist_eq_norm, norm_sub_rev]
  have hZnorm (j : Fin h) : r ≤ ‖Z j‖ := by
    have hsep := isMinPair_le_dist p hmin (hv.ne (cyclic_three_distinct hh j).1)
    dsimp [Z, r]
    rw [norm_div, henorm, hullEdgeDirection, pointToComplex.norm_map]
    apply div_le_div_of_nonneg_right _ hL.le
    simpa only [dist_eq_norm, norm_sub_rev] using hsep
  have hZsub (j : Fin h) : M (v (j + 1)) - M (v j) = Z j := by
    dsimp [M, Z, e, u, s]
    rw [edgeCoordinate_sub]
    rfl
  have hargs := tight_hull_eight_edge_args p hp v hv hh i hpos hgood
  have hZbounds (j : Fin h)
      (hj : j = (((i - 1) - 1) - 1) - 1 ∨ j = ((i - 1) - 1) - 1 ∨
        j = (i - 1) - 1 ∨ j = i - 1 ∨ j = i ∨ j = i + 1 ∨
        j = (i + 1) + 1 ∨ j = ((i + 1) + 1) + 1) :
      (99 / 100 : ℝ) * r ≤ (Z j).re ∧ |(Z j).im| ≤ (Z j).re / 30 := by
    have ha : |(Z j).arg| ≤ Real.pi / 300 := hargs j hj
    have hb := extended_small_arg_projection (Z j) ha
    exact ⟨by linarith [hZnorm j, hb.1], hb.2⟩
  have hside (j : Fin h) (k : Fin n) :
      0 ≤ complexTurn (M (v j)) (M (v (j + 1))) (M k) := by
    have ht := edgeCoordinate_complexTurn_mul_dist_sq (p u) (p s)
      (p (v j)) (p (v (j + 1))) (p k) hus
    have hs := hsupport j k
    have hLsq : 0 < dist (p u) (p s) ^ 2 := sq_pos_of_pos hL
    change complexTurn (M (v j)) (M (v (j + 1))) (M k) * _ = _ at ht
    nlinarith only [ht, hs, hLsq]
  obtain ⟨j, huj⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  obtain ⟨k, hwk⟩ := (mem_diameterEndpoints_iff_exists_adj p w).mp hw
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  let D := pairDist p kl / L
  have hDlong : 10 * r < D := by
    have ht := ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
    dsimp [r, D]
    rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hL).mpr ht
  have hD : 0 < D := by linarith
  have hmetric (a b : Fin n) : dist (M a) (M b) ≤ D := by
    rw [hMd]
    exact div_le_div_of_nonneg_right (isMaxPair_dist_le p hmax a b) hL.le
  let A := M j
  let B := M k - M w
  have hA : ‖A‖ = D := by
    rw [hMn, (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp huj]
  have hB : ‖B‖ = D := by
    rw [show ‖B‖ = dist (M k) (M w) by simp only [B, dist_eq_norm], hMd,
      dist_comm (p k) (p w), (diameterGraph_adj_iff_dist_eq p hp hmax w k).mp hwk]
  have hWnorm : ‖M w‖ ≤ 4 * r := by
    rw [hMn]
    have hc := div_le_div_of_nonneg_right hclose hL.le
    simpa only [r, mul_div_assoc] using hc
  have hgap : ‖A - B‖ < 7 * D / 5 := by
    have hnorm : ‖A - B‖ ≤ D + 4 * r := by
      have hid : A - B = (M j - M k) + M w := by dsimp [A, B]; abel
      rw [hid]
      exact (norm_add_le _ _).trans
        (add_le_add (by simpa only [dist_eq_norm] using hmetric j k) hWnorm)
    linarith
  have hAx : 0 < A.re := by
    have hs := normalized_diameter_inward_strict p hp u s hus huj
      (hv.ne (cyclic_three_distinct hh i).1).symm
    change 0 < (M j - M u).re * (M s - M u).re +
      (M j - M u).im * (M s - M u).im at hs
    simpa only [hMu, hMs, sub_zero, Complex.one_re, Complex.one_im,
      mul_one, mul_zero, add_zero] using hs
  have hcone : 100 * A.re ≤ A.im := by
    let P := M (v (i - 1))
    have hprev : P = -Z (i - 1) := by
      have hs := hZsub (i - 1)
      simp only [sub_add_cancel] at hs
      change M u - P = Z (i - 1) at hs
      rw [hMu, zero_sub] at hs
      simpa only [neg_neg] using congrArg Neg.neg hs
    have hb := hZbounds (i - 1) (by tauto)
    have hsharp : |(Z (i - 1)).im| ≤ (Z (i - 1)).re / 100 :=
      tight_hull_predecessor_slope p v hv i hpos hgood
    have hPx : P.re < 0 := by rw [hprev, Complex.neg_re]; nlinarith [hr, hb.1]
    have hPy : 0 ≤ P.im := by
      have hs := hside i (v (i - 1))
      change 0 ≤ complexTurn (M u) (M s) P at hs
      simpa only [hMu, hMs, complexTurn, sub_zero, map_one, one_mul] using hs
    have hPslope : P.im ≤ -P.re / 100 := by
      have hh := (abs_le.mp hsharp).1
      simpa only [hprev, Complex.neg_re, Complex.neg_im, neg_neg] using (by linarith :
        -(Z (i - 1)).im ≤ (Z (i - 1)).re / 100)
    have hpi : v (i - 1) ≠ u := by
      have hne := hv.ne (cyclic_three_distinct hh (i - 1)).1
      simpa only [sub_add_cancel] using hne
    have hs := normalized_diameter_inward_strict p hp u s hus huj hpi
    change 0 < (M j - M u).re * (P - M u).re +
      (M j - M u).im * (P - M u).im at hs
    simp only [hMu, sub_zero] at hs
    change 0 < A.re * P.re + A.im * P.im at hs
    have hAy : 0 < A.im := by
      by_contra hnot
      have hy := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hPy
      have hx := mul_neg_of_pos_of_neg hAx hPx
      linarith
    have hy := mul_le_mul_of_nonneg_left hPslope hAy.le
    by_contra hnot
    have ht : A.im < 100 * A.re := lt_of_not_ge hnot
    have htprod := mul_lt_mul_of_neg_right ht hPx
    nlinarith only [hs, hy, htprod]
  have hBy : 0 < B.im := four_distance_diameter_axis_im_pos A B D hD hA hB hgap hAx.le hcone
  let idx : ℕ → Fin h := fun t =>
    if t = 0 then (((i - 1) - 1) - 1) - 1 else
    if t = 1 then ((i - 1) - 1) - 1 else
    if t = 2 then (i - 1) - 1 else if t = 3 then i - 1 else
    if t = 4 then i else if t = 5 then i + 1 else
    if t = 6 then (i + 1) + 1 else if t = 7 then ((i + 1) + 1) + 1 else
    (((i + 1) + 1) + 1) + 1
  let c : ℕ → ℂ := fun t => M (v (idx t))
  have hnext (t : ℕ) (ht : t < 8) : idx (t + 1) = idx t + 1 := by
    interval_cases t <;> simp [idx]
  have hedgebound (t : ℕ) (ht : t < 8) :
      (99 / 100 : ℝ) * r ≤ (c (t + 1)).re - (c t).re := by
    have hb : (99 / 100 : ℝ) * r ≤ (Z (idx t)).re := by
      apply (hZbounds (idx t) ?_).1
      interval_cases t <;> simp [idx]
    have heq := congrArg Complex.re (hZsub (idx t))
    rw [← hnext t ht] at heq
    simp only [Complex.sub_re] at heq
    change (c (t + 1)).re - (c t).re = _ at heq
    rw [heq]
    exact hb
  have hstep (t : ℕ) (ht : t < 8) : (c t).re < (c (t + 1)).re := by
    have hb := hedgebound t ht
    nlinarith only [hb, hr]
  have hc4 : c 4 = 0 := by simpa [c, idx] using hMu
  have hc0 : (c 0).re ≤ -(396 / 100 : ℝ) * r := by
    have h0 := hedgebound 0 (by omega)
    have h1 := hedgebound 1 (by omega)
    have h2 := hedgebound 2 (by omega)
    have h3 := hedgebound 3 (by omega)
    norm_num only [Nat.reduceAdd] at h0 h1 h2 h3
    rw [hc4, Complex.zero_re] at h3
    linarith
  have hc8 : (396 / 100 : ℝ) * r ≤ (c 8).re := by
    have h4 := hedgebound 4 (by omega)
    have h5 := hedgebound 5 (by omega)
    have h6 := hedgebound 6 (by omega)
    have h7 := hedgebound 7 (by omega)
    norm_num only [Nat.reduceAdd] at h4 h5 h6 h7
    rw [hc4, Complex.zero_re] at h4
    linarith
  have hWx : -((15 / 4 : ℝ) * r) ≤ (M w).re ∧ (M w).re ≤ (15 / 4 : ℝ) * r :=
    abs_le.mp hhorizontal
  have hstrict (t : ℕ) (_ht : t ≤ 8) (hne : c t ≠ M w) :
      0 < B.re * ((c t).re - (M w).re) + B.im * ((c t).im - (M w).im) := by
    have hidx : v (idx t) ≠ w := fun heq => hne (by simp only [c, heq])
    have hs := normalized_diameter_inward_strict p hp u s hus hwk hidx
    simpa only [B, c, M, Complex.sub_re, Complex.sub_im] using hs
  obtain ⟨t, ht, heq⟩ := supported_point_mem_increasing_chain c 8 (by omega)
    (M w) B hstep (by linarith [hWx.1]) (by linarith [hWx.2])
    (fun t ht => by simpa only [c, hnext t ht] using hside (idx t) w)
    hBy hstrict
  have hwidx : w = v (idx t) := hp (edgeCoordinate_injective (p u) (p s) hus heq)
  interval_cases t
  · rw [← heq] at hc0
    linarith [hWx.1]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [idx] using hwidx))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [idx] using hwidx)))))
  · exact Or.inr (Or.inr (Or.inl (by simpa [idx] using hwidx)))
  · exact Or.inl (by simpa [idx] using hwidx)
  · exact Or.inr (Or.inl (by simpa [idx] using hwidx))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [idx] using hwidx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [idx] using hwidx))))))
  · rw [← heq] at hc8
    linarith [hWx.2]

end Erdos957
