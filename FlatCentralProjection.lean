import SupportedCentralNeighbor
import TightFlatChord

/-! Supporting-frame central projection and exclusion of the two-step hull sites. -/

namespace Erdos957

open scoped ComplexConjugate

private theorem upper_cross_arg_lt (a b : ℂ)
    (ha : 0 ≤ a.im) (hb : 0 ≤ b.im) (hcross : 0 < (conj a * b).im) :
    a.arg < b.arg := by
  have ha0 := Complex.arg_nonneg_iff.mpr ha
  have hb0 := Complex.arg_nonneg_iff.mpr hb
  have has := Complex.arg_le_pi a
  have hbs := Complex.arg_le_pi b
  rw [im_conj_mul_eq_norm_mul_sin_arg_sub] at hcross
  by_contra hnot
  have hs : Real.sin (b.arg - a.arg) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (norm_nonneg a) (norm_nonneg b)) hs
  linarith

/-- The middle of three separated equal-radius upper-half-plane directions
has horizontal projection at most half the radius in absolute value. -/
theorem upper_circle_middle_re_bound (a q c : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : ‖a‖ = r) (hq : ‖q‖ = r) (hc : ‖c‖ = r)
    (hai : 0 ≤ a.im) (hqi : 0 ≤ q.im) (hci : 0 ≤ c.im)
    (haq : 0 < (conj a * q).im) (hqc : 0 < (conj q * c).im)
    (hsep1 : r ≤ dist a q) (hsep2 : r ≤ dist q c) : |q.re| ≤ r / 2 := by
  have haqarg := upper_cross_arg_lt a q hai hqi haq
  have hqcarg := upper_cross_arg_lt q c hqi hci hqc
  have hgap (z w : ℂ) (hz : ‖z‖ = r) (hw : ‖w‖ = r)
      (hzw : r ≤ dist z w) : Real.pi / 3 ≤ |z.arg - w.arg| := by
    have hz0 : z ≠ 0 := by intro heq; simp [heq] at hz; linarith
    have hw0 : w ≠ 0 := by intro heq; simp [heq] at hw; linarith
    calc
      Real.pi / 3 ≤ InnerProductGeometry.angle ((0 : ℂ) - z) (0 - w) :=
        equal_radius_angle_ge_pi_div_three (0 : ℂ) z w r hr
          (by simpa using hz) (by simpa using hw) hzw
      _ = InnerProductGeometry.angle z w := by
        simpa only [zero_sub] using InnerProductGeometry.angle_neg_neg z w
      _ ≤ |z.arg - w.arg| := complex_angle_le_arg_gap hz0 hw0
  have hgap1 := hgap a q ha hq hsep1
  have hgap2 := hgap q c hq hc hsep2
  rw [abs_of_neg (sub_neg.mpr haqarg)] at hgap1
  rw [abs_of_neg (sub_neg.mpr hqcarg)] at hgap2
  have hqlo : Real.pi / 3 ≤ q.arg := by
    have := Complex.arg_nonneg_iff.mpr hai
    linarith
  have hqhi : q.arg ≤ 2 * Real.pi / 3 := by
    have := Complex.arg_le_pi c
    linarith
  have hcoshi : Real.cos q.arg ≤ 1 / 2 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity) (Complex.arg_le_pi q) hqlo
    simpa only [Real.cos_pi_div_three] using h
  have hcoslo : -(1 / 2 : ℝ) ≤ Real.cos q.arg := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (Complex.arg_nonneg_iff.mpr hqi)
      (show 2 * Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hqhi
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at h
    exact h
  have hre := Complex.norm_mul_cos_arg q
  rw [hq] at hre
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hcoshi hr.le,
    mul_le_mul_of_nonneg_left hcoslo hr.le]

private theorem turn_pos_of_halfplaneArg_lt (x axis a b : Point)
    (haxis : axis ≠ 0) (ha : a ≠ x) (hb : b ≠ x)
    (harg : halfplaneArg x axis a < halfplaneArg x axis b)
    (hgap : halfplaneArg x axis b - halfplaneArg x axis a < Real.pi) :
    0 < turn x a b := by
  have hx : rotatedCoordinate x axis x = 0 := by simp [rotatedCoordinate]
  apply (rotatedCoordinate_turn_pos_iff x axis x a b haxis).mp
  rw [hx, sub_zero, sub_zero, im_conj_mul_eq_norm_mul_sin_arg_sub,
    rotatedCoordinate_arg, rotatedCoordinate_arg]
  have hna : 0 < ‖rotatedCoordinate x axis a‖ := by
    rw [rotatedCoordinate_norm]
    exact mul_pos (norm_pos_iff.mpr haxis) (dist_pos.mpr ha.symm)
  have hnb : 0 < ‖rotatedCoordinate x axis b‖ := by
    rw [rotatedCoordinate_norm]
    exact mul_pos (norm_pos_iff.mpr haxis) (dist_pos.mpr hb.symm)
  exact mul_pos (mul_pos hna hnb)
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg) hgap)

/-- In any actual supporting-edge frame at a donor, the central neighbor's
horizontal coordinate has absolute value at most half its normalized radius. -/
theorem central_neighbor_re_bound_of_support {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k)) :
    |(edgeCoordinate (p u) (p s) (p ctx.q)).re| ≤
      (pairDist p ctx.minPair / dist (p u) (p s)) / 2 := by
  obtain ⟨v, hvinj, _hvrange, hvadj, hvmono, _hgap01, _hgap12, hvlo, hvhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp ctx.diameter_adj ctx.degree_three
  have hmiddle : v 1 = ctx.q := ctx.central_unique (v 1) (hvadj 1) hvlo hvhi
  have hhalf (i : Fin 3) :
      0 < inner ℝ (p ctx.j - p u) (p (v i) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp ctx.diameter_adj (hvadj i).ne
  have haxis : p ctx.j - p u ≠ 0 := by
    intro h
    have := hhalf 0
    simp [h] at this
  have hturn (i j : Fin 3) (hij : i < j) :
      0 < turn (p u) (p (v i)) (p (v j)) := by
    apply turn_pos_of_halfplaneArg_lt (p u) (p ctx.j - p u) _ _ haxis
      (hp.ne (hvadj i).ne.symm) (hp.ne (hvadj j).ne.symm) (hvmono i j hij)
    have hlo := (halfplaneArg_mem_Ioo (hhalf i)).1
    have hhi := (halfplaneArg_mem_Ioo (hhalf j)).2
    linarith
  let M := edgeCoordinate (p u) (p s)
  let r := pairDist p ctx.minPair / dist (p u) (p s)
  have hL : 0 < dist (p u) (p s) := dist_pos.mpr (hp.ne hus)
  have hr : 0 < r := div_pos (pairDist_pos p hp ctx.minPair_spec.1) hL
  have hnorm (i : Fin 3) : ‖M (p (v i))‖ = r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ (hp.ne hus),
      nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj i)]
  have him (i : Fin 3) : 0 ≤ (M (p (v i))).im := by
    have heq := edgeCoordinate_im_mul_dist_sq (p u) (p s) (p (v i)) (hp.ne hus)
    have hs := hsupport (v i)
    change (M (p (v i))).im * dist (p u) (p s) ^ 2 = _ at heq
    nlinarith [sq_pos_of_pos hL]
  have hcross (i j : Fin 3) (hij : i < j) :
      0 < (conj (M (p (v i))) * M (p (v j))).im := by
    dsimp [M]
    rw [edgeCoordinate_cross_eq_turn_div]
    exact div_pos (hturn i j hij) (sq_pos_of_pos hL)
  have hsep (i j : Fin 3) (hij : i ≠ j) : r ≤ dist (M (p (v i))) (M (p (v j))) := by
    dsimp [M, r]
    rw [edgeCoordinate_dist _ _ _ _ (hp.ne hus)]
    exact div_le_div_of_nonneg_right
      (isMinPair_le_dist p ctx.minPair_spec (hvinj.ne hij)) hL.le
  have h := upper_circle_middle_re_bound (M (p (v 0))) (M (p (v 1))) (M (p (v 2)))
    r hr (hnorm 0) (hnorm 1) (hnorm 2) (him 0) (him 1) (him 2)
    (hcross 0 1 (by decide)) (hcross 1 2 (by decide))
    (hsep 0 1 (by decide)) (hsep 1 2 (by decide))
  simpa only [hmiddle] using h

/-- A nearly horizontal point at least `1.98` radii away cannot lie on the
radius circle about a center with horizontal projection at most half a radius. -/
theorem flat_far_chord_not_on_central_circle (Q W : ℂ) (r : ℝ) (hr : 0 < r)
    (hQ : ‖Q‖ = r) (hQr : |Q.re| ≤ r / 2)
    (hWfar : (198 / 100 : ℝ) * r ≤ |W.re|)
    (hWslope : |W.im| ≤ |W.re| / 30) : ‖W - Q‖ ≠ r := by
  intro hWQ
  have hQi : |Q.im| ≤ r := by simpa only [hQ] using Complex.abs_im_le_norm Q
  have hQsq : Q.re ^ 2 + Q.im ^ 2 = r ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two, hQ] using Complex.normSq_eq_norm_sq Q
  have hWQsq : (W.re - Q.re) ^ 2 + (W.im - Q.im) ^ 2 = r ^ 2 := by
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two, hWQ]
      using Complex.normSq_eq_norm_sq (W - Q)
  have hre : Q.re * W.re ≤ r / 2 * |W.re| := calc
    Q.re * W.re ≤ |Q.re * W.re| := le_abs_self _
    _ = |Q.re| * |W.re| := abs_mul _ _
    _ ≤ r / 2 * |W.re| := mul_le_mul_of_nonneg_right hQr (abs_nonneg _)
  have him : Q.im * W.im ≤ r * (|W.re| / 30) := calc
    Q.im * W.im ≤ |Q.im * W.im| := le_abs_self _
    _ = |Q.im| * |W.im| := abs_mul _ _
    _ ≤ r * (|W.re| / 30) := mul_le_mul hQi hWslope (abs_nonneg _) hr.le
  have hpos : 0 < |W.re| := by linarith
  have hlarge : (16 / 15 : ℝ) * r < |W.re| := by linarith
  have hstrict := mul_pos hpos (sub_pos.mpr hlarge)
  nlinarith [sq_abs W.re, sq_nonneg W.im]

private theorem two_small_vectors_projection (z₁ z₂ : ℂ) (r : ℝ)
    (h₁ : r ≤ ‖z₁‖) (h₂ : r ≤ ‖z₂‖)
    (ha₁ : |z₁.arg| ≤ Real.pi / 600) (ha₂ : |z₂.arg| ≤ Real.pi / 600) :
    (198 / 100 : ℝ) * r ≤ (z₁ + z₂).re ∧
      |(z₁ + z₂).im| ≤ (z₁ + z₂).re / 30 := by
  obtain ⟨hp₁, hs₁⟩ := small_arg_projection z₁ ha₁
  obtain ⟨hp₂, hs₂⟩ := small_arg_projection z₂ ha₂
  simp only [Complex.add_re, Complex.add_im]
  constructor
  · linarith
  · have h := abs_add_le z₁.im z₂.im
    linarith

/-- At a tight-flat donor, neither hull vertex two steps away can be adjacent
to the donor's actual central neighbor. The supporting hull edge need not be
a nearest edge. -/
theorem tight_flat_central_neighbor_not_adjacent_two_step {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j) (i : Fin h)
    (ctx : DonorContext p (tightHullBadVertices p v) (v i)) (w : Fin n)
    (hw : w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1)) :
    ¬ (nearestGraph p).Adj ctx.q w := by
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let r := pairDist p ctx.minPair / dist (p (v i)) (p (v (i + 1)))
  let D := fun j => hullEdgeDirection p v j / hullEdgeDirection p v i
  have hus : v i ≠ v (i + 1) := hv.ne (cyclic_three_distinct hh i).1
  have hL : 0 < dist (p (v i)) (p (v (i + 1))) := dist_pos.mpr (hp.ne hus)
  have hr : 0 < r := div_pos (pairDist_pos p hp ctx.minPair_spec.1) hL
  have hQ : ‖M (p ctx.q)‖ = r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ (hp.ne hus),
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj]
  have hQr : |(M (p ctx.q)).re| ≤ r / 2 :=
    central_neighbor_re_bound_of_support p hn hp ctx hus (hsupport i)
  have hnormedge (j : Fin h) : ‖hullEdgeDirection p v j‖ =
      dist (p (v j)) (p (v (j + 1))) := by
    rw [hullEdgeDirection, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  have hD (j : Fin h) : r ≤ ‖D j‖ := by
    dsimp [D, r]
    rw [norm_div, hnormedge, hnormedge]
    exact div_le_div_of_nonneg_right
      (isMinPair_le_dist p ctx.minPair_spec (hv.ne (cyclic_three_distinct hh j).1)) hL.le
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i ctx.outside_bad
  have ha := tight_hull_nearby_edge_args p hp v hv hh i hpos hi hm1 hm2 hp1 hp2
  have h0 : |(D i).arg| ≤ Real.pi / 600 := by
    dsimp [D]
    rw [div_self (hullEdgeDirection_ne_zero p hp v hv hh i), Complex.arg_one, abs_zero]
    positivity
  have h1 : |(D (i + 1)).arg| ≤ Real.pi / 600 := ha _ (Or.inl rfl)
  have hm1 : |(D (i - 1)).arg| ≤ Real.pi / 600 :=
    ha _ (Or.inr (Or.inr (Or.inl rfl)))
  have hm2 : |(D ((i - 1) - 1)).arg| ≤ Real.pi / 600 :=
    ha _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hedge (j : Fin h) : M (p (v (j + 1))) - M (p (v j)) = D j := by
    dsimp [M, D]
    rw [edgeCoordinate_sub]
    rfl
  have hM0 : M (p (v i)) = 0 := by simp [M, edgeCoordinate]
  have hW : (198 / 100 : ℝ) * r ≤ |(M (p w)).re| ∧
      |(M (p w)).im| ≤ |(M (p w)).re| / 30 := by
    rcases hw with rfl | rfl
    · have hsum : M (p (v ((i + 1) + 1))) = D i + D (i + 1) := by
        have he1 := hedge i
        have he2 := hedge (i + 1)
        rw [hM0, sub_zero] at he1
        rw [← he1, ← he2]
        ring
      have hs := two_small_vectors_projection _ _ r (hD i) (hD (i + 1)) h0 h1
      have hspos : 0 ≤ (D i + D (i + 1)).re := by linarith [hs.1]
      simpa only [hsum, abs_of_nonneg hspos] using hs
    · have hsum : M (p (v ((i - 1) - 1))) = -(D (i - 1) + D ((i - 1) - 1)) := by
        have he1 := hedge (i - 1)
        have he2 := hedge ((i - 1) - 1)
        simp only [sub_add_cancel, hM0] at he1 he2
        rw [← he1, ← he2]
        ring
      have hs := two_small_vectors_projection _ _ r (hD (i - 1))
        (hD ((i - 1) - 1)) hm1 hm2
      have hspos : 0 ≤ (D (i - 1) + D ((i - 1) - 1)).re := by linarith [hs.1]
      simpa only [hsum, Complex.neg_re, Complex.neg_im, abs_neg, abs_of_nonneg hspos]
        using hs
  intro hqw
  apply flat_far_chord_not_on_central_circle (M (p ctx.q)) (M (p w)) r hr hQ hQr hW.1 hW.2
  rw [← dist_eq_norm]
  dsimp [M, r]
  rw [edgeCoordinate_dist _ _ _ _ (hp.ne hus),
    nearestGraph_adj_dist_eq p ctx.minPair_spec hqw.symm]

end Erdos957
