import CertifiedDonorRules
import PacketMetricLocality
import TightFlatChord

/-! Actual supporting-edge rectangles for every retained donor rule. -/

namespace Erdos957

/-- Each certified transfer is direct, or retains a nearest diameter partner
whose donor-centered frame places the receiver in a fixed rectangle. -/
theorem CertifiedDonorRule.positive_adj_or_shared_base {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {u q : Fin n} {height : Fin n → ℝ} (rule : CertifiedDonorRule p u q height)
    (x : Fin n) (hx : 0 < rule.packet.weight x) :
    (nearestGraph p).Adj u x ∨
      ∃ w, w ∈ diameterEndpoints p ∧ (nearestGraph p).Adj u w ∧
        |(edgeCoordinate (p u) (p w) (p x)).re| ≤ 3 / 2 ∧
        |(edgeCoordinate (p u) (p w) (p x)).im| ≤ 2 := by
  classical
  cases rule with
  | low choice => exact Or.inl (choice.positive_geometry hx).1
  | unique choice _ => exact Or.inl (choice.positive_adj x hx)
  | sharedFive available hu hqu =>
    let choice := selectedSharedFiveCenter p q available
    change 0 < (choice.packetFor u hu hqu).weight x at hx
    rw [choice.packetFor_weight] at hx
    rcases choice.diameter_neighbor_cases u hu hqu with hl | hr
    · subst u
      have hfirst : 0 < choice.selection.first.weight x := by
        simpa [SharedFiveCenterChoice.charge, choice.base.ne] using hx
      obtain ⟨hxlo, hxhi, hylo, hyhi⟩ :=
        choice.selection.receivers_in_rectangle x (Or.inl hfirst)
      exact Or.inr ⟨choice.right, choice.right_diameter, choice.base,
        abs_le.mpr ⟨by linarith, hxhi⟩, abs_le.mpr ⟨hylo, by linarith⟩⟩
    · subst u
      have hsecond : 0 < choice.selection.second.weight x := by
        simpa [SharedFiveCenterChoice.charge, choice.base.ne.symm] using hx
      obtain ⟨hxlo, hxhi, hylo, hyhi⟩ :=
        choice.selection.receivers_in_rectangle x (Or.inr hsecond)
      refine Or.inr ⟨choice.left, choice.left_diameter, choice.base.symm, ?_, ?_⟩
      all_goals rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
      · simp only [Complex.sub_re, Complex.one_re]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
        exact abs_le.mpr ⟨hylo, by linarith⟩
  | sharedSix choice =>
    obtain ⟨hxlo, hxhi, hylo, hyhi, _⟩ := choice.receivers_in_region x hx
    refine Or.inr ⟨_, choice.partner_diameter, choice.base.symm, ?_, ?_⟩
    all_goals rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
    · simp only [Complex.sub_re, Complex.one_re]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact abs_le.mpr ⟨hylo, by linarith⟩
  | reflectedSharedSix choice =>
    rename_i w
    have hG := nearestGraph_eq_of_dist_eq p (fun k => planeReflection (p k))
      (fun a b => planeReflection.dist_map (p a) (p b))
    have hD := diameterEndpoints_eq_of_dist_eq p (fun k => planeReflection (p k))
      (fun a b => planeReflection.dist_map (p a) (p b))
    have hbase : (nearestGraph p).Adj w u := by
      simpa only [hG] using choice.reflected.base
    have hpartner : w ∈ diameterEndpoints p := by
      simpa only [hD] using choice.reflected.partner_diameter
    obtain ⟨hxlo, hxhi, hylo, hyhi, _⟩ := choice.receivers_in_original_region x hx
    refine Or.inr ⟨_, hpartner, hbase.symm, ?_, ?_⟩
    all_goals rw [edgeCoordinate_swap_base _ _ _ (hp.ne hbase.ne)]
    · simp only [Complex.sub_re, Complex.one_re]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact abs_le.mpr ⟨by linarith, hyhi⟩

/-- Changing only the second base point multiplies normalized coordinates. -/
theorem edgeCoordinate_mul_base_change (u w s x : Point) (huw : u ≠ w) :
    edgeCoordinate u s x = edgeCoordinate u w x * edgeCoordinate u s w := by
  have hb : pointToComplex (w - u) ≠ 0 := by
    intro hzero
    have heq : w - u = 0 := pointToComplex.injective (by simpa using hzero)
    exact huw (sub_eq_zero.mp heq).symm
  simp only [edgeCoordinate]
  field_simp

private theorem re_mul_bound (z a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hzre : |z.re| ≤ 3 / 2) (hzim : |z.im| ≤ 2)
    (ha : ‖a‖ = r) (haim : |a.im| ≤ r / 30) :
    |(z * a).re| ≤ (7 / 4 : ℝ) * r := by
  have hare : |a.re| ≤ r := by simpa only [ha] using Complex.abs_re_le_norm a
  calc
    |(z * a).re| = |z.re * a.re - z.im * a.im| := by rw [Complex.mul_re]
    _ ≤ |z.re * a.re| + |z.im * a.im| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (z.re * a.re) (-(z.im * a.im))
    _ = |z.re| * |a.re| + |z.im| * |a.im| := by rw [abs_mul, abs_mul]
    _ ≤ (3 / 2 : ℝ) * r + 2 * (r / 30) := add_le_add
      (mul_le_mul hzre hare (abs_nonneg _) (by norm_num))
      (mul_le_mul hzim haim (abs_nonneg _) (by norm_num))
    _ ≤ (7 / 4 : ℝ) * r := by linarith

private theorem tight_flat_adjacent_nearest_im_bound {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j) (i : Fin h)
    (hgood : v i ∉ tightHullBadVertices p v) (w : Fin n)
    (huw : (nearestGraph p).Adj (v i) w)
    (hwhere : w = v (i + 1) ∨ w = v (i - 1)) :
    |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p w)).im| ≤
      (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) / 30 := by
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let r := pairDist p ij / dist (p (v i)) (p (v (i + 1)))
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hnorm : ‖M (p w)‖ = r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ hne, nearestGraph_adj_dist_eq p hmin huw]
  have hr : 0 ≤ r := div_nonneg dist_nonneg dist_nonneg
  change |(M (p w)).im| ≤ r / 30
  rcases hwhere with rfl | rfl
  · have hM : M (p (v (i + 1))) = 1 := by
      change pointToComplex (p (v (i + 1)) - p (v i)) /
        pointToComplex (p (v (i + 1)) - p (v i)) = 1
      exact div_self (fun heq => hne
        (sub_eq_zero.mp (pointToComplex.injective (by simpa using heq))).symm)
    rw [hM, Complex.one_im, abs_zero]
    positivity
  · obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
      tight_hull_five_turns_of_not_bad p v hv i hgood
    have ha := tight_hull_nearby_edge_args p hp v hv hh i hpos hi hm1 hm2 hp1 hp2
    let a := hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i
    have hsmall : |a.arg| ≤ Real.pi / 600 := ha _ (Or.inr (Or.inr (Or.inl rfl)))
    have hMa : M (p (v (i - 1))) = -a := by
      simp only [M, a, edgeCoordinate, hullEdgeDirection, sub_add_cancel]
      rw [← neg_div, ← map_neg]
      congr 2
      abel
    have hanorm : ‖a‖ = r := by simpa only [hMa, norm_neg] using hnorm
    have hbound := (small_arg_projection a hsmall).2
    have hare : a.re ≤ r := by simpa only [hanorm] using Complex.re_le_norm a
    rw [hMa, Complex.neg_im, abs_neg]
    linarith

/-- Every positive certified transfer lies in the donor's actual outgoing
supporting-edge rectangle, at the normalized minimum-distance scale. -/
theorem certifiedDonorRule_supporting_rectangle {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j) (i : Fin h)
    (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (height : Fin n → ℝ) (rule : CertifiedDonorRule p (v i) ctx.q height)
    (x : Fin n) (hx : 0 < rule.packet.weight x) :
    let M := edgeCoordinate (p (v i)) (p (v (i + 1)));
    let r := pairDist p ctx.minPair / dist (p (v i)) (p (v (i + 1)));
    |(M (p x)).re| ≤ (7 / 4 : ℝ) * r ∧
      0 ≤ (M (p x)).im ∧ (M (p x)).im ≤ 2 * r := by
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let r := pairDist p ctx.minPair / dist (p (v i)) (p (v (i + 1)))
  change |(M (p x)).re| ≤ (7 / 4 : ℝ) * r ∧
    0 ≤ (M (p x)).im ∧ (M (p x)).im ≤ 2 * r
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL := dist_pos.mpr hne
  have hr : 0 ≤ r := div_nonneg dist_nonneg dist_nonneg
  have hnorm : ‖M (p x)‖ ≤ 2 * r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ hne]
    have h := div_le_div_of_nonneg_right
      (rule.packet.positive_dist_le_two_min ctx.minPair_spec hx) hL.le
    simpa only [mul_div_assoc] using h
  refine ⟨?_, ?_, (Complex.im_le_norm _).trans hnorm⟩
  · rcases rule.positive_adj_or_shared_base p hp x hx with hux | ⟨w, hwD, huw, hxre, hxim⟩
    · have hnormone : ‖M (p x)‖ = r := by
        dsimp [M, r]
        rw [edgeCoordinate_norm _ _ _ hne, nearestGraph_adj_dist_eq p ctx.minPair_spec hux]
      have h := Complex.abs_re_le_norm (M (p x))
      rw [hnormone] at h
      linarith
    · have hwhere := nearest_diameter_endpoints_cyclic_adjacent_of_large_card
        p hp hn v hv hh hrange hsupport i w ctx.endpoint hwD huw
      have haim : |(M (p w)).im| ≤ r / 30 :=
        tight_flat_adjacent_nearest_im_bound p hp v hv hh ctx.minPair ctx.minPair_spec
          hpos i ctx.outside_bad w huw hwhere
      have hanorm : ‖M (p w)‖ = r := by
        dsimp [M, r]
        rw [edgeCoordinate_norm _ _ _ hne, nearestGraph_adj_dist_eq p ctx.minPair_spec huw]
      have hchange : M (p x) = edgeCoordinate (p (v i)) (p w) (p x) * M (p w) :=
        edgeCoordinate_mul_base_change _ _ _ _ (hp.ne huw.ne)
      rw [hchange]
      exact re_mul_bound _ _ r hr hxre hxim hanorm haim
  · have heq := edgeCoordinate_im_mul_dist_sq (p (v i)) (p (v (i + 1))) (p x) hne
    have hs := hsupport i x
    change (M (p x)).im * dist (p (v i)) (p (v (i + 1))) ^ 2 = _ at heq
    nlinarith [sq_pos_of_pos hL]

end Erdos957
