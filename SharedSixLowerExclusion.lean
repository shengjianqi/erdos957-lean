import CertifiedSharedSix
import SharedFiveCenterFamily
import CertifiedSourceLocality
import DeepReceiverExclusion

/-! The two upper neighbors of a shared-six lower site exclude other upper
unit neighbors. The outer neighbor cannot be a shared-five center. -/

namespace Erdos957

/-- Two separated upper equilateral directions block every other upper
unit direction. The separation assumptions exclude the two blockers themselves. -/
theorem unit_circle_two_upper_blockers_im_nonpos (z : ℂ) (h : ℝ)
    (hh : 0 < h) (hsq : h ^ 2 = 3 / 4) (hz : ‖z‖ = 1)
    (hleft : 1 ≤ ‖z - ((-1 / 2 : ℂ) + (h : ℂ) * Complex.I)‖)
    (hright : 1 ≤ ‖z - ((1 / 2 : ℂ) + (h : ℂ) * Complex.I)‖) :
    z.im ≤ 0 := by
  have norm_square (a : ℂ) : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq a
  have hzsq := norm_square z
  rw [hz] at hzsq
  have hl := norm_square (z - ((-1 / 2 : ℂ) + (h : ℂ) * Complex.I))
  have hr := norm_square (z - ((1 / 2 : ℂ) + (h : ℂ) * Complex.I))
  norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hl hr
  have hlsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr hleft
  have hrsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr hright
  have hcone : |z.re| + 2 * h * z.im ≤ 1 := by
    rcases le_total 0 z.re with hre | hre
    · rw [abs_of_nonneg hre]
      nlinarith only [hzsq, hr, hrsq, hsq]
    · rw [abs_of_nonpos hre]
      nlinarith only [hzsq, hl, hlsq, hsq]
  by_contra hnot
  have hy : 0 < z.im := lt_of_not_ge hnot
  have hyone : z.im ≤ 1 := by simpa only [hz] using Complex.im_le_norm z
  have hprod := mul_nonneg (sub_nonneg.mpr hcone)
    (by positivity : 0 ≤ 1 + |z.re|)
  have htriple := mul_nonneg (mul_nonneg hh.le hy.le) (abs_nonneg z.re)
  have hgap := mul_pos (by nlinarith only [hsq, hh] : 0 < 2 * h - 1) hy
  have hyy := mul_nonneg hy.le (sub_nonneg.mpr hyone)
  nlinarith only [hzsq, hprod, htriple, hgap, hyy, sq_abs z.re]

/-- In the retained shared-six frame, the only nearest neighbors strictly
above the lower site are the center and the outer site. -/
theorem SharedSixPacketChoice.lower_adj_above_cases {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q : Fin n} (choice : SharedSixPacketChoice p u w q)
    (k : Fin n) (hk : (nearestGraph p).Adj choice.lower k)
    (habove : (edgeCoordinate (p u) (p w) (p choice.lower)).im <
      (edgeCoordinate (p u) (p w) (p k)).im) :
    k = q ∨ k = choice.outer := by
  by_cases hkq : k = q
  · exact Or.inl hkq
  by_cases hkb : k = choice.outer
  · exact Or.inr hkb
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hd : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hbase := nearestGraph_adj_dist_eq p hmin choice.base
  have hne : p u ≠ p w := hp.ne choice.base.ne
  let M := fun a => edgeCoordinate (p u) (p w) (p a)
  let z := M k - M choice.lower
  have hz : ‖z‖ = 1 := by
    rw [show ‖z‖ = dist (M k) (M choice.lower) by simp only [z, dist_eq_norm]]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, hbase,
      nearestGraph_adj_dist_eq p hmin hk.symm, div_self hd.ne']
  have hq : M q - M choice.lower =
      (-1 / 2 : ℂ) + (choice.height : ℂ) * Complex.I := by
    change edgeCoordinate (p u) (p w) (p q) -
      edgeCoordinate (p u) (p w) (p choice.lower) = _
    rw [choice.center_coordinate, choice.lower_coordinate]
    push_cast
    ring
  have hb : M choice.outer - M choice.lower =
      (1 / 2 : ℂ) + (choice.height : ℂ) * Complex.I := by
    change edgeCoordinate (p u) (p w) (p choice.outer) -
      edgeCoordinate (p u) (p w) (p choice.lower) = _
    rw [choice.outer_coordinate, choice.lower_coordinate]
    push_cast
    ring
  have hsep (a : Fin n) (hka : k ≠ a) : 1 ≤ ‖z - (M a - M choice.lower)‖ := by
    rw [show z - (M a - M choice.lower) = M k - M a by dsimp [z]; abel,
      ← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, hbase]
    exact (le_div_iff₀ hd).mpr (by simpa only [one_mul] using isMinPair_le_dist p hmin hka)
  have him := unit_circle_two_upper_blockers_im_nonpos z choice.height
    choice.height_pos choice.height_sq hz
    (by rw [← hq]; exact hsep q hkq)
    (by rw [← hb]; exact hsep choice.outer hkb)
  change (M choice.lower).im < (M k).im at habove
  change (M k - M choice.lower).im ≤ 0 at him
  simp only [Complex.sub_im] at him
  exact False.elim (by linarith)

/-- The outer site cannot be a shared-five center: the second diameter
neighbor would make the original source a forbidden midpoint. -/
theorem SharedSixPacketChoice.outer_not_sharedFive_center {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q : Fin n} (choice : SharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w) :
    ¬ Nonempty (SharedFiveCenterChoice p choice.outer) := by
  rintro ⟨five⟩
  have hwhere := five.diameter_neighbor_cases w hw choice.outer_adj_source.symm
  obtain ⟨a, haD, hwa, hba⟩ : ∃ a, a ∈ diameterEndpoints p ∧
      (nearestGraph p).Adj w a ∧ (nearestGraph p).Adj choice.outer a := by
    rcases hwhere with hl | hr
    · exact ⟨five.right, five.right_diameter, by simpa only [hl] using five.base, five.center_right⟩
    · exact ⟨five.left, five.left_diameter, by simpa only [hr] using five.base.symm, five.center_left⟩
  have haq : a ≠ q := by
    intro heq
    have hdeg := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp a haD
    rw [heq, choice.center_degree] at hdeg
    omega
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have hrhombus := equilateral_rhombus (p w) (p choice.outer) (p q) (p a)
    (pairDist p ij) hr
    (nearestGraph_adj_dist_eq p hmin choice.outer_adj_source)
    (nearestGraph_adj_dist_eq p hmin hqw.symm)
    (nearestGraph_adj_dist_eq p hmin choice.outer_adj_center.symm)
    (nearestGraph_adj_dist_eq p hmin hwa)
    (nearestGraph_adj_dist_eq p hmin hba) (hp.ne haq.symm)
  apply diameterEndpoint_not_midpoint p hp hw choice.base.ne.symm hwa.ne
  rw [two_smul]
  calc
    p u + p a = p u + (p q + p a) - p q := by abel
    _ = p u + (p w + p choice.outer) - p q := by rw [hrhombus]
    _ = (p u + p choice.outer) + p w - p q := by abel
    _ = (p q + p w) + p w - p q := by rw [choice.outer_identity]
    _ = p w + p w := by abel

/-- A shared-five bottom cannot be the shared-six lower site when its
center is strictly above that site in the shared-six supporting frame.
This theorem retains that alignment premise explicitly. -/
theorem SharedSixPacketChoice.sharedFive_bottom_ne_lower_of_center_above {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w)
    (five : SharedFiveCenterChoice p qfive)
    (habove : (edgeCoordinate (p u) (p w) (p choice.lower)).im <
      (edgeCoordinate (p u) (p w) (p qfive)).im) :
    five.selection.bottom ≠ choice.lower := by
  intro heq
  have hadj : (nearestGraph p).Adj choice.lower qfive := by
    simpa only [heq] using five.selection.bottom_adj.symm
  rcases choice.lower_adj_above_cases p hn hp qfive hadj habove with hc | hb
  · have hdeg := five.center_degree
    rw [hc, choice.center_degree] at hdeg
    omega
  · subst qfive
    exact choice.outer_not_sharedFive_center p hn hp hw hqw ⟨five⟩

/-- In the actual tight-flat hull, a selected shared-six lower receiver is
never the bottom of another retained shared-five center. The supporting-frame
alignment is derived, and neither shared-five endpoint has to be a donor. -/
theorem tight_flat_sharedSix_selected_lower_ne_sharedFive_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hselected : choice.packet.right = choice.lower)
    (five : SharedFiveCenterChoice p qfive) :
    five.selection.bottom ≠ choice.lower := by
  intro heq
  let M := fun k => edgeCoordinate (p (v i)) (p (v (i + 1))) (p k)
  let r := pairDist p ctx.minPair / dist (p (v i)) (p (v (i + 1)))
  let Z := fun k => edgeCoordinate (p partner) (p (v i)) (p k)
  let A := -M partner
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL := dist_pos.mpr hne
  have hdelta := pairDist_pos p hp ctx.minPair_spec.1
  have hr : 0 < r := div_pos hdelta hL
  have hdist := nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base.symm
  have hnear : dist (p (v i)) (p partner) ≤ 2 * pairDist p ctx.minPair := by
    rw [hdist]
    linarith
  have hwhere := tight_flat_nearby_diameter_endpoint_local p hp hn v hv hh hsupport hpos
    ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint partner choice.partner_diameter hnear
  have hslope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i ctx.outside_bad partner
    (by tauto)
  have hAnorm : ‖A‖ = r := by
    dsimp [A, M, r]
    rw [norm_neg, edgeCoordinate_norm _ _ _ hne, hdist]
  have hARe : |A.re| ≤ r := by simpa only [hAnorm] using Complex.abs_re_le_norm A
  have hAim : |A.im| ≤ r / 30 := by
    change |(M partner).im| ≤ |(M partner).re| / 30 at hslope
    dsimp [A] at hARe ⊢
    simp only [abs_neg] at hARe
    simp only [abs_neg]
    linarith
  have hAReLower : 29 * r / 30 ≤ |A.re| := by
    have ht := Complex.norm_le_abs_re_add_abs_im A
    rw [hAnorm] at ht
    linarith
  have hchange (k : Fin n) : M k = (Z k - 1) * A := by
    have ht := edgeCoordinate_mul_base_change (p (v i)) (p partner)
      (p (v (i + 1))) (p k) (hp.ne choice.base.ne.symm)
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)] at ht
    change M k = (1 - Z k) * M partner at ht
    rw [ht]
    dsimp [A]
    ring
  have hMQ : M ctx.q = ((-1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * A := by
    rw [hchange]
    change (edgeCoordinate (p partner) (p (v i)) (p ctx.q) - 1) * A = _
    rw [choice.center_coordinate]
    ring
  have hQpos : 0 ≤ (M ctx.q).im := by
    have ht := edgeCoordinate_im_mul_dist_sq (p (v i)) (p (v (i + 1))) (p ctx.q) hne
    have hs := hsupport i ctx.q
    change (M ctx.q).im * dist (p (v i)) (p (v (i + 1))) ^ 2 = _ at ht
    nlinarith only [ht, hs, sq_pos_of_pos hL]
  have hheight : (4 / 5 : ℝ) ≤ choice.height := by
    nlinarith [choice.height_pos, choice.height_sq]
  have hAre : A.re ≤ 0 := by
    by_contra hnot
    have ha : 0 < A.re := lt_of_not_ge hnot
    rw [abs_of_pos ha] at hAReLower
    rw [hMQ] at hQpos
    norm_num [Complex.mul_im, Complex.mul_re] at hQpos
    have hhprod := mul_le_mul_of_nonneg_right hheight ha.le
    have hlo := (abs_le.mp hAim).1
    nlinarith only [hQpos, hhprod, hlo, hAReLower, hr]
  have hML : M choice.lower = -((2 * choice.height : ℝ) : ℂ) * Complex.I * A := by
    rw [hchange]
    change (edgeCoordinate (p partner) (p (v i)) (p choice.lower) - 1) * A = _
    rw [choice.lower_coordinate]
    ring
  have hdeep : (3 / 2 : ℝ) * r ≤ (M choice.lower).im := by
    rw [abs_of_nonpos hAre] at hAReLower
    rw [hML]
    norm_num [Complex.mul_im, Complex.mul_re]
    have hprod := mul_le_mul_of_nonneg_right hheight (neg_nonneg.mpr hAre)
    nlinarith only [hAReLower, hprod, hr]
  have hpositive : 0 < choice.packet.weight choice.lower := by
    rw [← hselected, choice.site_weights.2]
    omega
  let rule : CertifiedDonorRule p (v i) ctx.q (fun _ => 0) := .sharedSix choice
  have hrect := certifiedDonorRule_supporting_rectangle p hp hn v hv hh hrange
    hsupport hpos i ctx (fun _ => 0) rule choice.lower hpositive
  have hfirst : five.selection.first.right = choice.lower := by
    rcases five.selection.branch with ⟨_, ht, _⟩ | ⟨hsix, _⟩
    · exact ht.trans heq
    · have hlow := choice.packet.right_degree
      rw [hselected, ← heq, hsix] at hlow
      omega
  have hfpos : 0 < five.selection.first.weight choice.lower := by
    simp [LocalChargePacket.weight, hfirst]
  have hdwhere := certified_rule_common_receiver_source_local p hp hn v hv hh hrange
    hsupport hpos i ctx (fun _ => 0) rule five.left five.left_diameter
    five.selection.first choice.lower hpositive hfpos
  have hdSlope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i ctx.outside_bad
    five.left ((mem_hullSourceNeighborhood_iff v i five.left).mp hdwhere)
  have hdRe := packet_source_horizontal_bound p (v i) (v (i + 1)) five.left choice.lower
    hne ctx.minPair ctx.minPair_spec five.selection.first hfpos hrect.1
  change |(M five.left).im| ≤ |(M five.left).re| / 30 at hdSlope
  change |(M five.left).re| ≤ (15 / 4 : ℝ) * r at hdRe
  have hdIm : (M five.left).im ≤ r / 8 := by
    linarith [le_abs_self (M five.left).im]
  have hQdNorm : ‖M qfive - M five.left‖ = r := by
    rw [← dist_eq_norm]
    dsimp [M, r]
    rw [edgeCoordinate_dist _ _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec five.center_left]
  have hQdIm : (M qfive).im - (M five.left).im ≤ r := by
    have ht := Complex.im_le_norm (M qfive - M five.left)
    simpa only [Complex.sub_im, hQdNorm] using ht
  have hQshallow : (M qfive).im ≤ (9 / 8 : ℝ) * r := by linarith
  have habove : (Z choice.lower).im < (Z qfive).im := by
    by_contra hnot
    let z := Z qfive - Z choice.lower
    have hzim : z.im ≤ 0 := by
      change (Z qfive - Z choice.lower).im ≤ 0
      simp only [Complex.sub_im]
      exact sub_nonpos.mpr (le_of_not_gt hnot)
    have hznorm : ‖z‖ = 1 := by
      rw [show ‖z‖ = dist (Z qfive) (Z choice.lower) by simp only [z, dist_eq_norm]]
      dsimp [Z]
      rw [edgeCoordinate_dist _ _ _ _ (hp.ne choice.base.ne),
        nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base]
      have hqbottom := nearestGraph_adj_dist_eq p ctx.minPair_spec five.selection.bottom_adj
      rw [heq] at hqbottom
      rw [hqbottom, div_self hdelta.ne']
    have hzre : |z.re| ≤ 1 := by simpa only [hznorm] using Complex.abs_re_le_norm z
    have herr : |z.re * A.im| ≤ r / 30 := by
      rw [abs_mul]
      exact (mul_le_mul hzre hAim (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have hmain := mul_nonneg_of_nonpos_of_nonpos hzim hAre
    have hmul : -(r / 30) ≤ (z * A).im := by
      rw [Complex.mul_im]
      have hlo := (abs_le.mp herr).1
      linarith
    have hdiff : M qfive - M choice.lower = z * A := by
      rw [hchange, hchange]
      dsimp [z]
      ring
    rw [← hdiff, Complex.sub_im] at hmul
    linarith only [hmul, hdeep, hQshallow, hr]
  exact choice.sharedFive_bottom_ne_lower_of_center_above p (by omega) hp
    ctx.endpoint ctx.central_adj.symm five habove heq

end Erdos957
