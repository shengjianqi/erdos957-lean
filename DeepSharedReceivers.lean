import DeepReceiverExclusion
import SupportingPacketFrames
import DirectChargeAccounting
import TightFlatDiameterLocality

/-! Deep receivers in a nearest diameter-partner frame remain deep in the
actual supporting frame, and therefore have no direct incoming charge. -/

namespace Erdos957

/-- A nearly horizontal change of base preserves a sufficient depth margin.
Both signs of the base direction and of the original depth are allowed. -/
theorem deep_coordinate_mul_im_bound (z a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hzre : |z.re| ≤ 2) (hzim : (5 / 3 : ℝ) ≤ |z.im|)
    (ha : ‖a‖ = r) (haim : |a.im| ≤ r / 30) :
    (3 / 2 : ℝ) * r ≤ |(z * a).im| := by
  have hare : 29 * r / 30 ≤ |a.re| := by
    have ht := Complex.norm_le_abs_re_add_abs_im a
    rw [ha] at ht
    linarith
  have hmain : (5 / 3 : ℝ) * (29 * r / 30) ≤ |z.im| * |a.re| :=
    mul_le_mul hzim hare (by positivity) (abs_nonneg _)
  have herror : |z.re| * |a.im| ≤ 2 * (r / 30) :=
    mul_le_mul hzre haim (abs_nonneg _) (by norm_num)
  have htriangle : |z.im| * |a.re| ≤ |(z * a).im| + |z.re| * |a.im| := by
    calc
      |z.im| * |a.re| = |(z * a).im - z.re * a.im| := by
        rw [← abs_mul, Complex.mul_im]
        congr 1
        ring
      _ ≤ |(z * a).im| + |z.re * a.im| := abs_sub _ _
      _ = |(z * a).im| + |z.re| * |a.im| := by rw [abs_mul]
  linarith

/-- Depth in either orientation of a nearest diameter-partner base gives
a quantitative depth in the actual outgoing supporting frame. -/
theorem tight_flat_deep_base_receiver_depth {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (w : Fin n) (hw : w ∈ diameterEndpoints p) (huw : (nearestGraph p).Adj (v i) w)
    (x : Fin n) (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (5 / 3 : ℝ) ≤ |(edgeCoordinate (p (v i)) (p w) (p x)).im|) :
    (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im := by
  let M := fun k => edgeCoordinate (p (v i)) (p (v (i + 1))) (p k)
  let r := pairDist p ij / dist (p (v i)) (p (v (i + 1)))
  let z := edgeCoordinate (p (v i)) (p w) (p x)
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hr : 0 ≤ r := div_nonneg dist_nonneg dist_nonneg
  have hdelta : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hdist := nearestGraph_adj_dist_eq p hmin huw
  have hnear : dist (p (v i)) (p w) ≤ 2 * pairDist p ij := by rw [hdist]; linarith
  have hwhere := tight_flat_nearby_diameter_endpoint_local p hp hn v hv hh
    hsupport hpos ij hmin i hgood hu w hw hnear
  have hslope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood w
    (by tauto)
  have hanorm : ‖M w‖ = r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ hne, hdist]
  have hare : |(M w).re| ≤ r := by simpa only [hanorm] using Complex.abs_re_le_norm (M w)
  have haim : |(M w).im| ≤ r / 30 := by
    change |(M w).im| ≤ |(M w).re| / 30 at hslope
    linarith
  have hznorm : ‖z‖ ≤ 2 := by
    dsimp [z]
    rw [edgeCoordinate_norm _ _ _ (hp.ne huw.ne), hdist]
    exact (div_le_iff₀ hdelta).mpr (by linarith)
  have hzre : |z.re| ≤ 2 := (Complex.abs_re_le_norm z).trans hznorm
  have hchange : M x = z * M w :=
    edgeCoordinate_mul_base_change _ _ _ _ (hp.ne huw.ne)
  have himpos : 0 ≤ (M x).im := by
    have heq := edgeCoordinate_im_mul_dist_sq (p (v i)) (p (v (i + 1))) (p x) hne
    have hs := hsupport i x
    have hL := dist_pos.mpr hne
    change (M x).im * dist (p (v i)) (p (v (i + 1))) ^ 2 = _ at heq
    nlinarith [sq_pos_of_pos hL]
  have hactual : (3 / 2 : ℝ) * r ≤ (M x).im := by
    have hb := deep_coordinate_mul_im_bound z (M w) r hr hzre hdeep hanorm haim
    rw [← hchange, abs_of_nonneg himpos] at hb
    exact hb
  exact hactual

/-- Depth in either orientation of a nearest diameter-partner base excludes
every diameter neighbor at the receiver, using the actual tight-flat hull. -/
theorem tight_flat_deep_base_receiver_no_diameter_neighbor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (w : Fin n) (hw : w ∈ diameterEndpoints p) (huw : (nearestGraph p).Adj (v i) w)
    (x : Fin n) (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (5 / 3 : ℝ) ≤ |(edgeCoordinate (p (v i)) (p w) (p x)).im|) :
    ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p := by
  exact tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose (tight_flat_deep_base_receiver_depth p hp hn v hv hh
      hsupport hpos ij hmin i hgood hu w hw huw x hclose hdeep)

/-- The deepest neighbor of a retained shared-five center has no diameter
neighbor, from either actual good endpoint. This also covers the degree-six
bottom branch where the bottom itself is not selected as a receiver. -/
theorem sharedFive_bottom_no_diameter_neighbor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (q : Fin n) (choice : SharedFiveCenterChoice p q)
    (hsource : v i = choice.left ∨ v i = choice.right) :
    ∀ a, (nearestGraph p).Adj choice.selection.bottom a → a ∉ diameterEndpoints p := by
  have hpath (u : Fin n) (hqu : (nearestGraph p).Adj q u) :
      dist (p u) (p choice.selection.bottom) ≤ 2 * pairDist p ij := by
    have ht := dist_triangle (p u) (p q) (p choice.selection.bottom)
    rw [nearestGraph_adj_dist_eq p hmin hqu.symm,
      nearestGraph_adj_dist_eq p hmin choice.selection.bottom_adj] at ht
    linarith
  have hroot : (5 / 3 : ℝ) ≤ Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hdepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p choice.left) (p choice.right) (p choice.selection.bottom)).im| := by
    have hb := choice.selection.bottom_depth
    have habs := neg_le_abs (edgeCoordinate (p choice.left) (p choice.right)
      (p choice.selection.bottom)).im
    linarith
  rcases hsource with hs | hs
  · apply tight_flat_deep_base_receiver_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos ij hmin i hgood (by simpa only [hs] using choice.left_diameter)
      choice.right choice.right_diameter (by simpa only [hs] using choice.base)
      choice.selection.bottom (by simpa only [hs] using hpath choice.left choice.center_left)
    simpa only [hs] using hdepth
  · apply tight_flat_deep_base_receiver_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos ij hmin i hgood (by simpa only [hs] using choice.right_diameter)
      choice.left choice.left_diameter (by simpa only [hs] using choice.base.symm)
      choice.selection.bottom (by simpa only [hs] using hpath choice.right choice.center_right)
    rw [hs, edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hdepth

/-- The first two shared-six secondary sites are deep; the remaining site
has degree at most four by the retained branch certificate. -/
theorem SharedSixPacketChoice.right_deep_or_degree_le_four {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n} (choice : SharedSixPacketChoice p u w q) :
    (5 / 3 : ℝ) ≤ |(edgeCoordinate (p u) (p w) (p choice.packet.right)).im| ∨
      (nearestGraph p).degree choice.packet.right ≤ 4 := by
  have hh : (5 / 3 : ℝ) ≤ 2 * choice.height := by
    have hp := choice.height_pos
    have hs := choice.height_sq
    nlinarith
  have hd (c : ℝ) (hc : edgeCoordinate (p u) (p w) (p choice.packet.right) =
      (c : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I) :
      (5 / 3 : ℝ) ≤ |(edgeCoordinate (p u) (p w) (p choice.packet.right)).im| := by
    rw [hc]
    simpa [abs_of_pos choice.height_pos] using hh
  rcases choice.branch with ⟨_, ht⟩ | ⟨_, t₂, _, _, _, ht₂, hcases⟩
  · left
    apply hd 1
    simpa [ht] using choice.lower_coordinate
  · rcases hcases with ⟨_, ht⟩ | ⟨_, _, _, _, hfour⟩
    · left
      apply hd 2
      simpa [ht] using ht₂
    · exact Or.inr hfour

theorem ReflectedSharedSixPacketChoice.right_deep_or_degree_le_four {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w q) :
    (5 / 3 : ℝ) ≤ |(edgeCoordinate (p u) (p w) (p choice.packet.right)).im| ∨
      (nearestGraph p).degree choice.packet.right ≤ 4 := by
  have hdeg := nearestGraph_degree_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))
  rcases choice.reflected.right_deep_or_degree_le_four with hdeep | hfour
  · left
    rw [choice.packet_sites.2]
    simpa only [edgeCoordinate_planeReflection, Complex.conj_im, abs_neg] using hdeep
  · exact Or.inr ((hdeg choice.packet.right).symm.le.trans hfour)

/-- The selected shared-six secondary receiver has no direct diameter source,
unless its retained construction already guarantees degree at most four. -/
theorem sharedSix_right_no_diameter_neighbor_or_degree_le_four {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (w : Fin n) (choice : SharedSixPacketChoice p w (v i) ctx.q) :
    (∀ a, (nearestGraph p).Adj choice.packet.right a → a ∉ diameterEndpoints p) ∨
      (nearestGraph p).degree choice.packet.right ≤ 4 := by
  rcases choice.right_deep_or_degree_le_four with hd | hfour
  · left
    apply tight_flat_deep_base_receiver_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint
      w choice.partner_diameter choice.base.symm choice.packet.right
      (choice.packet.positive_dist_le_two_min ctx.minPair_spec (by rw [choice.site_weights.2]; omega))
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hd
  · exact Or.inr hfour

theorem reflectedSharedSix_right_no_diameter_neighbor_or_degree_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (w : Fin n) (choice : ReflectedSharedSixPacketChoice p w (v i) ctx.q) :
    (∀ a, (nearestGraph p).Adj choice.packet.right a → a ∉ diameterEndpoints p) ∨
      (nearestGraph p).degree choice.packet.right ≤ 4 := by
  have hG := nearestGraph_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hD := diameterEndpoints_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hbase : (nearestGraph p).Adj w (v i) := by simpa only [hG] using choice.reflected.base
  have hpartner : w ∈ diameterEndpoints p := by simpa only [hD] using choice.reflected.partner_diameter
  rcases choice.right_deep_or_degree_le_four with hd | hfour
  · left
    apply tight_flat_deep_base_receiver_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint
      w hpartner hbase.symm choice.packet.right
      (choice.packet.positive_dist_le_two_min ctx.minPair_spec (by rw [choice.site_weights.2]; omega))
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne hbase.ne)]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hd
  · exact Or.inr hfour

end Erdos957
