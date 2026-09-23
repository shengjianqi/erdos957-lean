import DeepSharedReceivers
import ShortArcPacking
import SharedCenterUniqueness

/-! A deep shared receiver has at most three nearby diameter endpoints.
Consequently two shared-five endpoint pairs with the same bottom must overlap,
and supporting-triangle uniqueness identifies their centers. A total charge
bound is proved separately in DeepReceiverCapacity. -/

namespace Erdos957

private theorem complex_dist_sq_coordinates (z w : ℂ) :
    dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- A radius-two disk centered at depth at least three halves meets a thin
boundary strip in space for at most three minimum-separated points. -/
theorem deep_disk_strip_card_le_three {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℂ) (X : ℂ) (r : ℝ) (hr : 0 < r)
    (hdeep : (3 / 2 : ℝ) * r ≤ X.im)
    (hclose : ∀ a ∈ S, dist (f a) X ≤ 2 * r)
    (hstrip : ∀ a ∈ S, 0 ≤ (f a).im ∧ (f a).im ≤ r / 8)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist (f a) (f b)) :
    S.card ≤ 3 := by
  classical
  have hreal (a : ι) (ha : a ∈ S) :
      |(f a).re - X.re| ≤ (147 / 100 : ℝ) * r := by
    have hdistSq : dist (f a) X ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (by positivity)).mpr (hclose a ha)
    have hy : (11 / 8 : ℝ) * r ≤ X.im - (f a).im := by
      linarith [(hstrip a ha).2]
    have hySq : ((11 / 8 : ℝ) * r) ^ 2 ≤ (X.im - (f a).im) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith)).mpr hy
    have hsq := complex_dist_sq_coordinates (f a) X
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [sq_pos_of_pos hr]
  have hgap (a : ι) (ha : a ∈ S) (b : ι) (hb : b ∈ S) (hab : a ≠ b) :
      (99 / 100 : ℝ) * r ≤ |(f a).re - (f b).re| := by
    have hdy : |(f a).im - (f b).im| ≤ r / 8 :=
      abs_le.mpr ⟨by linarith [(hstrip a ha).1, (hstrip b hb).2],
        by linarith [(hstrip a ha).2, (hstrip b hb).1]⟩
    have hdySq : ((f a).im - (f b).im) ^ 2 ≤ (r / 8) ^ 2 := by
      have ht := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdy
      simpa only [sq_abs] using ht
    have hdistSq : r ^ 2 ≤ dist (f a) (f b) ^ 2 :=
      (sq_le_sq₀ hr.le dist_nonneg).mpr (hsep a ha b hb hab)
    have hsq := complex_dist_sq_coordinates (f a) (f b)
    apply (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
    rw [sq_abs]
    nlinarith [sq_pos_of_pos hr]
  let R := S.image fun a => (f a).re
  have hcard : R.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb heq
    change (f a).re = (f b).re at heq
    by_contra hab
    have ht := hgap a ha b hb hab
    rw [heq, sub_self, abs_zero] at ht
    linarith
  rw [← hcard]
  apply card_le_three_of_separated_in_short_interval R
    (X.re - (147 / 100 : ℝ) * r) (X.re + (147 / 100 : ℝ) * r)
    ((99 / 100 : ℝ) * r) (by positivity) (by linarith)
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have ht := abs_le.mp (hreal b hb)
    constructor <;> linarith
  · intro a ha b hb hab
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    exact hgap a₀ ha₀ b₀ hb₀ (fun heq => hab (by rw [heq]))

/-- Actual flat hull locality and a depth margin bound all diameter
endpoints within two minimum distances of the receiver, including endpoints
that are not eligible donors. -/
theorem tight_flat_deep_nearby_diameter_endpoints_card_le_three
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im) :
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij).card ≤ 3 := by
  classical
  let M := fun a => edgeCoordinate (p (v i)) (p (v (i + 1))) (p a)
  let L := dist (p (v i)) (p (v (i + 1)))
  let r := pairDist p ij / L
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL : 0 < L := dist_pos.mpr hne
  have hr : 0 < r := div_pos (pairDist_pos p hp hmin.1) hL
  have hMx : ‖M x‖ ≤ 2 * r := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne]
    have ht := div_le_div_of_nonneg_right hclose hL.le
    simpa only [r, L, mul_div_assoc] using ht
  change (3 / 2 : ℝ) * r ≤ (M x).im at hdeep
  have hMxre : |(M x).re| ≤ (3 / 2 : ℝ) * r := by
    have hsq : (M x).re ^ 2 + (M x).im ^ 2 = ‖M x‖ ^ 2 := by
      simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq (M x)
    have hnSq : ‖M x‖ ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hMx
    have himSq : ((3 / 2 : ℝ) * r) ^ 2 ≤ (M x).im ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith)).mpr hdeep
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [sq_pos_of_pos hr]
  let S := (diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij
  have hdist (a : Fin n) (ha : a ∈ S) : dist (M a) (M x) ≤ 2 * r := by
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    have ht := div_le_div_of_nonneg_right (Finset.mem_filter.mp ha).2 hL.le
    simpa only [r, L, mul_div_assoc] using ht
  apply deep_disk_strip_card_le_three S M (M x) r hr hdeep hdist
  · intro a ha
    obtain ⟨haD, hax⟩ := Finset.mem_filter.mp ha
    have hdiff : |(M a).re - (M x).re| ≤ 2 * r := by
      have ht := (Complex.abs_re_le_norm (M a - M x)).trans (by
        simpa only [dist_eq_norm] using hdist a ha)
      simpa only [Complex.sub_re] using ht
    have hare : |(M a).re| ≤ (7 / 2 : ℝ) * r := by
      have ht : |(M a).re| ≤ |(M a).re - (M x).re| + |(M x).re| := by
        calc
          |(M a).re| = |((M a).re - (M x).re) + (M x).re| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      linarith
    have hnear : dist (p (v i)) (p a) ≤ 4 * pairDist p ij := by
      have ht := dist_triangle (p (v i)) (p x) (p a)
      rw [dist_comm (p x) (p a)] at ht
      linarith
    have hlocal := tight_flat_four_distance_diameter_endpoint_local p hp hn v hv hh
      hsupport hpos ij hmin i hgood hu a haD hnear (by
        change |(M a).re| ≤ (15 / 4 : ℝ) * r
        linarith)
    have hslope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood a hlocal
    change |(M a).im| ≤ |(M a).re| / 30 at hslope
    have him : 0 ≤ (M a).im := by
      have heq := edgeCoordinate_im_mul_dist_sq (p (v i)) (p (v (i + 1))) (p a) hne
      have hs := hsupport i a
      change (M a).im * L ^ 2 = _ at heq
      nlinarith [sq_pos_of_pos hL]
    exact ⟨him, by linarith [le_abs_self (M a).im]⟩
  · intro a _ha b _hb hab
    dsimp [M, r, L]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMinPair_le_dist p hmin hab) hL.le

/-- The existing deep base-frame condition also gives the three-endpoint
packing bound after transport to the actual outgoing support frame. -/
theorem tight_flat_deep_base_nearby_diameter_card_le_three
    {n h : ℕ} [NeZero h]
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
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij).card ≤ 3 := by
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
  have hslope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood w (by tauto)
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
  have hchange : M x = z * M w := edgeCoordinate_mul_base_change _ _ _ _ (hp.ne huw.ne)
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
  exact tight_flat_deep_nearby_diameter_endpoints_card_le_three p hp hn v hv hh
    hsupport hpos ij hmin i hgood hu x hclose hactual

/-- All endpoints reaching a shared-five bottom in two steps fit among at
most three nearby diameter endpoints. Either endpoint may be the good donor. -/
theorem sharedFive_bottom_nearby_diameter_card_le_three
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (q : Fin n) (choice : SharedFiveCenterChoice p q)
    (hsource : v i = choice.left ∨ v i = choice.right) :
    ((diameterEndpoints p).filter fun a =>
      dist (p a) (p choice.selection.bottom) ≤ 2 * pairDist p ij).card ≤ 3 := by
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
  · apply tight_flat_deep_base_nearby_diameter_card_le_three p hp hn v hv hh
      hsupport hpos ij hmin i hgood (by simpa only [hs] using choice.left_diameter)
      choice.right choice.right_diameter (by simpa only [hs] using choice.base)
      choice.selection.bottom (by simpa only [hs] using hpath choice.left choice.center_left)
    simpa only [hs] using hdepth
  · apply tight_flat_deep_base_nearby_diameter_card_le_three p hp hn v hv hh
      hsupport hpos ij hmin i hgood (by simpa only [hs] using choice.right_diameter)
      choice.left choice.left_diameter (by simpa only [hs] using choice.base.symm)
      choice.selection.bottom (by simpa only [hs] using hpath choice.right choice.center_right)
    rw [hs, edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hdepth

/-- Two shared-five centers with the same deepest neighbor have overlapping
diameter endpoint pairs. Only one pair needs an actual good endpoint. -/
theorem sharedFive_same_bottom_endpoint_pairs_overlap
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n} (choice : SharedFiveCenterChoice p q)
    (other : SharedFiveCenterChoice p q')
    (hsource : v i = choice.left ∨ v i = choice.right)
    (hbottom : choice.selection.bottom = other.selection.bottom) :
    choice.left = other.left ∨ choice.left = other.right ∨
      choice.right = other.left ∨ choice.right = other.right := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  let S := (diameterEndpoints p).filter fun a =>
    dist (p a) (p choice.selection.bottom) ≤ 2 * pairDist p ij
  have hcard : S.card ≤ 3 := sharedFive_bottom_nearby_diameter_card_le_three
    p hp hn v hv hh hsupport hpos ij hmin i hgood q choice hsource
  have hmem (q₀ : Fin n) (ch : SharedFiveCenterChoice p q₀)
      (hb : ch.selection.bottom = choice.selection.bottom)
      (a : Fin n) (haD : a ∈ diameterEndpoints p) (hqa : (nearestGraph p).Adj q₀ a) :
      a ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨haD, ?_⟩
    rw [← hb]
    have ht := dist_triangle (p a) (p q₀) (p ch.selection.bottom)
    rw [nearestGraph_adj_dist_eq p hmin hqa.symm,
      nearestGraph_adj_dist_eq p hmin ch.selection.bottom_adj] at ht
    linarith
  have hal := hmem q choice rfl choice.left choice.left_diameter choice.center_left
  have har := hmem q choice rfl choice.right choice.right_diameter choice.center_right
  have hbl := hmem q' other hbottom.symm other.left other.left_diameter other.center_left
  have hbr := hmem q' other hbottom.symm other.right other.right_diameter other.center_right
  by_contra hnone
  simp only [not_or] at hnone
  obtain ⟨hll, hlr, hrl, hrr⟩ := hnone
  have hsub : ({choice.left, choice.right, other.left, other.right} : Finset (Fin n)) ⊆ S := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hfour : ({choice.left, choice.right, other.left, other.right} : Finset (Fin n)).card = 4 := by
    simp [choice.base.ne, other.base.ne, hll, hlr, hrl, hrr]
  have ht := Finset.card_le_card hsub
  omega

/-- Combining endpoint overlap with supported-triangle uniqueness identifies
the centers. The shared endpoint itself need not be good or an eligible donor. -/
theorem sharedFive_same_bottom_centers_eq
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n} (choice : SharedFiveCenterChoice p q)
    (other : SharedFiveCenterChoice p q')
    (hsource : v i = choice.left ∨ v i = choice.right)
    (hbottom : choice.selection.bottom = other.selection.bottom) : q = q' := by
  have htriangle (q₀ : Fin n) (ch : SharedFiveCenterChoice p q₀)
      (u : Fin n) (hu : u = ch.left ∨ u = ch.right) :
      ∃ w, u ∈ diameterEndpoints p ∧ w ∈ diameterEndpoints p ∧
        (nearestGraph p).Adj u w ∧ (nearestGraph p).Adj u q₀ ∧
        (nearestGraph p).Adj w q₀ ∧
        ((∀ k, 0 ≤ turn (p u) (p w) (p k)) ∨
          (∀ k, 0 ≤ turn (p w) (p u) (p k))) := by
    rcases hu with rfl | rfl
    · exact ⟨ch.right, ch.left_diameter, ch.right_diameter, ch.base,
        ch.center_left.symm, ch.center_right.symm, Or.inr ch.support⟩
    · exact ⟨ch.left, ch.right_diameter, ch.left_diameter, ch.base.symm,
        ch.center_right.symm, ch.center_left.symm, Or.inl ch.support⟩
  have hoverlap := sharedFive_same_bottom_endpoint_pairs_overlap p hp hn v hv hh
    hsupport hpos i hgood choice other hsource hbottom
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u, (u = choice.left ∨ u = choice.right) ∧
      (u = other.left ∨ u = other.right) := by
    rcases hoverlap with hll | hlr | hrl | hrr
    · exact ⟨choice.left, Or.inl rfl, Or.inl hll⟩
    · exact ⟨choice.left, Or.inl rfl, Or.inr hlr⟩
    · exact ⟨choice.right, Or.inr rfl, Or.inl hrl⟩
    · exact ⟨choice.right, Or.inr rfl, Or.inr hrr⟩
  obtain ⟨w₁, hu, hw₁, huw₁, huq₁, hwq₁, hs₁⟩ := htriangle q choice u hu₁
  obtain ⟨w₂, _hu, hw₂, huw₂, huq₂, hwq₂, hs₂⟩ := htriangle q' other u hu₂
  have hdeg₁ : 4 ≤ (nearestGraph p).degree q := by rw [choice.center_degree]; omega
  have hdeg₂ : 4 ≤ (nearestGraph p).degree q' := by rw [other.center_degree]; omega
  exact high_degree_supported_triangle_centers_eq_of_diameterEndpoint p hp hn
    hu hw₁ hw₂ huw₁ huw₂ huq₁ huq₂ hwq₁ hwq₂ hdeg₁ hdeg₂ hs₁ hs₂

end Erdos957
