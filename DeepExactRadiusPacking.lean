import DeepReceiverCapacity

/-! Diameter endpoints at exactly two minimum distances from a deep receiver
occupy a thin circle strip, so there are at most two of them. -/

namespace Erdos957

private theorem complex_dist_sq_coordinates (z w : ℂ) :
    dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

private theorem same_side_sq_sub_le_abs_sq_sub (a b : ℝ)
    (hside : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  rcases hside with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases le_total a b with hab | hba
  · have hp := mul_nonneg ha (sub_nonneg.mpr hab)
    nlinarith [neg_le_abs (a ^ 2 - b ^ 2)]
  · have hp := mul_nonneg hb (sub_nonneg.mpr hba)
    nlinarith [le_abs_self (a ^ 2 - b ^ 2)]
  · have hp := mul_nonneg_of_nonpos_of_nonpos hb (sub_nonpos.mpr hab)
    nlinarith [le_abs_self (a ^ 2 - b ^ 2)]
  · have hp := mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.mpr hba)
    nlinarith [neg_le_abs (a ^ 2 - b ^ 2)]

private theorem twice_circle_same_side_close_im_dist_lt (z w : ℂ) (r : ℝ)
    (hr : 0 < r) (hz : ‖z‖ = 2 * r) (hw : ‖w‖ = 2 * r)
    (hside : (0 ≤ z.re ∧ 0 ≤ w.re) ∨ (z.re ≤ 0 ∧ w.re ≤ 0))
    (him : |z.im - w.im| ≤ r / 8) : dist z w < r := by
  have hsq (a : ℂ) : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq a
  have hzs := hsq z
  have hws := hsq w
  rw [hz] at hzs
  rw [hw] at hws
  have hzabs : |z.im| ≤ 2 * r := by simpa only [hz] using Complex.abs_im_le_norm z
  have hwabs : |w.im| ≤ 2 * r := by simpa only [hw] using Complex.abs_im_le_norm w
  have hsum : |z.im + w.im| ≤ 4 * r :=
    (abs_add_le _ _).trans (by linarith)
  have hreal : (z.re - w.re) ^ 2 ≤ (1 / 2 : ℝ) * r ^ 2 := calc
    (z.re - w.re) ^ 2 ≤ |z.re ^ 2 - w.re ^ 2| :=
      same_side_sq_sub_le_abs_sq_sub _ _ hside
    _ = |(z.im - w.im) * (z.im + w.im)| := by
      have hid : z.re ^ 2 - w.re ^ 2 = -((z.im - w.im) * (z.im + w.im)) := by
        nlinarith only [hzs, hws]
      rw [hid, abs_neg]
    _ = |z.im - w.im| * |z.im + w.im| := abs_mul _ _
    _ ≤ (r / 8) * (4 * r) :=
      mul_le_mul him hsum (abs_nonneg _) (by positivity)
    _ = (1 / 2 : ℝ) * r ^ 2 := by ring
  have himsq : (z.im - w.im) ^ 2 ≤ (r / 8) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (z.im - w.im)) (by positivity)).mpr him
    simpa only [sq_abs] using h
  have hd := hsq (z - w)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hd
  nlinarith [dist_nonneg (x := z) (y := w), sq_pos_of_pos hr]

/-- Any radius-`2 * r` circle has at most two points separated by at least `r`
inside a horizontal strip of height `r / 8`. -/
theorem separated_twice_radius_circle_card_le_two_in_thin_strip {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℂ) (q : ℂ) (r lo : ℝ) (hr : 0 < r)
    (hcircle : ∀ a ∈ S, dist (f a) q = 2 * r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist (f a) (f b))
    (hstrip : ∀ a ∈ S, lo ≤ (f a).im ∧ (f a).im ≤ lo + r / 8) :
    S.card ≤ 2 := by
  by_contra hnot
  have hbad (a : ι) (ha : a ∈ S) (b : ι) (hb : b ∈ S) (hab : a ≠ b)
      (hside : (0 ≤ (f a - q).re ∧ 0 ≤ (f b - q).re) ∨
        ((f a - q).re ≤ 0 ∧ (f b - q).re ≤ 0)) : False := by
    have hfa : ‖f a - q‖ = 2 * r := by simpa only [dist_eq_norm] using hcircle a ha
    have hfb : ‖f b - q‖ = 2 * r := by simpa only [dist_eq_norm] using hcircle b hb
    have hthin : |(f a - q).im - (f b - q).im| ≤ r / 8 := by
      obtain ⟨ha0, ha1⟩ := hstrip a ha
      obtain ⟨hb0, hb1⟩ := hstrip b hb
      simp only [Complex.sub_im]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hlt := twice_circle_same_side_close_im_dist_lt (f a - q) (f b - q) r hr hfa hfb hside hthin
    rw [dist_sub_right] at hlt
    exact (not_lt_of_ge (hsep a ha b hb hab)) hlt
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  rcases le_total 0 (f a - q).re with haR | haL <;>
    rcases le_total 0 (f b - q).re with hbR | hbL <;>
    rcases le_total 0 (f c - q).re with hcR | hcL
  all_goals first
    | exact hbad a ha b hb hab (Or.inl ⟨haR, hbR⟩)
    | exact hbad a ha b hb hab (Or.inr ⟨haL, hbL⟩)
    | exact hbad a ha c hc hac (Or.inl ⟨haR, hcR⟩)
    | exact hbad a ha c hc hac (Or.inr ⟨haL, hcL⟩)
    | exact hbad b hb c hc hbc (Or.inl ⟨hbR, hcR⟩)
    | exact hbad b hb c hc hbc (Or.inr ⟨hbL, hcL⟩)

/-- Actual flat hull locality and a depth margin bound the number of diameter
endpoints at exactly two minimum distances from the receiver by two. -/
theorem tight_flat_deep_exact_two_diameter_endpoints_card_le_two
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
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) = 2 * pairDist p ij).card ≤ 2 := by
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
  let S := (diameterEndpoints p).filter fun a => dist (p a) (p x) = 2 * pairDist p ij
  have hdist (a : Fin n) (ha : a ∈ S) : dist (M a) (M x) ≤ 2 * r := by
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    have ht := div_le_div_of_nonneg_right (le_of_eq (Finset.mem_filter.mp ha).2) hL.le
    simpa only [r, L, mul_div_assoc] using ht
  apply separated_twice_radius_circle_card_le_two_in_thin_strip S M (M x) r 0 hr
  · intro a ha
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, (Finset.mem_filter.mp ha).2]
    simp only [r, L, mul_div_assoc]
  · intro a _ha b _hb hab
    dsimp [M, r, L]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMinPair_le_dist p hmin hab) hL.le
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

/-- If every positive donor into a deep receiver is at exactly two minimum
distances, the complete certified sum is at most two doubled units. -/
theorem certified_family_deep_receiver_total_le_two_of_exact_distance
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
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hexact : ∀ u ∈ chargeDonors p bad,
      0 < localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x →
      dist (p u) (p x) = 2 * pairDist p ij) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤ 2 := by
  classical
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  have hunit := certified_family_total_le_positive_sources_card_of_no_diameter_neighbor
    p bad height assignments x hno
  have hsub : ((chargeDonors p bad).filter (fun u =>
      0 < localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x)) ⊆
      ((diameterEndpoints p).filter (fun u => dist (p u) (p x) = 2 * pairDist p ij)) := by
    intro u hu
    obtain ⟨hudonor, hpositive⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hudonor).1, hexact u hudonor hpositive⟩
  exact hunit.trans ((Finset.card_le_card hsub).trans
    (tight_flat_deep_exact_two_diameter_endpoints_card_le_two p hp hn v hv hh
      hsupport hpos ij hmin i hgood hu x hclose hdeep))

end Erdos957

