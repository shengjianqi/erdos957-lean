import TwoSixBottomRigidity

/-! Uniform packing of all nearby diameter endpoints. -/

namespace Erdos957

theorem card_le_four_of_separated_in_Ico
    (s : Finset ℝ) (r : ℝ) (hr : 0 < r)
    (hinterval : ∀ t ∈ s, 0 ≤ t ∧ t < 4 * r)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → r ≤ |t - u|) :
    s.card ≤ 4 := by
  let bin : ℝ → ℕ := fun t => Nat.floor (t / r)
  have hbin_bounds (t : ℝ) (ht : 0 ≤ t) :
      (bin t : ℝ) * r ≤ t ∧ t < ((bin t : ℝ) + 1) * r := by
    have htdiv : 0 ≤ t / r := div_nonneg ht hr.le
    constructor
    · exact (le_div_iff₀ hr).mp (Nat.floor_le htdiv)
    · exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
  have hmaps : Set.MapsTo bin (s : Set ℝ) (Finset.range 4 : Set ℕ) := by
    intro t ht
    have htint := hinterval t ht
    have htdiv : 0 ≤ t / r := div_nonneg htint.1 hr.le
    have htdiv4 : t / r < 4 := (div_lt_iff₀ hr).mpr htint.2
    exact Finset.mem_range.mpr ((Nat.floor_lt htdiv).mpr htdiv4)
  have hinj : Set.InjOn bin (s : Set ℝ) := by
    intro t ht u hu htu
    by_contra hne
    have hgap := hsep t ht u hu hne
    obtain ⟨htlo, hthi⟩ := hbin_bounds t (hinterval t ht).1
    obtain ⟨hulo, huhi⟩ := hbin_bounds u (hinterval u hu).1
    have hbin_eq : (bin t : ℝ) = (bin u : ℝ) :=
      congrArg (fun k : ℕ => (k : ℝ)) htu
    rw [← hbin_eq] at hulo huhi
    rcases le_total t u with htuord | hutord
    · have habs : |t - u| = u - t := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htuord)]
      rw [habs] at hgap
      nlinarith
    · have habs : |t - u| = t - u := abs_of_nonneg (sub_nonneg.mpr hutord)
      rw [habs] at hgap
      nlinarith
  simpa using (Finset.card_le_card_of_injOn bin hmaps hinj)

theorem card_le_four_of_separated_in_short_interval
    (s : Finset ℝ) (lo hi r : ℝ) (hr : 0 < r)
    (hwidth : hi - lo < 4 * r)
    (hrange : ∀ θ ∈ s, lo ≤ θ ∧ θ ≤ hi)
    (hsep : ∀ θ ∈ s, ∀ φ ∈ s, θ ≠ φ → r ≤ |θ - φ|) :
    s.card ≤ 4 := by
  classical
  let shift : ℝ → ℝ := fun θ => θ - lo
  let t := s.image shift
  have ht_interval : ∀ u ∈ t, 0 ≤ u ∧ u < 4 * r := by
    intro u hu
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hlo, hhi⟩ := hrange θ hθ
    constructor <;> dsimp [shift] <;> linarith
  have ht_sep : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → r ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hv
    have hne : θ ≠ φ := by
      intro h
      exact huv (congrArg shift h)
    simpa only [shift, sub_sub_sub_cancel_right] using hsep θ hθ φ hφ hne
  have hcard : t.card = s.card := by
    dsimp [t]
    apply Finset.card_image_of_injective
    intro θ φ h
    dsimp [shift] at h
    linarith
  rw [← hcard]
  exact card_le_four_of_separated_in_Ico t r hr ht_interval ht_sep

private theorem complex_dist_sq_coordinates (z w : ℂ) :
    dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- A radius-two disk centered at depth at least seven tenths meets a thin
boundary strip in space for at most four minimum-separated points. -/
theorem medium_disk_strip_card_le_four {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℂ) (X : ℂ) (r : ℝ) (hr : 0 < r)
    (hdeep : (7 / 10 : ℝ) * r ≤ X.im)
    (hclose : ∀ a ∈ S, dist (f a) X ≤ 2 * r)
    (hstrip : ∀ a ∈ S, 0 ≤ (f a).im ∧ (f a).im ≤ r / 8)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist (f a) (f b)) :
    S.card ≤ 4 := by
  classical
  have hreal (a : ι) (ha : a ∈ S) :
      |(f a).re - X.re| ≤ (192 / 100 : ℝ) * r := by
    have hdistSq : dist (f a) X ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (by positivity)).mpr (hclose a ha)
    have hy : (23 / 40 : ℝ) * r ≤ X.im - (f a).im := by
      linarith [(hstrip a ha).2]
    have hySq : ((23 / 40 : ℝ) * r) ^ 2 ≤ (X.im - (f a).im) ^ 2 :=
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
  apply card_le_four_of_separated_in_short_interval R
    (X.re - (192 / 100 : ℝ) * r) (X.re + (192 / 100 : ℝ) * r)
    ((99 / 100 : ℝ) * r) (by positivity) (by linarith)
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have ht := abs_le.mp (hreal b hb)
    constructor <;> linarith
  · intro a ha b hb hab
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    exact hgap a₀ ha₀ b₀ hb₀ (fun heq => hab (by rw [heq]))

/-- Every diameter endpoint within two minimum lengths is included. -/
theorem tight_flat_medium_nearby_diameter_endpoints_card_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hMxre : |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re| ≤
      (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))))
    (hdeep : (7 / 10 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im) :
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij).card ≤ 4 := by
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
  change (7 / 10 : ℝ) * r ≤ (M x).im at hdeep
  change |(M x).re| ≤ (3 / 2 : ℝ) * r at hMxre
  let S := (diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij
  have hdist (a : Fin n) (ha : a ∈ S) : dist (M a) (M x) ≤ 2 * r := by
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    have ht := div_le_div_of_nonneg_right (Finset.mem_filter.mp ha).2 hL.le
    simpa only [r, L, mul_div_assoc] using ht
  apply medium_disk_strip_card_le_four S M (M x) r hr hdeep hdist
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

/-- A supported nearest pair with a deep bottom and a common secondary
receiver gives the four-endpoint bound in its forward hull orientation. -/
theorem sharedFive_forward_nearby_diameter_card_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q x : Fin n} (choice : SharedFiveCenterChoice p q)
    (hR : choice.right = v i) (hL : choice.left = v (i + 1))
    (hqx : (nearestGraph p).Adj q x)
    (hbx : (nearestGraph p).Adj choice.selection.bottom x)
    (hxlo : -(1 / 2 : ℝ) ≤ (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re)
    (hxhi : (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re ≤ 3 / 2) :
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij).card ≤ 4 := by
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  have hbase : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hR, hL] using choice.base.symm
  have hne := hp.ne hbase.ne
  have hδ := pairDist_pos p hp hmin.1
  have hscale : pairDist p ij / dist (p (v i)) (p (v (i + 1))) = 1 := by
    rw [nearestGraph_adj_dist_eq p hmin hbase, div_self hδ.ne']
  have hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij := by
    have ht := dist_triangle (p (v i)) (p q) (p x)
    have hadj : (nearestGraph p).Adj (v i) q := by
      simpa only [hR] using choice.center_right.symm
    rw [nearestGraph_adj_dist_eq p hmin hadj,
      nearestGraph_adj_dist_eq p hmin hqx] at ht
    linarith
  have hbdepth : Real.sqrt 3 ≤ (M (p choice.selection.bottom)).im := by
    have ht := choice.selection.bottom_depth
    simp only [hL, hR] at ht
    dsimp only [M]
    rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) _ hne.symm]
    simp only [Complex.sub_im, Complex.one_im]
    linarith
  have hdist : dist (M (p choice.selection.bottom)) (M (p x)) = 1 := by
    rw [edgeCoordinate_dist _ _ _ _ hne,
      nearestGraph_adj_dist_eq p hmin hbx,
      nearestGraph_adj_dist_eq p hmin hbase, div_self hδ.ne']
  have him := Complex.abs_im_le_norm (M (p choice.selection.bottom) - M (p x))
  simp only [Complex.sub_im, ← dist_eq_norm, hdist] at him
  have hroot : (17 / 10 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  apply tight_flat_medium_nearby_diameter_endpoints_card_le_four
    p hp hn v hv hh hsupport hpos ij hmin i hgood
    (by simpa only [hR] using choice.right_diameter) x hclose
  · rw [hscale]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hscale]
    change (7 / 10 : ℝ) * 1 ≤ (M (p x)).im
    linarith [(abs_le.mp him).2]

/-- Every actual six-bottom source bounds ALL nearby diameter endpoints,
in either orientation. The family and packet selections are unchanged. -/
theorem SixBottomIndirectSource.nearby_diameter_card_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    {x : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i)) :
    ((diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij).card ≤ 4 := by
  classical
  obtain ⟨hid, av, _hsix, horient⟩ :=
    hi.oriented_selected_pair p hp v hv hh hrange hsupport height assignments x i
  let first := selectedSharedFiveCenter p (assignments (v i) hid).context.q av
  obtain ⟨hid', av', hbx, hqx⟩ :=
    hi.receiver_adj_center_and_bottom p v height assignments
  have hhud : hid' = hid := Subsingleton.elim _ _
  subst hid'
  have hav : av' = av := Subsingleton.elim _ _
  subst av'
  change (nearestGraph p).Adj first.selection.bottom x at hbx
  have hgood := (Finset.mem_filter.mp hid).2.1
  rcases horient with ⟨hR, hL⟩ | ⟨hL, hR⟩
  · obtain ⟨hlo, hhi⟩ := hi.forward_receiving_strip p hp v height assignments hid av hR hL
    exact sharedFive_forward_nearby_diameter_card_le_four p hp hn v hv hh
      hsupport hpos ij hmin i hgood first hR hL hqx hbx hlo hhi
  · have hiCopy := hi
    obtain ⟨hid', hx, _hnot, _av, _hb⟩ := hiCopy
    have hhud : hid' = hid := Subsingleton.elim _ _
    subst hid'
    have hxrule : 0 < (assignments (v i) hid).rule.packet.weight x := by
      simpa only [localPacketCharge, dite_eq_left hid, certifiedFamilyPackets,
        CertifiedDonorAssignment.packet] using hx
    have hxcharge : 0 < first.charge (v i) x := by
      simpa only [(assignments (v i) hid).rule.weight_eq_selected_sharedFive av x]
        using hxrule
    change first.left = v i at hL
    change first.right = v (i - 1) at hR
    have hxfirst : 0 < first.selection.first.weight x := by
      simpa [SharedFiveCenterChoice.charge, ← hL, first.base.ne] using hxcharge
    obtain ⟨hlo, hhi, _⟩ := first.selection.receivers_in_rectangle x (Or.inl hxfirst)
    rw [hL, hR] at hlo hhi
    let pR : Fin n → Point := fun a => planeReflection (p a)
    let vR := reversedHullCycle v
    have hpR : Function.Injective pR := planeReflection.injective.comp hp
    have hvR : Function.Injective vR := reversedHullCycle_injective v hv
    have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
      planeReflection.dist_map _ _
    have hG := nearestGraph_eq_of_dist_eq p pR hdist
    have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
    have hminR := (isMinPair_iff_of_dist_eq p pR hdist ij).mpr hmin
    have hsupportR : ∀ a k, 0 ≤ turn (pR (vR a)) (pR (vR (a + 1))) (pR k) :=
      reflectedHull_support p v hsupport
    have hposR : ∀ a, 0 < hullExteriorAngle pR vR a := by
      intro a
      simpa only [pR, vR, hullExteriorAngle_planeReflection_reversed] using hpos (-a)
    have hgoodR : vR (-i) ∉ tightHullBadVertices pR vR :=
      tightHull_not_bad_planeReflection_reversed p v hv (-i) (by
        simpa only [neg_neg] using hgood)
    have hbound := sharedFive_forward_nearby_diameter_card_le_four
      pR hpR hn vR hvR hh hsupportR hposR ij hminR (-i) hgoodR
      (first.reflection_swap hp)
      (by simpa only [SharedFiveCenterChoice.reflection_swap_right_index,
        vR, reversedHullCycle_neg] using hL)
      (by simpa only [SharedFiveCenterChoice.reflection_swap_left_index,
        vR, reversedHullCycle_neg_successor] using hR)
      (by simpa only [hG] using hqx)
      (by simpa only [SharedFiveCenterChoice.reflection_swap_bottom, hG] using hbx)
      (by simpa only [pR, vR, reversedHullCycle_neg, reversedHullCycle_neg_successor,
        edgeCoordinate_planeReflection, Complex.conj_re] using hlo)
      (by simpa only [pR, vR, reversedHullCycle_neg, reversedHullCycle_neg_successor,
        edgeCoordinate_planeReflection, Complex.conj_re] using hhi)
    simpa only [hD, hdist, pairDist_eq_of_dist_eq p pR hdist ij] using hbound

end Erdos957


