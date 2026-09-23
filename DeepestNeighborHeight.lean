import SharedFiveReceiver

/-! A depth bound for a deepest neighbor in a supported shared-five triangle. -/

namespace Erdos957

private theorem lower_shoulder_inner_gt_half
    (x y u v : ℝ)
    (hz : x ^ 2 + y ^ 2 = 1) (hw : u ^ 2 + v ^ 2 = 1)
    (hx : 1 / 2 < x) (hu : 1 / 2 < u)
    (hy : y ≤ 0) (hv : v ≤ 0) :
    1 / 2 < x * u + y * v := by
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y]
  have hu1 : u ≤ 1 := by nlinarith [sq_nonneg v]
  have hgap : (x - u) ^ 2 < 1 / 4 := by
    have hpos := mul_pos (show 0 < 1 / 2 - (x - u) by linarith)
      (show 0 < 1 / 2 + (x - u) by linarith)
    nlinarith only [hpos]
  by_contra hnot
  have hdot : x * u + y * v ≤ 1 / 2 := le_of_not_gt hnot
  have hyv : 0 ≤ y * v := mul_nonneg_of_nonpos_of_nonpos hy hv
  have hxu : x * u ≤ 1 / 2 := by linarith
  have hsquare : (y * v) ^ 2 ≤ (1 / 2 - x * u) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - x * u - y * v by linarith)
      (show 0 ≤ 1 / 2 - x * u + y * v by linarith)]
  have hy2 : y ^ 2 = 1 - x ^ 2 := by linarith
  have hv2 : v ^ 2 = 1 - u ^ 2 := by linarith
  have hprod : (y * v) ^ 2 = (1 - x ^ 2) * (1 - u ^ 2) := by
    rw [mul_pow, hy2, hv2]
  nlinarith only [hprod, hsquare, hgap, hxu]

private theorem lower_unit_same_shoulder_dist_lt_one
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzlo : z.im ≤ 0) (hwlo : w.im ≤ 0)
    (hside : (1 / 2 < z.re ∧ 1 / 2 < w.re) ∨
      (z.re < -1 / 2 ∧ w.re < -1 / 2)) : dist z w < 1 := by
  have hnorm (t : ℂ) : t.re ^ 2 + t.im ^ 2 = ‖t‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq t
  have hzeq := hnorm z
  have hweq := hnorm w
  rw [hz] at hzeq
  rw [hw] at hweq
  have hinner : 1 / 2 < z.re * w.re + z.im * w.im := by
    rcases hside with ⟨hzre, hwre⟩ | ⟨hzre, hwre⟩
    · exact lower_shoulder_inner_gt_half z.re z.im w.re w.im
        (by simpa using hzeq) (by simpa using hweq) hzre hwre hzlo hwlo
    · have h := lower_shoulder_inner_gt_half (-z.re) z.im (-w.re) w.im
        (by simpa using hzeq) (by simpa using hweq)
        (by linarith) (by linarith) hzlo hwlo
      nlinarith only [h]
  have hdist := hnorm (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hdist
  rw [← dist_eq_norm] at hdist
  nlinarith [dist_nonneg (x := z) (y := w)]

/-- Three unit vectors on the lower semicircle separated by chords of at
least one include a vector at vertical depth at least `sqrt(3)/2`. -/
theorem three_lower_unit_neighbors_has_deep_point
    (S : Finset ℂ) (h : ℝ) (hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (hcard : 2 < S.card)
    (hunit : ∀ z ∈ S, ‖z‖ = 1)
    (hlower : ∀ z ∈ S, z.im ≤ 0)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → 1 ≤ dist z w) :
    ∃ z ∈ S, z.im ≤ -h := by
  classical
  by_contra hnone
  have hhigh (z : ℂ) (hz : z ∈ S) : -h < z.im := by
    by_contra hnot
    exact hnone ⟨z, hz, le_of_not_gt hnot⟩
  have hside (z : ℂ) (hz : z ∈ S) :
      1 / 2 < z.re ∨ z.re < -1 / 2 := by
    have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
      simpa only [Complex.normSq_apply, pow_two, hunit z hz, one_mul]
        using Complex.normSq_eq_norm_sq z
    have hy := hlower z hz
    have hdeep := hhigh z hz
    have hprod := mul_pos (show 0 < h + z.im by linarith)
      (show 0 < h - z.im by linarith)
    rcases le_or_gt 0 z.re with hx | hx
    · left
      nlinarith only [hnorm, hprod, hsq, hx]
    · right
      nlinarith only [hnorm, hprod, hsq, hx]
  have hbad (z : ℂ) (hz : z ∈ S) (w : ℂ) (hw : w ∈ S) (hne : z ≠ w)
      (hside : (1 / 2 < z.re ∧ 1 / 2 < w.re) ∨
        (z.re < -1 / 2 ∧ w.re < -1 / 2)) : False :=
    (not_lt_of_ge (hsep z hz w hw hne))
      (lower_unit_same_shoulder_dist_lt_one z w (hunit z hz) (hunit w hw)
        (hlower z hz) (hlower w hw) hside)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcard
  rcases hside a ha with haR | haL <;>
    rcases hside b hb with hbR | hbL <;>
    rcases hside c hc with hcR | hcL
  all_goals first
    | exact hbad a ha b hb hab (Or.inl ⟨haR, hbR⟩)
    | exact hbad a ha b hb hab (Or.inr ⟨haL, hbL⟩)
    | exact hbad a ha c hc hac (Or.inl ⟨haR, hcR⟩)
    | exact hbad a ha c hc hac (Or.inr ⟨haL, hcL⟩)
    | exact hbad b hb c hc hbc (Or.inl ⟨hbR, hcR⟩)
    | exact hbad b hb c hc hbc (Or.inr ⟨hbL, hcL⟩)

/-- An additional neighbor of a supported equilateral triangle's lower
vertex lies on or below that vertex's horizontal line. -/
theorem equilateral_other_neighbor_im_le_neg_height (z : ℂ) (h : ℝ)
    (_hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (hunit : ‖z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1)
    (hzero : 1 ≤ ‖z‖) (hone : 1 ≤ ‖z - 1‖) (hbelow : z.im ≤ 0) :
    z.im ≤ -h := by
  have hnorm (t : ℂ) : t.re ^ 2 + t.im ^ 2 = ‖t‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq t
  have hcircle := hnorm (z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I))
  rw [hunit] at hcircle
  norm_num at hcircle
  have hz := hnorm z
  have hz1 := hnorm (z - 1)
  norm_num at hz1
  have hzsq : 1 ≤ ‖z‖ ^ 2 := by nlinarith only [hzero]
  have hz1sq : 1 ≤ ‖z - 1‖ ^ 2 := by nlinarith only [hone]
  have hrelation : z.re ^ 2 + z.im ^ 2 - z.re + 2 * h * z.im = 0 := by
    nlinarith only [hcircle, hsq]
  have hlo : 0 ≤ z.re - 1 - 2 * h * z.im := by
    nlinarith only [hz, hzsq, hrelation]
  have hhi : 0 ≤ -2 * h * z.im - z.re := by
    nlinarith only [hz1, hz1sq, hrelation]
  have hyneg : z.im < 0 := by
    by_contra hn
    have hyzero : z.im = 0 := by linarith only [hbelow, hn]
    rw [hyzero] at hlo hhi
    nlinarith only [hlo, hhi]
  have hprod := mul_nonneg hlo hhi
  have hsqy : h ^ 2 * z.im ^ 2 = (3 / 4 : ℝ) * z.im ^ 2 := by rw [hsq]
  have hysq : 0 ≤ z.im * (z.im + h) := by
    nlinarith only [hprod, hrelation, hsqy]
  by_contra hn
  have hp := mul_neg_of_neg_of_pos hyneg (by linarith : 0 < z.im + h)
  linarith only [hysq, hp]

/-- A neighbor minimizing height among the three non-boundary neighbors of
a degree-five shared center has depth at least `sqrt(3)` in unit base coordinates.
No hull flatness, diameter or receiving capacity premise is needed. -/
theorem shared_five_deepest_neighbor_height {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q t : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hqdeg : (nearestGraph p).degree q = 5)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hminimal : ∀ a, (nearestGraph p).Adj q a → a ≠ u → a ≠ w →
      (edgeCoordinate (p u) (p w) (p t)).im ≤
        (edgeCoordinate (p u) (p w) (p a)).im) :
    (edgeCoordinate (p u) (p w) (p t)).im ≤ -Real.sqrt 3 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hne : p u ≠ p w := hp.ne huw.ne
  have huwdist : dist (p u) (p w) = r := nearestGraph_adj_dist_eq p hmin huw
  have huqdist := nearestGraph_adj_dist_eq p hmin hqu.symm
  have hwqdist := nearestGraph_adj_dist_eq p hmin hqw.symm
  let M := edgeCoordinate (p u) (p w)
  have hq0 : ‖M (p q)‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne, huqdist, huwdist, div_self hr.ne']
  have hq1 : ‖M (p q) - 1‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, hwqdist, huwdist, div_self hr.ne']
  have hbelow (a : Fin n) : (M (p a)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne (hsupport a)
  obtain ⟨h, hh, hhsq, hMq⟩ := unit_triangle_below_real_axis (M (p q)) hq0 hq1 (hbelow q)
  let N := (nearestGraph p).neighborFinset q \ {u, w}
  have hsubset : ({u, w} : Finset (Fin n)) ⊆ (nearestGraph p).neighborFinset q := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ((nearestGraph p).mem_neighborFinset q _).mpr hqu
    · exact ((nearestGraph p).mem_neighborFinset q _).mpr hqw
  have hNcard : N.card = 3 := by
    dsimp [N]
    rw [Finset.card_sdiff_of_subset hsubset,
      (nearestGraph p).card_neighborFinset_eq_degree, hqdeg]
    simp [huw.ne]
  have hNmem (a : Fin n) (ha : a ∈ N) :
      (nearestGraph p).Adj q a ∧ a ≠ u ∧ a ≠ w := by
    obtain ⟨hqa, hnot⟩ := Finset.mem_sdiff.mp ha
    exact ⟨((nearestGraph p).mem_neighborFinset q a).mp hqa,
      by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot⟩
  let f : Fin n → ℂ := fun a => M (p a) - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)
  have hfdist (a b : Fin n) : dist (f a) (f b) = dist (p a) (p b) / r := by
    dsimp [f, M]
    rw [dist_sub_right, edgeCoordinate_dist _ _ _ _ hne, huwdist]
  have hfinj : Function.Injective f := by
    intro a b hab
    have hzero : dist (p a) (p b) / r = 0 := by
      rw [← hfdist, hab, dist_self]
    have hdistzero : dist (p a) (p b) = 0 := by
      by_contra hnot
      exact div_ne_zero hnot hr.ne' hzero
    exact hp (dist_eq_zero.mp hdistzero)
  have hfunit (a : Fin n) (ha : a ∈ N) : ‖f a‖ = 1 := by
    have haqdist := nearestGraph_adj_dist_eq p hmin (hNmem a ha).1.symm
    dsimp [f]
    rw [← hMq, ← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, haqdist, huwdist, div_self hr.ne']
  have hflower (a : Fin n) (ha : a ∈ N) : (f a).im ≤ 0 := by
    obtain ⟨_, hau, haw⟩ := hNmem a ha
    have ha0 : 1 ≤ ‖M (p a)‖ := by
      dsimp [M]
      rw [edgeCoordinate_norm _ _ _ hne, huwdist]
      exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin hau.symm)
    have ha1 : 1 ≤ ‖M (p a) - 1‖ := by
      dsimp [M]
      rw [edgeCoordinate_sub_one_norm _ _ _ hne, huwdist]
      exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin haw.symm)
    have hlow := equilateral_other_neighbor_im_le_neg_height
      (M (p a)) h hh hhsq (hfunit a ha) ha0 ha1 (hbelow a)
    dsimp [f]
    simp only [Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    linarith
  let S := N.image f
  have hScard : 2 < S.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective N hfinj, hNcard]
    norm_num
  have hSunit : ∀ z ∈ S, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact hfunit a ha
  have hSlower : ∀ z ∈ S, z.im ≤ 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact hflower a ha
  have hSsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → 1 ≤ dist z z' := by
    intro z hz z' hz' hzz'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz'
    have hab : a ≠ b := fun hab => hzz' (congrArg f hab)
    rw [hfdist]
    exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin hab)
  obtain ⟨z, hz, hzdeep⟩ := three_lower_unit_neighbors_has_deep_point
    S h hh hhsq hScard hSunit hSlower hSsep
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hqa, hau, haw⟩ := hNmem a ha
  have htmin := hminimal a hqa hau haw
  have hsqrt : Real.sqrt 3 = 2 * h := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  dsimp [f] at hzdeep
  simp only [Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero] at hzdeep
  change (M (p t)).im ≤ -Real.sqrt 3
  change (M (p t)).im ≤ (M (p a)).im at htmin
  linarith

end Erdos957
