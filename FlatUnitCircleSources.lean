import TightFlatDiameterLocality
import DeepReceiverExclusion

/-! A thin strip around an actual flat hull chain contains at most two
separated points on a minimum-distance circle. -/

namespace Erdos957

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

private theorem circle_same_side_close_im_dist_lt (z w : ℂ) (r : ℝ)
    (hr : 0 < r) (hz : ‖z‖ = r) (hw : ‖w‖ = r)
    (hside : (0 ≤ z.re ∧ 0 ≤ w.re) ∨ (z.re ≤ 0 ∧ w.re ≤ 0))
    (him : |z.im - w.im| ≤ r / 15) : dist z w < r := by
  have hsq (a : ℂ) : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq a
  have hzs := hsq z
  have hws := hsq w
  rw [hz] at hzs
  rw [hw] at hws
  have hzabs : |z.im| ≤ r := by simpa only [hz] using Complex.abs_im_le_norm z
  have hwabs : |w.im| ≤ r := by simpa only [hw] using Complex.abs_im_le_norm w
  have hsum : |z.im + w.im| ≤ 2 * r :=
    (abs_add_le _ _).trans (by linarith)
  have hreal : (z.re - w.re) ^ 2 ≤ (2 / 15 : ℝ) * r ^ 2 := calc
    (z.re - w.re) ^ 2 ≤ |z.re ^ 2 - w.re ^ 2| :=
      same_side_sq_sub_le_abs_sq_sub _ _ hside
    _ = |(z.im - w.im) * (z.im + w.im)| := by
      have hid : z.re ^ 2 - w.re ^ 2 = -((z.im - w.im) * (z.im + w.im)) := by
        nlinarith only [hzs, hws]
      rw [hid, abs_neg]
    _ = |z.im - w.im| * |z.im + w.im| := abs_mul _ _
    _ ≤ (r / 15) * (2 * r) :=
      mul_le_mul him hsum (abs_nonneg _) (by positivity)
    _ = (2 / 15 : ℝ) * r ^ 2 := by ring
  have himsq : (z.im - w.im) ^ 2 ≤ (r / 15) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (z.im - w.im)) (by positivity)).mpr him
    simpa only [sq_abs] using h
  have hd := hsq (z - w)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hd
  nlinarith [dist_nonneg (x := z) (y := w), sq_pos_of_pos hr]

/-- Any radius-`r` circle has at most two points separated by at least `r`
inside a horizontal strip of height `r / 15`. -/
theorem separated_circle_card_le_two_in_thin_strip {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℂ) (q : ℂ) (r lo : ℝ) (hr : 0 < r)
    (hcircle : ∀ a ∈ S, dist (f a) q = r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist (f a) (f b))
    (hstrip : ∀ a ∈ S, lo ≤ (f a).im ∧ (f a).im ≤ lo + r / 15) :
    S.card ≤ 2 := by
  by_contra hnot
  have hbad (a : ι) (ha : a ∈ S) (b : ι) (hb : b ∈ S) (hab : a ≠ b)
      (hside : (0 ≤ (f a - q).re ∧ 0 ≤ (f b - q).re) ∨
        ((f a - q).re ≤ 0 ∧ (f b - q).re ≤ 0)) : False := by
    have hfa : ‖f a - q‖ = r := by simpa only [dist_eq_norm] using hcircle a ha
    have hfb : ‖f b - q‖ = r := by simpa only [dist_eq_norm] using hcircle b hb
    have hthin : |(f a - q).im - (f b - q).im| ≤ r / 15 := by
      obtain ⟨ha0, ha1⟩ := hstrip a ha
      obtain ⟨hb0, hb1⟩ := hstrip b hb
      simp only [Complex.sub_im]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hlt := circle_same_side_close_im_dist_lt (f a - q) (f b - q) r hr hfa hfb hside hthin
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

/-- If a receiver is adjacent to any actual tight-flat diameter endpoint,
at most two diameter endpoints are adjacent to it. The receiver need not be
the donor's central neighbor, and no degree condition is imposed on the donor. -/
theorem tight_flat_diameter_neighbors_card_le_two {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j) (i : Fin h)
    (hgood : v i ∉ tightHullBadVertices p v) (hu : v i ∈ diameterEndpoints p)
    (x : Fin n) (hux : (nearestGraph p).Adj (v i) x) :
    ((diameterEndpoints p).filter (fun w => (nearestGraph p).Adj x w)).card ≤ 2 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  let M := fun w => edgeCoordinate (p (v i)) (p (v (i + 1))) (p w)
  let r := pairDist p ij / dist (p (v i)) (p (v (i + 1)))
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL : 0 < dist (p (v i)) (p (v (i + 1))) := dist_pos.mpr hne
  have hr : 0 < r := div_pos (pairDist_pos p hp hmin.1) hL
  apply separated_circle_card_le_two_in_thin_strip _ M (M x) r 0 hr
  · intro w hw
    have hxw := (Finset.mem_filter.mp hw).2
    dsimp [M, r]
    rw [edgeCoordinate_dist _ _ _ _ hne, nearestGraph_adj_dist_eq p hmin hxw.symm]
  · intro w hw z hz hwz
    dsimp [M, r]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMinPair_le_dist p hmin hwz) hL.le
  · intro w hw
    obtain ⟨hwD, hxw⟩ := Finset.mem_filter.mp hw
    have hclose : dist (p (v i)) (p w) ≤ 2 * pairDist p ij := by
      calc
        dist (p (v i)) (p w) ≤ dist (p (v i)) (p x) + dist (p x) (p w) :=
          dist_triangle _ _ _
        _ = 2 * pairDist p ij := by
          rw [nearestGraph_adj_dist_eq p hmin hux, nearestGraph_adj_dist_eq p hmin hxw]
          ring
    have hwhere := tight_flat_nearby_diameter_endpoint_local p hp hn v hv hh hsupport hpos
      ij hmin i hgood hu w hwD hclose
    have hslope : |(M w).im| ≤ |(M w).re| / 30 :=
      tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood w (by tauto)
    have hnorm : ‖M w‖ ≤ 2 * r := by
      dsimp [M, r]
      rw [edgeCoordinate_norm _ _ _ hne]
      have hbound := div_le_div_of_nonneg_right hclose hL.le
      simpa only [mul_div_assoc] using hbound
    have hre := (Complex.abs_re_le_norm (M w)).trans hnorm
    have hprod := edgeCoordinate_im_mul_dist_sq (p (v i)) (p (v (i + 1))) (p w) hne
    have hside := hsupport i w
    change (M w).im * dist (p (v i)) (p (v (i + 1))) ^ 2 = _ at hprod
    constructor
    · nlinarith only [hprod, hside, sq_pos_of_pos hL]
    · have him := le_abs_self (M w).im
      linarith

end Erdos957
