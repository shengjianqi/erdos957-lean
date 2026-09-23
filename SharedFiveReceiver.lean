import SharedFiveGeometry
import NormalizedReceiverInterior
import InteriorExclusion

/-! All non-boundary nearest neighbors of a supported equilateral triangle's
interior vertex lie inside one bounded receiving region. -/

namespace Erdos957

set_option maxHeartbeats 1000000

/-- Avoiding both endpoint unit disks forces another unit neighbor of the
lower equilateral vertex onto its lower semicircle. -/
theorem equilateral_other_neighbor_rectangle (z : ℂ) (h : ℝ)
    (hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (hunit : ‖z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1)
    (hzero : 1 ≤ ‖z‖) (hone : 1 ≤ ‖z - 1‖) (hbelow : z.im ≤ 0) :
    -(1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 3 / 2 ∧
      -2 ≤ z.im ∧ z.im ≤ -1 / 2 := by
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
  have hydeep : z.im ≤ -h := by
    by_contra hn
    have hp := mul_neg_of_neg_of_pos hyneg (by linarith : 0 < z.im + h)
    linarith only [hysq, hp]
  have hhrange : 1 / 2 < h ∧ h < 1 := by constructor <;> nlinarith only [hh, hsq]
  have hx : |z.re - 1 / 2| ≤ 1 := by
    have ht := Complex.abs_re_le_norm (z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I))
    rw [hunit] at ht
    norm_num at ht
    exact ht
  have hy : |z.im + h| ≤ 1 := by
    have ht := Complex.abs_im_le_norm (z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I))
    rw [hunit] at ht
    norm_num at ht
    exact ht
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hylo, _⟩ := abs_le.mp hy
  exact ⟨by linarith, by linarith, by linarith [hhrange.2], by linarith [hhrange.1]⟩

/-- The same shallow-span triangle contains the full rectangle
`[-1/2,3/2] × [-2,-1/2]`, including the leftmost shared-five candidates. -/
theorem long_triangle_shared_five_rectangle_strict_turns
    (L J R q : ℂ) (D : ℝ)
    (hD : 9 < D)
    (hLre : L.re ≤ -1) (hRre : 3 ≤ R.re)
    (hLimlo : -1 / 10 ≤ L.im) (hLimhi : L.im ≤ 0)
    (hRimlo : -1 / 10 ≤ R.im) (hRimhi : R.im ≤ 0)
    (hJrelo : -D / 10 ≤ J.re) (hJrehi : J.re ≤ D / 10)
    (hJim : J.im = -D)
    (hqrelo : -(1 / 2 : ℝ) ≤ q.re) (hqrehi : q.re ≤ 3 / 2)
    (hqimlo : -2 ≤ q.im) (hqimhi : q.im ≤ -1 / 2)
    :
    0 < complexTurn L J R ∧
      0 < complexTurn L J q ∧
      0 < complexTurn J R q ∧
      0 < complexTurn R L q := by
  have hLJ_formula : complexTurn L J q =
      (J.re - L.re) * (q.im - L.im) + (D + L.im) * (q.re - L.re) := by
    simp [complexTurn, Complex.mul_im, hJim]
  have hJR_formula : complexTurn J R q =
      (R.re - J.re) * (q.im + D) -
        (D + R.im) * (q.re - J.re) := by
    simp [complexTurn, Complex.mul_im, hJim]
    ring
  have hRL_formula : complexTurn R L q =
      (R.re - L.re) * (-q.im) +
        (q.re - L.re) * R.im + (R.re - q.re) * L.im := by
    simp [complexTurn, Complex.mul_im]
    ring
  have hDq : 0 ≤ D + q.im := by linarith
  have haY : 0 ≤ L.im - q.im := by linarith
  have hbY : 0 ≤ R.im - q.im := by linarith
  have hLgap : 0 ≤ -1 - L.re := by linarith
  have hRgap : 0 ≤ R.re - 3 := by linarith
  have hJupper : 0 ≤ D / 10 - J.re := by linarith
  have hJlower : 0 ≤ J.re + D / 10 := by linarith
  have hX : 0 ≤ q.re + 1 / 2 := by linarith
  have hDX : 0 ≤ D / 10 := by linarith
  have hXDX : 0 ≤ q.re + D / 10 := by linarith
  have hLX : 0 ≤ q.re - L.re := by linarith
  have hRX : 0 ≤ R.re - q.re := by linarith
  have hRLim : 0 ≤ L.im + 1 / 10 := by linarith
  have hRRim : 0 ≤ R.im + 1 / 10 := by linarith
  have hRL : 0 ≤ R.re - L.re := by linarith
  have hLbound₁ : 0 ≤ (-1 - L.re) * (D + q.im) :=
    mul_nonneg hLgap hDq
  have hLbound₂ : 0 ≤ (D / 10 - J.re) * (L.im - q.im) :=
    mul_nonneg hJupper haY
  have hLbound₃ : 0 ≤ (-L.im) * (D / 10) :=
    mul_nonneg (by linarith) hDX
  have hLbound₄ : 0 ≤ (L.im + 1 / 10) * (q.re + 1 / 2) :=
    mul_nonneg hRLim hX
  have hLcoef : 0 ≤ q.re + 1 + q.im / 10 := by linarith
  have hLbound₅ : 0 ≤ (D - 9) * (q.re + 1 + q.im / 10) :=
    mul_nonneg (by linarith) hLcoef
  have hLbound₆ : 0 ≤ -L.im / 2 := by linarith
  have hLlower :
      9 * (q.re + 1 + q.im / 10) + q.im - q.re / 10 - 1 / 20 ≤
        complexTurn L J q := by
    rw [hLJ_formula]
    nlinarith only [hLbound₁, hLbound₂, hLbound₃, hLbound₄, hLbound₅, hLbound₆]
  have hLturn : 0 < complexTurn L J q := by
    have hbase : 0 <
        9 * (q.re + 1 + q.im / 10) + q.im - q.re / 10 - 1 / 20 := by
      linarith
    exact lt_of_lt_of_le hbase hLlower
  have hRbound₁ : 0 ≤ (R.re - 3) * (D + q.im) :=
    mul_nonneg hRgap hDq
  have hRbound₂ : 0 ≤ (J.re + D / 10) * (R.im - q.im) :=
    mul_nonneg hJlower hbY
  have hRbound₃ : 0 ≤ (-R.im) * (q.re + D / 10) :=
    mul_nonneg (by linarith) hXDX
  have hRlower :
      D * (3 - q.re + q.im / 10) + 3 * q.im ≤ complexTurn J R q := by
    rw [hJR_formula]
    nlinarith only [hRbound₁, hRbound₂, hRbound₃]
  have hRturn : 0 < complexTurn J R q := by
    have hshape : q.re ≤ 2 ∨ -1 ≤ q.im := Or.inl (by linarith)
    rcases hshape with hleft | hright
    · have hcoef : 0 ≤ 3 - q.re + q.im / 10 := by linarith
      have hbound : 0 ≤ (D - 9) * (3 - q.re + q.im / 10) :=
        mul_nonneg (by linarith) hcoef
      have hbase : 0 < D * (3 - q.re + q.im / 10) + 3 * q.im := by
        nlinarith only [hbound, hleft, hqimlo]
      exact lt_of_lt_of_le hbase hRlower
    · have hcoef : 0 ≤ 3 - q.re + q.im / 10 := by linarith
      have hbound : 0 ≤ (D - 9) * (3 - q.re + q.im / 10) :=
        mul_nonneg (by linarith) hcoef
      have hbase : 0 < D * (3 - q.re + q.im / 10) + 3 * q.im := by
        nlinarith only [hbound, hqrehi, hright]
      exact lt_of_lt_of_le hbase hRlower
  have hRLbound₁ : 0 ≤ (R.re - L.re) * (-q.im - 1 / 2) :=
    mul_nonneg hRL (by linarith)
  have hRLbound₂ : 0 ≤ (q.re - L.re) * (R.im + 1 / 10) :=
    mul_nonneg hLX hRRim
  have hRLbound₃ : 0 ≤ (R.re - q.re) * (L.im + 1 / 10) :=
    mul_nonneg hRX hRLim
  have hRLlower : (2 / 5 : ℝ) * (R.re - L.re) ≤ complexTurn R L q := by
    rw [hRL_formula]
    nlinarith only [hRLbound₁, hRLbound₂, hRLbound₃]
  have hRLturn : 0 < complexTurn R L q := by
    have hbase : 0 < (2 / 5 : ℝ) * (R.re - L.re) := by linarith
    exact lt_of_lt_of_le hbase hRLlower
  have hsum : complexTurn L J q + complexTurn J R q +
      complexTurn R L q = complexTurn L J R := by
    simp [complexTurn, Complex.mul_im]
    ring
  constructor
  · rw [← hsum]
    positivity
  exact ⟨hLturn, hRturn, hRLturn⟩

/-- The actual shallow hull span also contains the slightly left-extended
rectangle needed for all other neighbors of a shared equilateral vertex. -/
theorem NormalizedHullSpan.shared_five_receiver_mem_interior {n : ℕ}
    (p : Fin n → Point) {u w j : Fin n}
    (span : NormalizedHullSpan p u w) (hne : p u ≠ p w)
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (hsupport : 0 ≤ turn (p w) (p u) (p j))
    (x : Point)
    (hx : -(1 / 2 : ℝ) ≤ (edgeCoordinate (p u) (p w) x).re ∧
      (edgeCoordinate (p u) (p w) x).re ≤ 3 / 2 ∧
      -2 ≤ (edgeCoordinate (p u) (p w) x).im ∧
      (edgeCoordinate (p u) (p w) x).im ≤ -1 / 2) :
    x ∈ interior (convexHull ℝ (Set.range p)) := by
  let M := edgeCoordinate (p u) (p w)
  have hJim : (M (p j)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne hsupport
  have hJL := normalized_diameter_dist_le_norm p hdiam hne span.left span.left_mem
  have hJR := normalized_diameter_dist_le_norm p hdiam hne span.right span.right_mem
  have hnorm := normalized_diameter_norm_gt_ten p hne hscale
  have hD := diameter_partner_depth_gt_nine (M span.left) (M span.right) (M (p j))
    span.left_re span.right_re span.left_im span.right_im hJim hJL hJR hnorm
  obtain ⟨hJlo, hJhi⟩ := diameter_partner_re_bound
    (M span.left) (M span.right) (M (p j)) span.left_re span.right_re
    span.left_im span.right_im hJim hJL hJR
  obtain ⟨hqlo, hqhi, hylo, hyhi⟩ := hx
  obtain ⟨_, hLJ, hJRq, hRL⟩ := long_triangle_shared_five_rectangle_strict_turns
    (M span.left) (M (p j)) (M span.right) (M x) (-(M (p j)).im)
    hD span.left_re span.right_re (by simpa only [neg_div] using span.left_im.1)
    span.left_im.2 (by simpa only [neg_div] using span.right_im.1)
    span.right_im.2 hJlo hJhi (by ring) hqlo hqhi hylo hyhi
  exact normalized_triangle_mem_interior_convexHull (Set.range p)
    (p u) (p w) span.left (p j) span.right x hne
    span.left_mem (subset_convexHull ℝ _ (Set.mem_range_self j))
    span.right_mem hLJ hJRq hRL

/-- Every nearest neighbor of the shared equilateral vertex, other than
the two supporting endpoints, is interior when the true hull has the
verified shallow span. No choice of a deepest neighbor is required. -/
theorem shared_triangle_other_neighbor_mem_interior {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q a j : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w) (hqa : (nearestGraph p).Adj q a)
    (hau : a ≠ u) (haw : a ≠ w)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) :
    p a ∈ interior (convexHull ℝ (Set.range p)) := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have hne : p u ≠ p w := hp.ne huw.ne
  have huwdist := nearestGraph_adj_dist_eq p hmin huw
  have huqdist := nearestGraph_adj_dist_eq p hmin hqu.symm
  have hwqdist := nearestGraph_adj_dist_eq p hmin hqw.symm
  have haqdist := nearestGraph_adj_dist_eq p hmin hqa.symm
  let M := edgeCoordinate (p u) (p w)
  have hq0 : ‖M (p q)‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne, huqdist, huwdist, div_self hr.ne']
  have hq1 : ‖M (p q) - 1‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, hwqdist, huwdist, div_self hr.ne']
  have hbelow (k : Fin n) : (M (p k)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne (hsupport k)
  obtain ⟨h, hh, hhsq, hMq⟩ := unit_triangle_below_real_axis (M (p q)) hq0 hq1 (hbelow q)
  have haunit : ‖M (p a) - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1 := by
    rw [← hMq, ← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, haqdist, huwdist, div_self hr.ne']
  have ha0 : 1 ≤ ‖M (p a)‖ := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne, huwdist]
    exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin hau.symm)
  have ha1 : 1 ≤ ‖M (p a) - 1‖ := by
    dsimp [M]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, huwdist]
    exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin haw.symm)
  have hrect := equilateral_other_neighbor_rectangle (M (p a)) h hh hhsq haunit ha0 ha1 (hbelow a)
  exact span.shared_five_receiver_mem_interior p hne hdiam hscale (hsupport j) (p a) hrect

/-- The other nearest neighbors are therefore genuine non-diameter
receivers; the exclusion follows from proved interior membership. -/
theorem shared_triangle_other_neighbor_not_diameter {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q a j : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w) (hqa : (nearestGraph p).Adj q a)
    (hau : a ≠ u) (haw : a ≠ w)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) : a ∉ diameterEndpoints p :=
  interior_not_diameterEndpoints p hp a
    (shared_triangle_other_neighbor_mem_interior p hn hp hqu hqw huw hqa
      hau haw hsupport hdiam hscale span)

end Erdos957

