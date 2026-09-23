import NormalizedEdgeGeometry
import DiameterGraph
import Mathlib.Tactic.Linarith

/-! A farthest partner seen between nearly horizontal left and right witnesses
lies in a narrow inward cone. -/

namespace Erdos957

/-- A point at least as far from the origin as from `Q` has nonnegative
Euclidean scalar product with `Q`. -/
private theorem complex_dot_nonneg_of_dist_le_norm (J Q : ℂ)
    (hJQ : dist J Q ≤ ‖J‖) :
    0 ≤ J.re * Q.re + J.im * Q.im := by
  have hnorm : ‖J - Q‖ ≤ ‖J‖ := by simpa only [dist_eq_norm] using hJQ
  have hsq : ‖J - Q‖ ^ 2 ≤ ‖J‖ ^ 2 := by
    nlinarith [norm_nonneg (J - Q), norm_nonneg J]
  have hJ : J.re ^ 2 + J.im ^ 2 = ‖J‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq J
  have hJQsq : (J.re - Q.re) ^ 2 + (J.im - Q.im) ^ 2 = ‖J - Q‖ ^ 2 := by
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
      using Complex.normSq_eq_norm_sq (J - Q)
  nlinarith [sq_nonneg Q.re, sq_nonneg Q.im]

/-- The farthest partner lies within one tenth of its inward depth in the
horizontal direction. The actual dot inequalities give a stronger cone; this
simple bound is suited to subsequent finite-hull estimates. -/
theorem diameter_partner_re_bound (L R J : ℂ)
    (hLre : L.re ≤ -1) (hRre : 3 ≤ R.re)
    (hLim : -(1 / 10 : ℝ) ≤ L.im ∧ L.im ≤ 0)
    (hRim : -(1 / 10 : ℝ) ≤ R.im ∧ R.im ≤ 0)
    (hJim : J.im ≤ 0)
    (hJL : dist J L ≤ ‖J‖) (hJR : dist J R ≤ ‖J‖) :
    let D : ℝ := -J.im;
    -D / 10 ≤ J.re ∧ J.re ≤ D / 10 := by
  dsimp
  have hdotL := complex_dot_nonneg_of_dist_le_norm J L hJL
  have hdotR := complex_dot_nonneg_of_dist_le_norm J R hJR
  have hD : 0 ≤ -J.im := by linarith
  constructor
  · by_contra hnot
    have hx : J.re < J.im / 10 := by linarith
    have hxneg : J.re < 0 := by linarith
    have hxr : J.re * R.re ≤ J.re * 3 := by
      have hm := mul_le_mul_of_nonpos_left hRre (le_of_lt hxneg)
      nlinarith only [hm]
    have hyr : J.im * R.im ≤ J.im * (-(1 / 10 : ℝ)) := by
      have hm := mul_le_mul_of_nonpos_left hRim.1 hJim
      nlinarith only [hm]
    nlinarith only [hdotR, hxr, hyr, hx, hJim]
  · by_contra hnot
    have hx : -J.im / 10 < J.re := by linarith
    have hxpos : 0 < J.re := by linarith
    have hxl : J.re * L.re ≤ J.re * (-1) := by
      have hm := mul_le_mul_of_nonneg_left hLre (le_of_lt hxpos)
      nlinarith only [hm]
    have hyl : J.im * L.im ≤ J.im * (-(1 / 10 : ℝ)) := by
      have hm := mul_le_mul_of_nonpos_left hLim.1 hJim
      nlinarith only [hm]
    nlinarith only [hdotL, hxl, hyl, hx, hJim]

/-- If the farthest partner is more than ten units away, its inward
vertical depth exceeds nine units. -/
theorem diameter_partner_depth_gt_nine (L R J : ℂ)
    (hLre : L.re ≤ -1) (hRre : 3 ≤ R.re)
    (hLim : -(1 / 10 : ℝ) ≤ L.im ∧ L.im ≤ 0)
    (hRim : -(1 / 10 : ℝ) ≤ R.im ∧ R.im ≤ 0)
    (hJim : J.im ≤ 0)
    (hJL : dist J L ≤ ‖J‖) (hJR : dist J R ≤ ‖J‖)
    (hJnorm : 10 < ‖J‖) :
    9 < -J.im := by
  obtain ⟨hxlo, hxhi⟩ :=
    diameter_partner_re_bound L R J hLre hRre hLim hRim hJim hJL hJR
  have hsq : 0 ≤ ((-J.im) / 10 - J.re) * ((-J.im) / 10 + J.re) :=
    mul_nonneg (by linarith) (by linarith)
  have hnormsq : J.re ^ 2 + J.im ^ 2 = ‖J‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq J
  by_contra hnot
  have hDle : -J.im ≤ 9 := le_of_not_gt hnot
  have hDnonneg : 0 ≤ -J.im := by linarith
  have hDsq : (-J.im) ^ 2 ≤ 81 := by
    nlinarith [mul_nonneg hDnonneg (by linarith : 0 ≤ 9 + J.im)]
  nlinarith only [hsq, hnormsq, hDsq, hJnorm, norm_nonneg J]

set_option maxHeartbeats 1000000

/-- Every point of the actual convex hull is no farther from a diameter
partner than the diameter endpoint is. The normalized edge similarity
preserves that inequality after dividing both distances by the same scale. -/
theorem normalized_diameter_dist_le_norm {n : ℕ}
    (p : Fin n → Point) {u w j : Fin n}
    (hdiam : (diameterGraph p).Adj u j)
    (hne : p u ≠ p w)
    (x : Point) (hx : x ∈ convexHull ℝ (Set.range p)) :
    dist (edgeCoordinate (p u) (p w) (p j))
      (edgeCoordinate (p u) (p w) x) ≤
      ‖edgeCoordinate (p u) (p w) (p j)‖ := by
  have hbound (k : Fin n) :
      dist (p j) (p k) ≤ dist (p u) (p j) := by
    rcases (diameterGraph_adj_iff p u j).mp hdiam with hmax | hmax
    · simpa only [pairDist] using isMaxPair_dist_le p hmax j k
    · simpa only [pairDist, dist_comm] using isMaxPair_dist_le p hmax j k
  have hsubset : Set.range p ⊆
      Metric.closedBall (p j) (dist (p u) (p j)) := by
    rintro y ⟨k, rfl⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_comm (p k) (p j)] using hbound k)
  have hHull : convexHull ℝ (Set.range p) ⊆
      Metric.closedBall (p j) (dist (p u) (p j)) :=
    convexHull_min hsubset (convex_closedBall (p j) (dist (p u) (p j)))
  have hmetric : dist (p j) x ≤ dist (p u) (p j) := by
    have h := Metric.mem_closedBall.mp (hHull hx)
    simpa only [dist_comm (p j) x] using h
  calc
    dist (edgeCoordinate (p u) (p w) (p j))
        (edgeCoordinate (p u) (p w) x) =
        dist (p j) x / dist (p u) (p w) :=
      edgeCoordinate_dist (p u) (p w) (p j) x hne
    _ ≤ dist (p u) (p j) / dist (p u) (p w) :=
      div_le_div_of_nonneg_right hmetric dist_nonneg
    _ = ‖edgeCoordinate (p u) (p w) (p j)‖ :=
      (edgeCoordinate_norm (p u) (p w) (p j) hne).symm

/-- A diameter more than ten times the normalization edge gives a normalized
diameter partner of norm greater than ten. -/
theorem normalized_diameter_norm_gt_ten {n : ℕ}
    (p : Fin n → Point) {u w j : Fin n}
    (hne : p u ≠ p w)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j)) :
    10 < ‖edgeCoordinate (p u) (p w) (p j)‖ := by
  rw [edgeCoordinate_norm (p u) (p w) (p j) hne]
  exact (lt_div_iff₀ (dist_pos.mpr hne)).2 (by simpa only [mul_comm] using hscale)

end Erdos957
