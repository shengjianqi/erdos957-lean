import NormalizedTriangle
import NormalizedDiameterCone
import RectangleInterior

/-! A shallow span in the actual hull forces the local receiving region inside it. -/

namespace Erdos957

/-- Two hull points spanning the receiving region just below the support line.
They may be interpolated points on long hull edges. Existence is separate. -/
structure NormalizedHullSpan {n : ℕ} (p : Fin n → Point) (u w : Fin n) where
  left : Point
  right : Point
  left_mem : left ∈ convexHull ℝ (Set.range p)
  right_mem : right ∈ convexHull ℝ (Set.range p)
  left_re : (edgeCoordinate (p u) (p w) left).re ≤ -1
  right_re : 3 ≤ (edgeCoordinate (p u) (p w) right).re
  left_im : -(1 / 10 : ℝ) ≤ (edgeCoordinate (p u) (p w) left).im ∧
    (edgeCoordinate (p u) (p w) left).im ≤ 0
  right_im : -(1 / 10 : ℝ) ≤ (edgeCoordinate (p u) (p w) right).im ∧
    (edgeCoordinate (p u) (p w) right).im ≤ 0

def sharedReceiverRegion (z : ℂ) : Prop :=
  0 ≤ z.re ∧ z.re ≤ 5 / 2 ∧ -2 ≤ z.im ∧ z.im ≤ -1 / 2 ∧
    (z.re ≤ 2 ∨ -1 ≤ z.im)

/-- A far diameter partner and a shallow left/right hull span certify actual
topological interior membership throughout the two-part receiving region. -/
theorem NormalizedHullSpan.receiver_mem_interior {n : ℕ}
    (p : Fin n → Point) {u w j : Fin n}
    (span : NormalizedHullSpan p u w) (hne : p u ≠ p w)
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (hsupport : 0 ≤ turn (p w) (p u) (p j))
    (x : Point) (hx : sharedReceiverRegion (edgeCoordinate (p u) (p w) x)) :
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
  obtain ⟨hqlo, hqhi, hylo, hyhi, hshape⟩ := hx
  obtain ⟨_hdet, hLJ, hJRq, hRL⟩ := long_triangle_rectangle_strict_turns
    (M span.left) (M (p j)) (M span.right) (M x) (-(M (p j)).im)
    hD span.left_re span.right_re (by simpa only [neg_div] using span.left_im.1)
    span.left_im.2 (by simpa only [neg_div] using span.right_im.1)
    span.right_im.2 hJlo hJhi (by ring)
    hqlo hqhi hylo hyhi hshape
  exact normalized_triangle_mem_interior_convexHull (Set.range p)
    (p u) (p w) span.left (p j) span.right x hne
    span.left_mem (subset_convexHull ℝ _ (Set.mem_range_self j))
    span.right_mem hLJ hJRq hRL

theorem hexagon_receiver_sites_in_region (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = 3 / 4) :
    sharedReceiverRegion ((3 / 2 : ℂ) - (h : ℂ) * Complex.I) ∧
    sharedReceiverRegion ((1 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I) ∧
    sharedReceiverRegion ((2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I) ∧
    sharedReceiverRegion ((5 / 2 : ℂ) - (h : ℂ) * Complex.I) := by
  have hhlo : 1 / 2 < h := by nlinarith
  have hhhi : h < 1 := by nlinarith
  norm_num [sharedReceiverRegion]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> linarith

end Erdos957
