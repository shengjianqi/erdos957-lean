import FourEndpointPacking

namespace Erdos957

theorem tight_flat_far_deep_receiver_no_diameter_neighbor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (x : Fin n) (hclose : dist (p (v i)) (p x) ≤ 3 * pairDist p ij)
    (hxre : |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re| ≤
      2 * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))))
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im) :
    ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p := by
  let M := fun k => edgeCoordinate (p (v i)) (p (v (i + 1))) (p k)
  let L := dist (p (v i)) (p (v (i + 1)))
  let r := pairDist p ij / L
  have hne : p (v i) ≠ p (v (i + 1)) := hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hL : 0 < L := dist_pos.mpr hne
  have hr : 0 < r := div_pos (pairDist_pos p hp hmin.1) hL
  intro a hxa haD
  have hxaDist := nearestGraph_adj_dist_eq p hmin hxa
  have huaDist : dist (p (v i)) (p a) ≤ 4 * pairDist p ij := by
    have ht := dist_triangle (p (v i)) (p x) (p a)
    linarith
  have hdiffNorm : ‖M x - M a‖ = r := by
    rw [← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hne, hxaDist]
  have haRe : |(M a).re| ≤ 3 * r := by
    have hd := Complex.abs_re_le_norm (M x - M a)
    rw [hdiffNorm, Complex.sub_re] at hd
    change |(M x).re| ≤ 2 * r at hxre
    have ht : |(M a).re| ≤ |(M x).re - (M a).re| + |(M x).re| := by
      calc
        |(M a).re| = |(M x).re - ((M x).re - (M a).re)| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_sub_comm, add_comm] using abs_sub (M x).re ((M x).re - (M a).re)
    linarith
  have haLocal := tight_flat_four_distance_diameter_endpoint_local
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu a haD
    (by linarith [pairDist_pos p hp hmin.1]) (by change |(M a).re| ≤ _; dsimp [r, L] at haRe ⊢; linarith [hr])
  have haSlope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i hgood a haLocal
  change |(M a).im| ≤ |(M a).re| / 30 at haSlope
  have haIm : (M a).im ≤ r / 10 := by linarith [le_abs_self (M a).im]
  have hdiffIm : (M x).im - (M a).im ≤ r := by
    have ht := Complex.im_le_norm (M x - M a)
    simpa only [Complex.sub_im, hdiffNorm] using ht
  change (3 / 2 : ℝ) * r ≤ (M x).im at hdeep
  linarith

end Erdos957

