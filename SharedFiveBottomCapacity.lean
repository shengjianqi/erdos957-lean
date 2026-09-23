import LowDegreeCapacity

/-! Complete capacity at shared-five bottom sites, using their actual depth. -/

namespace Erdos957

theorem certified_family_sharedFive_bottom_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (q : Fin n) (choice : SharedFiveCenterChoice p q)
    (hsource : v i = choice.left ∨ v i = choice.right)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.selection.bottom ≤
      2 * (6 - (nearestGraph p).degree choice.selection.bottom) := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
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
  have hdeep (w : Fin n) (hu : v i ∈ diameterEndpoints p)
      (hw : w ∈ diameterEndpoints p) (hadj : (nearestGraph p).Adj (v i) w)
      (hclose : dist (p (v i)) (p choice.selection.bottom) ≤ 2 * pairDist p ij)
      (hd : (5 / 3 : ℝ) ≤
        |(edgeCoordinate (p (v i)) (p w) (p choice.selection.bottom)).im|) :
      ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
          u choice.selection.bottom ≤
        2 * (6 - (nearestGraph p).degree choice.selection.bottom) := by
    exact certified_family_deep_receiver_capacity p hp hn v hv hh hrange hsupport hpos
      ij hmin i hgood hu choice.selection.bottom hclose
      (tight_flat_deep_base_receiver_depth p hp hn v hv hh hsupport hpos ij hmin
        i hgood hu w hw hadj choice.selection.bottom hclose hd) height assignments
  rcases hsource with hs | hs
  · apply hdeep choice.right (by simpa only [hs] using choice.left_diameter)
      choice.right_diameter (by simpa only [hs] using choice.base)
      (by simpa only [hs] using hpath choice.left choice.center_left)
    simpa only [hs] using hdepth
  · apply hdeep choice.left (by simpa only [hs] using choice.right_diameter)
      choice.left_diameter (by simpa only [hs] using choice.base.symm)
      (by simpa only [hs] using hpath choice.right choice.center_right)
    rw [hs, edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne)]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hdepth

end Erdos957

