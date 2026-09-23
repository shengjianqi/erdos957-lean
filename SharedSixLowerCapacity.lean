import DeepFiveObstruction

/-! Full incoming capacity at the first selected lower shared-six receiver.
The degree-five case now follows from the proved obstruction reduction and
the actual mixed exclusion, including every other rule's contribution. -/

namespace Erdos957

theorem certified_family_sharedSix_selected_lower_capacity {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (w : Fin n) (choice : SharedSixPacketChoice p w (v i) ctx.q)
    (hselected : choice.packet.right = choice.lower)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u choice.lower ≤
      2 * (6 - (nearestGraph p).degree choice.lower) := by
  have hpositive : 0 < choice.packet.weight choice.lower := by
    rw [← hselected, choice.site_weights.2]
    omega
  have hclose := choice.packet.positive_dist_le_two_min ctx.minPair_spec hpositive
  have hbaseDepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p (v i)) (p w) (p choice.lower)).im| := by
    have hhgt : (5 / 3 : ℝ) ≤ 2 * choice.height := by
      nlinarith [choice.height_pos, choice.height_sq]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne), choice.lower_coordinate]
    simpa [abs_of_pos choice.height_pos] using hhgt
  have hdeep := tight_flat_deep_base_receiver_depth p hp hn v hv hh hsupport hpos
    ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint w
    choice.partner_diameter choice.base.symm choice.lower hclose hbaseDepth
  by_cases hfour : (nearestGraph p).degree choice.lower ≤ 4
  · exact certified_family_deep_receiver_capacity_of_degree_le_four p hp hn v hv hh
      hsupport hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint choice.lower
      hclose hdeep (tightHullBadVertices p v) height assignments hfour
  have hfive : (nearestGraph p).degree choice.lower = 5 := by
    have ht := choice.packet.right_degree
    rw [hselected] at ht
    omega
  have hle := certified_family_deep_five_capacity_of_no_sharedFive_pair p hp hn v hv hh
    hrange hsupport hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint
    choice.lower hclose hdeep hfive height assignments (by
      intro q available _hl _hr heq
      exact tight_flat_sharedSix_selected_lower_ne_sharedFive_bottom p hp hn v hv hh
        hrange hsupport hpos i ctx w q choice hselected
        (selectedSharedFiveCenter p q available) heq.symm)
  simpa only [hfive] using hle

end Erdos957
