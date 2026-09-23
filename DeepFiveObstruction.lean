import DeepOverloadSaturation
import DeepFiveRuleCases
import SharedFivePairedReceivers
import SharedSixLowerExclusion

/-! A complete reduction of hypothetical deep degree-five overload to an
actual shared-five bottom whose two selected endpoints are eligible donors.
This constrains the full simultaneous sum, not just two chosen packets. -/

namespace Erdos957

/-- Every hypothetical overload of a deep degree-five receiver contains a
saturated shared-five bottom with both actual endpoint donors. -/
theorem certified_family_deep_five_overload_has_sharedFive_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (hover : 2 < ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x) :
    ∃ (q : Fin n) (available : Nonempty (SharedFiveCenterChoice p q)),
      x = (selectedSharedFiveCenter p q available).selection.bottom ∧
      (selectedSharedFiveCenter p q available).left ∈ chargeDonors p (tightHullBadVertices p v) ∧
      (selectedSharedFiveCenter p q available).right ∈ chargeDonors p (tightHullBadVertices p v) := by
  classical
  let bad := tightHullBadVertices p v
  let packets := certifiedFamilyPackets p bad height assignments
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  have hsat := (certified_family_deep_overload_saturates_nearby p hp hn v hv hh
    hsupport hpos ij hmin i hgood hu x hclose hdeep bad height assignments hover).2.2
  obtain ⟨u, hud, hux, hnonexact⟩ := certified_family_deep_overload_has_nonexact_source
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu x hclose hdeep bad height assignments hover
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hud).1
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp huD
  obtain ⟨j, rfl⟩ := hurange
  let aU := assignments (v j) hud
  have hxU : 0 < aU.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hux
  have hnotU : ¬ (nearestGraph p).Adj (v j) x := fun hx => hno _ hx.symm huD
  obtain ⟨w, hwD, hwne, huw, hqw, hwclose⟩ :=
    (aU.rule.indirect_degree_five_exact_or_nearby_partner hp (by omega) ij hmin
      x hxU hnotU hdegree).resolve_left hnonexact
  obtain ⟨hwd, hwone⟩ := hsat w hwD hwclose
  let aW := assignments w hwd
  have hxW : 0 < aW.rule.packet.weight x := by
    have hpw : 0 < localPacketCharge p bad packets w x := by
      change localPacketCharge p bad packets w x = 1 at hwone
      omega
    simp only [localPacketCharge, dite_eq_left hwd] at hpw
    change 0 < (aW.rule.packet).weight x at hpw
    exact hpw
  have hnotW : ¬ (nearestGraph p).Adj w x := fun hx => hno _ hx.symm hwD
  have hcenter : aW.context.q = aU.context.q :=
    tight_flat_shared_partner_context_center_eq p hp hn v hv hh hsupport hpos
      j aU.context aW.context hqw hwne
  obtain ⟨ruleW, hxW'⟩ : ∃ ruleW : CertifiedDonorRule p w aU.context.q (height w),
      0 < ruleW.packet.weight x := by
    rw [← hcenter]
    exact ⟨aW.rule, hxW⟩
  rcases aU.rule.center_degree_five_or_six_of_indirect x hxU hnotU with hfive | hsix
  · obtain ⟨available, hbottom, hpair, _hlow⟩ :=
      certified_sharedFive_paired_indirect_receiver aU.rule ruleW hfive
        huD hwD aU.context.central_adj.symm hqw hwne.symm hxU hxW' hnotU hnotW
    refine ⟨aU.context.q, available, hbottom, ?_⟩
    rcases hpair with ⟨hul, hwr⟩ | ⟨hur, hwl⟩
    · exact ⟨hul ▸ hud, hwr ▸ hwd⟩
    · exact ⟨hwl ▸ hwd, hur ▸ hud⟩
  · have heq := tight_flat_certified_six_indirect_sources_eq p hp hn v hv hh
      hsupport hpos j aU.context aU.rule ruleW hsix hwD hqw hxU hxW' hnotU hnotW
    exact False.elim (hwne heq.symm)

/-- Excluding saturated shared-five bottoms is sufficient for the full deep
degree-five capacity, with all actual sources included in the sum. -/
theorem certified_family_deep_five_capacity_of_no_sharedFive_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (hexclude : ∀ q (available : Nonempty (SharedFiveCenterChoice p q)),
      (selectedSharedFiveCenter p q available).left ∈ chargeDonors p (tightHullBadVertices p v) →
      (selectedSharedFiveCenter p q available).right ∈ chargeDonors p (tightHullBadVertices p v) →
      x ≠ (selectedSharedFiveCenter p q available).selection.bottom) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤ 2 := by
  by_contra hnot
  obtain ⟨q, available, hbottom, hl, hr⟩ :=
    certified_family_deep_five_overload_has_sharedFive_pair p hp hn v hv hh hrange
      hsupport hpos ij hmin i hgood hu x hclose hdeep hdegree height assignments (by omega)
  exact hexclude q available hl hr hbottom

end Erdos957
