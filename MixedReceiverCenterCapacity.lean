import DeepFiveCapacityComplete
import ActualSharedFiveGroups
import SharedSixPairCompatibility

/-! Mixed receivers: an actual diameter-neighbor at the receiver prevents two
indirect units from coming from the same retained center.  Thus each center
contributes at most one indirect unit in the only regime not already covered
by the deep-receiver theorem. -/

namespace Erdos957

/-- If a receiver has an actual diameter-endpoint neighbor, two distinct
indirect positive donors cannot have the same retained center.  For a
five-degree center, two such donors force the receiver to be the selected
shared-five bottom, which has no diameter neighbor.  For a six-degree center,
the existing shared-six two-source incompatibility applies. -/
theorem certified_indirect_same_center_eq_of_receiver_has_diameter_neighbor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {u w x : Fin n}
    (hu : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hw : w ∈ chargeDonors p (tightHullBadVertices p v))
    (hcenter : (assignments u hu).context.q = (assignments w hw).context.q)
    (hxu : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hxw : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hnotu : ¬ (nearestGraph p).Adj u x)
    (hnotw : ¬ (nearestGraph p).Adj w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    u = w := by
  classical
  by_contra huw
  let aU := assignments u hu
  let aW := assignments w hw
  have hxuRule : 0 < aU.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hu, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aU] using hxu
  have hxwRule : 0 < aW.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hw, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aW] using hxw
  have hcenter' : aU.context.q = aW.context.q := by simpa only [aU, aW] using hcenter
  obtain ⟨ruleW, hpacketW⟩ : ∃ ruleW : CertifiedDonorRule p w aU.context.q (height w),
      ruleW.packet = aW.rule.packet := by
    rw [hcenter']
    exact ⟨aW.rule, rfl⟩
  have hxwRule' : 0 < ruleW.packet.weight x := by
    rw [hpacketW]
    exact hxwRule
  have hwcentral : (nearestGraph p).Adj aU.context.q w := by
    have := aW.context.central_adj.symm
    simpa only [hcenter'] using this
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hu).1
  have hwD : w ∈ diameterEndpoints p := (Finset.mem_filter.mp hw).1
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp huD
  obtain ⟨i, hui⟩ := hurange
  subst u
  have hgood : v i ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hu).2.1
  have hcenterCases := aU.rule.center_degree_five_or_six_of_indirect x hxuRule hnotu
  rcases hcenterCases with hfive | hsix
  · obtain ⟨available, hxbottom, hpair, _hlow⟩ :=
      certified_sharedFive_paired_indirect_receiver aU.rule ruleW hfive
        aU.context.endpoint hwD aU.context.central_adj.symm hwcentral huw
        hxuRule hxwRule' hnotu hnotw
    let selected := selectedSharedFiveCenter p aU.context.q available
    have hsource : v i = selected.left ∨ v i = selected.right := by
      rcases hpair with hpairCase | hpairCase
      · exact Or.inl hpairCase.1
      · exact Or.inr hpairCase.1
    obtain ⟨a, haD, hxa⟩ := hdiam
    have hno := sharedFive_bottom_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos aU.context.minPair aU.context.minPair_spec i hgood
      aU.context.q selected hsource
    exact (hno a (by simpa only [hxbottom] using hxa)) haD
  · exact huw (tight_flat_certified_six_indirect_sources_eq p hp hn v hv hh
      hsupport hpos i aU.context aU.rule ruleW hsix hwD hwcentral
      hxuRule hxwRule' hnotu hnotw)

/-- At a receiver having a diameter-endpoint neighbor, the indirect part of
one retained center group is at most one unit.  This is the center-group form
needed for shallow simultaneous accounting. -/
theorem centerIndirectPacketChargeTotal_le_one_of_receiver_has_diameter_neighbor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (q x : Fin n)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    centerIndirectPacketChargeTotal p (tightHullBadVertices p v)
      height assignments q x ≤ 1 := by
  classical
  let S := (centerChargeSources p (tightHullBadVertices p v) height assignments q).filter
    (fun u => ¬ (nearestGraph p).Adj u x)
  let f := fun u : Fin n => localPacketCharge p (tightHullBadVertices p v)
    (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x
  have hunit : ∀ u ∈ S, f u ≤ 1 := by
    intro u huS
    have hnot := (Finset.mem_filter.mp huS).2
    exact certified_family_charge_le_one_of_not_adj p (tightHullBadVertices p v)
      height assignments u x hnot
  have hactive_unique : ∀ u ∈ S, 0 < f u → ∀ w ∈ S, 0 < f w → u = w := by
    intro u huS hupos w hwS hwpos
    have huCenter := (Finset.mem_filter.mp huS).1
    have hwCenter := (Finset.mem_filter.mp hwS).1
    obtain ⟨huD, huC⟩ := Finset.mem_filter.mp huCenter
    obtain ⟨hwD, hwC⟩ := Finset.mem_filter.mp hwCenter
    rw [assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments u huD] at huC
    rw [assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments w hwD] at hwC
    apply certified_indirect_same_center_eq_of_receiver_has_diameter_neighbor
      p hp hn v hv hh hrange hsupport hpos height assignments huD hwD
    · exact huC.trans hwC.symm
    · exact hupos
    · exact hwpos
    · exact (Finset.mem_filter.mp huS).2
    · exact (Finset.mem_filter.mp hwS).2
    · exact hdiam
  have hactive_card : (S.filter (fun u => 0 < f u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu w hw
    exact hactive_unique u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
      w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  change ∑ u ∈ S, f u ≤ 1
  calc
    ∑ u ∈ S, f u = ∑ u ∈ S.filter (fun u => 0 < f u), f u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu hnot
      exact Nat.eq_zero_of_not_pos (fun hpos => hnot (Finset.mem_filter.mpr ⟨hu, hpos⟩))
    _ ≤ ∑ _u ∈ S.filter (fun u => 0 < f u), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hunit u (Finset.mem_filter.mp hu).1
    _ = (S.filter (fun u => 0 < f u)).card := by simp
    _ ≤ 1 := hactive_card

end Erdos957
