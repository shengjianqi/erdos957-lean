import SharedFiveBottomCapacity

/-! The last degree-five interface: receivers without diameter neighbors.
Every active source of a hypothetical overload is indirect and has a
six-degree shared-five bottom; three such sources contradict endpoint packing. -/

namespace Erdos957

/-- Every indirect active source in any degree-five overload uses a six-bottom
shared-five rule. No assumption about diameter neighbors is needed. -/
theorem degree_five_overload_indirect_is_six_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (u : Fin n) (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hnot : ¬ (nearestGraph p).Adj u x) :
    SixBottomIndirectSource p v height assignments x u := by
  have hxrule : 0 < (assignments u hud).rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  have hfive : (nearestGraph p).degree (assignments u hud).context.q = 5 := by
    rcases (assignments u hud).rule.center_degree_five_or_six_of_indirect
      x hxrule hnot with h5 | h6
    · exact h5
    · have hcap := certified_family_capacity_of_indirect_degree_six_center_source
        p hp hn v hv hh hrange hsupport hpos height assignments u hud x hx hnot hdegree h6
      omega
  have av : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q) :=
    (assignments u hud).rule.sharedFive_available_of_indirect hfive x hxrule hnot
  refine ⟨hud, hx, hnot, av, ?_⟩
  let choice := selectedSharedFiveCenter p (assignments u hud).context.q av
  have hxcharge : 0 < choice.charge u x := by
    simpa only [(assignments u hud).rule.weight_eq_selected_sharedFive av x] using hxrule
  have hxq : x ≠ (assignments u hud).context.q :=
    fun heq => hnot (heq ▸ (assignments u hud).context.central_adj)
  rcases choice.selection.branch with hlow | hsix
  · have hxb : x = choice.selection.bottom := by
      by_contra hxb
      simp only [SharedFiveCenterChoice.charge, LocalChargePacket.weight,
        choice.selection.first_central, choice.selection.second_central,
        hlow.2.1, hlow.2.2, ite_eq_right hxq, ite_eq_right hxb,
        zero_add, ite_self] at hxcharge
      omega
    have hurange : u ∈ Set.range v := by
      rw [hrange]
      exact diameterEndpoints_subset_hullVertexIndices p hp (Finset.mem_filter.mp hud).1
    obtain ⟨i, hi⟩ := hurange
    have hcap := certified_family_sharedFive_bottom_capacity p hp hn v hv hh
      hrange hsupport hpos i (by simpa only [hi] using (Finset.mem_filter.mp hud).2.1)
      (assignments u hud).context.q choice
      (by
        simpa only [hi] using (choice.diameter_neighbor_cases u
          (assignments u hud).context.endpoint (assignments u hud).context.central_adj.symm))
      height assignments
    rw [← hxb] at hcap
    omega
  · exact hsix.1

/-- Complete degree-five capacity without a diameter endpoint neighbor,
uniform over every supplied certified assignment family. -/
theorem certified_family_degree_five_capacity_of_no_diameter_neighbor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hno : ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  classical
  by_contra hfail
  have hover := Nat.lt_of_not_ge hfail
  let A := (chargeDonors p (tightHullBadVertices p v)).filter fun u =>
    0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x
  have hA3 : 3 ≤ A.card := certified_family_degree_five_overload_active_card_ge_three
    p (tightHullBadVertices p v) height assignments x hdegree hover
  obtain ⟨u, w, z, huA, hwA, hzA, huw, huz, hwz⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < A.card by omega)
  have hsource (a : Fin n) (ha : a ∈ A) :
      SixBottomIndirectSource p v height assignments x a := by
    obtain ⟨had, hax⟩ := Finset.mem_filter.mp ha
    exact degree_five_overload_indirect_is_six_bottom p hp hn v hv hh
      hrange hsupport hpos height assignments x hdegree hover a had hax
      (fun hax => hno a hax.symm (Finset.mem_filter.mp had).1)
  have hu := hsource u huA
  have hw := hsource w hwA
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp
      (Finset.mem_filter.mp (Finset.mem_filter.mp huA).1).1
  obtain ⟨i, rfl⟩ := hurange
  obtain ⟨hzd, hzx⟩ := Finset.mem_filter.mp hzA
  exact two_six_bottom_sources_no_third_active p hp hn v hv hh hrange hsupport hpos
    height assignments hu hw huw.symm huz.symm hwz.symm hzd hzx

end Erdos957
