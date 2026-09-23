import SharedSixRightCapacity

/-! A degree-six retained center cannot participate in a hypothetical
indirect overload at a degree-five receiver.  Constructor analysis reduces
such a source to one of the two shared-six orientations, whose full right-site
capacity is already proved. -/

namespace Erdos957

/-- If an actual donor contributes indirectly to a degree-five receiver and
its retained center has degree six, then the complete assembled family already
satisfies receiver capacity.  In particular, no hypothetical degree-five
overload can contain a degree-six-centered source. -/
theorem certified_family_capacity_of_indirect_degree_six_center_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (u : Fin n) (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (x : Fin n)
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hnot : ¬ (nearestGraph p).Adj u x)
    (hdegree : (nearestGraph p).degree x = 5)
    (hsix : (nearestGraph p).degree (assignments u hud).context.q = 6) :
    ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hud).1
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp huD
  obtain ⟨i, rfl⟩ := hurange
  let a := assignments (v i) hud
  have hxrule : 0 < a.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, a] using hx
  change (nearestGraph p).degree a.context.q = 6 at hsix
  cases hrule : a.rule with
  | low choice =>
      have hlow := choice.central_degree
      omega
  | unique choice high =>
      have hxchoice : 0 < choice.packet.weight x := by
        simpa only [hrule, CertifiedDonorRule.packet] using hxrule
      exact False.elim (hnot (choice.positive_adj x hxchoice))
  | sharedFive available endpoint central =>
      let selected := selectedSharedFiveCenter p a.context.q available
      have hfive : (nearestGraph p).degree a.context.q = 5 := selected.center_degree
      omega
  | @sharedSix partner choice =>
      have hxchoice : 0 < choice.packet.weight x := by
        simpa only [hrule, CertifiedDonorRule.packet] using hxrule
      exact certified_family_capacity_of_indirect_sharedSix_source
        p hp hn v hv hh hrange hsupport hpos i a.context partner choice x hxchoice
        hnot hdegree height assignments
  | @reflectedSharedSix partner choice =>
      have hxchoice : 0 < choice.packet.weight x := by
        simpa only [hrule, CertifiedDonorRule.packet] using hxrule
      exact certified_family_capacity_of_indirect_reflectedSharedSix_source
        p hp hn v hv hh hrange hsupport hpos i a.context partner choice x hxchoice
        hnot hdegree height assignments

end Erdos957
