import DegreeFiveMixedReduction

/-! Structural reduction for the remaining mixed degree-five regime.  A
positive indirect transfer from a five-degree retained center cannot use the
low-bottom shared-five branch once the receiver has an actual diameter
neighbor.  Hence it necessarily comes from the degree-six-bottom branch. -/

namespace Erdos957

/-- At a mixed receiver, an indirect source whose retained center has degree
five comes from a selected shared-five pair with a degree-six deepest bottom.
This removes the unit-weight low-bottom branch from shallow mixed accounting. -/
theorem certified_indirect_degree_five_center_mixed_forces_six_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {u x : Fin n} (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hnot : ¬ (nearestGraph p).Adj u x)
    (hfive : (nearestGraph p).degree (assignments u hud).context.q = 5)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ available : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q),
      (nearestGraph p).degree
        (selectedSharedFiveCenter p (assignments u hud).context.q available).selection.bottom = 6 := by
  classical
  let aU := assignments u hud
  have hxrule : 0 < aU.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aU] using hx
  let available := aU.rule.sharedFive_available_of_indirect hfive x hxrule hnot
  let selected := selectedSharedFiveCenter p aU.context.q available
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hud).1
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp huD
  obtain ⟨i, hui⟩ := hurange
  have hgood0 : u ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hud).2.1
  have hsource0 : u = selected.left ∨ u = selected.right :=
    selected.diameter_neighbor_cases u huD aU.context.central_adj.symm
  have hxcharge : 0 < selected.charge u x := by
    simpa only [aU.rule.weight_eq_selected_sharedFive available x] using hxrule
  rcases selected.selection.branch with hlow | hsix
  · exfalso
    have hxp : x ≠ aU.context.q := fun heq => hnot (heq ▸ aU.context.central_adj)
    have hxbot : x = selected.selection.bottom := by
      by_contra hxb
      simp only [SharedFiveCenterChoice.charge, LocalChargePacket.weight,
        selected.selection.first_central, selected.selection.second_central,
        hlow.2.1, hlow.2.2, ite_eq_right hxp, ite_eq_right hxb,
        zero_add, ite_self] at hxcharge
      omega
    obtain ⟨a, haD, hxa⟩ := hdiam
    have hno := sharedFive_bottom_no_diameter_neighbor p hp hn v hv hh
      hsupport hpos aU.context.minPair aU.context.minPair_spec i
      (by simpa only [hui] using hgood0) aU.context.q selected
      (by simpa only [hui] using hsource0)
    exact (hno a (by simpa only [hxbot] using hxa)) haD
  · exact ⟨available, hsix.1⟩

end Erdos957
