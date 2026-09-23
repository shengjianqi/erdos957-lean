import ReflectedSharedSixTerminalGeometry

/-! Complete low-degree shared-six capacity, including the terminal sites. -/

namespace Erdos957

/-- Every selected right receiver of degree <=4 satisfies the full incoming
capacity, for every simultaneous certified family, including the terminal branch. -/
theorem certified_family_sharedSix_low_right_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  rcases choice.branch with ⟨_, hright⟩ |
    ⟨_, t₂, _, houter, _, hcoord₂, hcases⟩
  · apply certified_family_sharedSix_deep_right_low_capacity
      p hp hn v hv hh hsupport hpos i ctx partner choice _ hdegree height assignments
    left
    rw [hright]
    exact choice.lower_coordinate
  · rcases hcases with ⟨_, hright⟩ | ⟨hdeg, hadj, _, hcoordx, _⟩
    · apply certified_family_sharedSix_deep_right_low_capacity
        p hp hn v hv hh hsupport hpos i ctx partner choice _ hdegree height assignments
      exact Or.inr (hright ▸ hcoord₂)
    · obtain ⟨z, hne, hxy, hxz, hyD, hzD, hno⟩ :=
        choice.terminal_blocked_neighbors p hp hn v hv hh hsupport hpos
          i ctx partner hrange t₂ hdeg houter hadj hcoord₂ hcoordx
      exact certified_family_capacity_of_two_blocked_neighbors p
        (tightHullBadVertices p v) height assignments
        (tight_flat_direct_sources_card_le_two p hp hn v hv hh hrange hsupport hpos)
        choice.packet.right hdegree t₂ z hne hxy hxz hyD hzD (by omega) hno

/-- Every selected right receiver of degree <=4 satisfies the full incoming
capacity, for every simultaneous certified family, including the terminal branch. -/
theorem certified_family_reflectedSharedSix_low_right_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  rcases choice.receiver_rule with ⟨_, hright⟩ |
    ⟨_, t₂, _, houter, _, hcoord₂, hcases⟩
  · apply certified_family_reflectedSharedSix_deep_right_low_capacity
      p hp hn v hv hh hsupport hpos i ctx partner choice _ hdegree height assignments
    left
    rw [hright]
    exact choice.original_coordinates.2.2
  · rcases hcases with ⟨_, hright⟩ | ⟨hdeg, hadj, _, hcoordx, _⟩
    · apply certified_family_reflectedSharedSix_deep_right_low_capacity
        p hp hn v hv hh hsupport hpos i ctx partner choice _ hdegree height assignments
      exact Or.inr (hright ▸ hcoord₂)
    · obtain ⟨z, hne, hxy, hxz, hyD, hzD, hno⟩ :=
        choice.terminal_blocked_neighbors p hp hn v hv hh hsupport hpos
          i ctx partner hrange t₂ hdeg houter hadj hcoord₂ hcoordx
      exact certified_family_capacity_of_two_blocked_neighbors p
        (tightHullBadVertices p v) height assignments
        (tight_flat_direct_sources_card_le_two p hp hn v hv hh hrange hsupport hpos)
        choice.packet.right hdegree t₂ z hne hxy hxz hyD hzD (by omega) hno

end Erdos957

