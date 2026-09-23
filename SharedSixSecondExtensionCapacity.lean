import DeepFiveObstruction
import SharedFiveSixExtensionExclusion

/-! Full incoming capacity at the forward shared-six second extension.  The
mixed shared-five obstruction is now strong enough to discharge the abstract
deep degree-five overload reduction, so every simultaneous certified source
is included in the bound. -/

namespace Erdos957

/-- A retained forward shared-six degree-five right receiver that is not the
first lower site has the full global incoming capacity.  The branch theorem
identifies it with the second extension `t₂`; the mixed exclusion then rules
out every saturated shared-five pair required by a hypothetical overload. -/
theorem certified_family_sharedSix_second_extension_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  have hpositive : 0 < choice.packet.weight choice.packet.right := by
    rw [choice.site_weights.2]
    omega
  have hclose := choice.packet.positive_dist_le_two_min ctx.minPair_spec hpositive
  obtain ⟨t₂, hright, _, _, _, _, ht₂coord, _⟩ :=
    choice.degree_five_right_second_extension_data hdegree hnot_lower
  have hrightCoord :
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I := by
    rw [hright]
    exact ht₂coord
  have hbaseDepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p (v i)) (p partner) (p choice.packet.right)).im| := by
    have hhgt : (5 / 3 : ℝ) ≤ 2 * choice.height := by
      nlinarith [choice.height_pos, choice.height_sq]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne), hrightCoord]
    simpa [abs_of_pos choice.height_pos] using hhgt
  have hdeep := tight_flat_deep_base_receiver_depth p hp hn v hv hh hsupport hpos
    ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint partner
    choice.partner_diameter choice.base.symm choice.packet.right hclose hbaseDepth
  have hle := certified_family_deep_five_capacity_of_no_sharedFive_pair
    p hp hn v hv hh hrange hsupport hpos ctx.minPair ctx.minPair_spec i
    ctx.outside_bad ctx.endpoint choice.packet.right hclose hdeep hdegree height
    assignments (by
      intro q available hleft _hright
      exact (tight_flat_sharedSix_second_extension_ne_sharedFive_bottom_of_left_donor
        p hp hn v hv hh hrange hsupport hpos i ctx partner q choice hdegree
        hnot_lower (selectedSharedFiveCenter p q available) hleft).symm)
  simpa only [hdegree] using hle

end Erdos957
