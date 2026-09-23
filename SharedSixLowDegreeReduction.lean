import SixBottomLowDegreeCapacity
import DeepFiveDegreeSixSourceCapacity

/-! Low-degree shared-six receivers: the first two sites have full capacity.
Any remaining overload is forced into an actual terminal rule, in either orientation. -/

namespace Erdos957

/-- Both depth-two sites satisfy the full family bound, at every degree <=4. -/
theorem certified_family_sharedSix_deep_right_low_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hcoord : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (1 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  have hbase := choice.base
  have hpartnerD := choice.partner_diameter
  have hclose := choice.packet.positive_dist_le_two_min ctx.minPair_spec
    (by rw [choice.site_weights.2]; omega)
  have hdepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p (v i)) (p partner) (p choice.packet.right)).im| := by
    have hhgt : (5 / 3 : ℝ) ≤ 2 * choice.height := by
      nlinarith [choice.height_pos, choice.height_sq]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne hbase.ne)]
    rcases hcoord with hc | hc <;> rw [hc] <;>
      simpa [abs_of_pos choice.height_pos] using hhgt
  exact certified_family_deep_base_receiver_capacity_of_degree_le_four
    p hp hn v hv hh hsupport hpos ctx.minPair ctx.minPair_spec i
    ctx.outside_bad ctx.endpoint partner hpartnerD hbase.symm choice.packet.right
    hclose hdepth (tightHullBadVertices p v) height assignments hdegree

/-- A hypothetical overload forces the actual degree-six second extension
and the terminal coordinate; the first two receiver branches are excluded. -/
theorem SharedSixPacketChoice.low_overload_terminal_data
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (hover : 2 * (6 - (nearestGraph p).degree choice.packet.right) <
      ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right) :
    ∃ t₂ : Fin n,
      (nearestGraph p).degree t₂ = 6 ∧
      (nearestGraph p).Adj t₂ choice.packet.right ∧
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (5 / 2 : ℂ) - (choice.height : ℂ) * Complex.I := by
  have hnot (hc : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (1 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I) : False := by
    have hcap := certified_family_sharedSix_deep_right_low_capacity
      p hp hn v hv hh hsupport hpos i ctx partner choice hc hdegree height assignments
    omega
  rcases choice.branch with ⟨_, hright⟩ |
    ⟨_, t₂, _, _, _, ht₂coord, hcases⟩
  · apply False.elim
    apply hnot
    left
    rw [hright]
    exact choice.lower_coordinate
  · rcases hcases with ⟨_, hright⟩ | ⟨hdeg, hadj, _, hcoord, _⟩
    · exact False.elim (hnot (Or.inr (hright ▸ ht₂coord)))
    · exact ⟨t₂, hdeg, hadj, hcoord⟩

/-- Both depth-two sites satisfy the full family bound, at every degree <=4. -/
theorem certified_family_reflectedSharedSix_deep_right_low_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hcoord : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (1 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I)
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  have hG := nearestGraph_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hD := diameterEndpoints_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hbase : (nearestGraph p).Adj partner (v i) := by
    simpa only [hG] using choice.reflected.base
  have hpartnerD : partner ∈ diameterEndpoints p := by
    simpa only [hD] using choice.reflected.partner_diameter
  have hclose := choice.packet.positive_dist_le_two_min ctx.minPair_spec
    (by rw [choice.site_weights.2]; omega)
  have hdepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p (v i)) (p partner) (p choice.packet.right)).im| := by
    have hhgt : (5 / 3 : ℝ) ≤ 2 * choice.reflected.height := by
      nlinarith [choice.reflected.height_pos, choice.reflected.height_sq]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne hbase.ne)]
    rcases hcoord with hc | hc <;> rw [hc] <;>
      simpa [abs_of_pos choice.reflected.height_pos] using hhgt
  exact certified_family_deep_base_receiver_capacity_of_degree_le_four
    p hp hn v hv hh hsupport hpos ctx.minPair ctx.minPair_spec i
    ctx.outside_bad ctx.endpoint partner hpartnerD hbase.symm choice.packet.right
    hclose hdepth (tightHullBadVertices p v) height assignments hdegree

/-- A hypothetical overload forces the actual degree-six second extension
and the terminal coordinate; the first two receiver branches are excluded. -/
theorem ReflectedSharedSixPacketChoice.low_overload_terminal_data
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right ≤ 4)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (hover : 2 * (6 - (nearestGraph p).degree choice.packet.right) <
      ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right) :
    ∃ t₂ : Fin n,
      (nearestGraph p).degree t₂ = 6 ∧
      (nearestGraph p).Adj t₂ choice.packet.right ∧
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (5 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I := by
  have hnot (hc : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (1 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I) : False := by
    have hcap := certified_family_reflectedSharedSix_deep_right_low_capacity
      p hp hn v hv hh hsupport hpos i ctx partner choice hc hdegree height assignments
    omega
  rcases choice.receiver_rule with ⟨_, hright⟩ |
    ⟨_, t₂, _, _, _, ht₂coord, hcases⟩
  · apply False.elim
    apply hnot
    left
    rw [hright]
    exact choice.original_coordinates.2.2
  · rcases hcases with ⟨_, hright⟩ | ⟨hdeg, hadj, _, hcoord, _⟩
    · exact False.elim (hnot (Or.inr (hright ▸ ht₂coord)))
    · exact ⟨t₂, hdeg, hadj, hcoord⟩

end Erdos957
