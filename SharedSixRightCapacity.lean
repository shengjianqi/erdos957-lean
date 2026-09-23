import ReflectedSharedSixSecondExtensionCapacity
import DeepFiveRuleCases

/-! Consolidated full-capacity interfaces for degree-five right receivers of
forward and reflected shared-six rules.  These theorems hide the first-lower
versus second-extension split and expose the form needed by the remaining
third-source classification. -/

namespace Erdos957

/-- Every degree-five right receiver selected by a forward shared-six rule has
full simultaneous incoming capacity. -/
theorem certified_family_sharedSix_degree_five_right_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  by_cases hselected : choice.packet.right = choice.lower
  · have hle := certified_family_sharedSix_selected_lower_capacity
      p hp hn v hv hh hrange hsupport hpos i ctx partner choice hselected
      height assignments
    rw [hselected]
    exact hle
  · exact certified_family_sharedSix_second_extension_capacity
      p hp hn v hv hh hrange hsupport hpos i ctx partner choice hdegree hselected
      height assignments

/-- Every degree-five right receiver selected by a reflected shared-six rule
has full simultaneous incoming capacity. -/
theorem certified_family_reflectedSharedSix_degree_five_right_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n)
    (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  by_cases hselected : choice.packet.right = choice.reflected.lower
  · have hle := certified_family_reflectedSharedSix_selected_lower_capacity
      p hp hn v hv hh hrange hsupport hpos i ctx partner choice hselected
      height assignments
    rw [hselected]
    exact hle
  · exact certified_family_reflectedSharedSix_second_extension_capacity
      p hp hn v hv hh hrange hsupport hpos i ctx partner choice hdegree hselected
      height assignments

/-- If an indirect positive source uses a forward shared-six rule and its
receiver has degree five, the complete assembled family already satisfies
capacity at that receiver.  Thus such a source can never witness a hypothetical
deep degree-five overload. -/
theorem certified_family_capacity_of_indirect_sharedSix_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (x : Fin n) (hx : 0 < choice.packet.weight x)
    (hnot : ¬ (nearestGraph p).Adj (v i) x)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  let rule : CertifiedDonorRule p (v i) ctx.q (height (v i)) := .sharedSix choice
  have hright : x = choice.packet.right := by
    have ht := rule.indirect_receiver_eq_right x (by
      simpa only [rule, CertifiedDonorRule.packet] using hx) hnot
    simpa only [rule, CertifiedDonorRule.packet] using ht
  subst x
  exact certified_family_sharedSix_degree_five_right_capacity
    p hp hn v hv hh hrange hsupport hpos i ctx partner choice hdegree height assignments

/-- Reflected counterpart of `certified_family_capacity_of_indirect_sharedSix_source`. -/
theorem certified_family_capacity_of_indirect_reflectedSharedSix_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n)
    (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (x : Fin n) (hx : 0 < choice.packet.weight x)
    (hnot : ¬ (nearestGraph p).Adj (v i) x)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  let rule : CertifiedDonorRule p (v i) ctx.q (height (v i)) := .reflectedSharedSix choice
  have hright : x = choice.packet.right := by
    have ht := rule.indirect_receiver_eq_right x (by
      simpa only [rule, CertifiedDonorRule.packet] using hx) hnot
    simpa only [rule, CertifiedDonorRule.packet] using ht
  subst x
  exact certified_family_reflectedSharedSix_degree_five_right_capacity
    p hp hn v hv hh hrange hsupport hpos i ctx partner choice hdegree height assignments

end Erdos957
