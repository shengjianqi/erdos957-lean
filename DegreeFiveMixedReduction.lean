import MixedReceiverCenterCapacity
import DeepFiveDegreeSixSourceCapacity

/-! Degree-five mixed overloads contain only degree-five retained centers on
the indirect side.  The degree-six shared-six branches already imply full
receiver capacity globally and therefore cannot occur in an overload. -/

namespace Erdos957

/-- In any degree-five overload, every positive indirect source has a
five-degree retained center.  No deep-receiver premise is used. -/
theorem certified_family_degree_five_overload_indirect_center_degree_five
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
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
    (nearestGraph p).degree (assignments u hud).context.q = 5 := by
  have hxrule : 0 < (assignments u hud).rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  rcases (assignments u hud).rule.center_degree_five_or_six_of_indirect x hxrule hnot with
      hfive | hsix
  · exact hfive
  · have hcap := certified_family_capacity_of_indirect_degree_six_center_source
      p hp hn v hv hh hrange hsupport hpos height assignments u hud x hx hnot hdegree hsix
    omega

end Erdos957
