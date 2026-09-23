import DegreeFiveNoDiameterCapacity
import WeightedChargeAssembly

/-! All receiver degrees are covered for the concrete supporting-height family. -/

namespace Erdos957

/-- Complete simultaneous weighted capacity, with no receiver degree,
depth, adjacency or local exclusion hypothesis left. -/
theorem supporting_family_receiver_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (x : Fin n) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v)
          (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos)) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  let height := hullSupportingHeight p v
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  have hdeg6 := nearestGraph_degree_le_six p (by omega : 2 ≤ n) hp x
  by_cases hlow : (nearestGraph p).degree x ≤ 4
  · exact certified_family_receiver_capacity_of_degree_le_four
      p hp hn v hv hh hrange hsupport hpos height assignments x hlow
  by_cases hfive : (nearestGraph p).degree x = 5
  · by_cases hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a
    · exact supporting_family_degree_five_mixed_capacity
        p hp hn v hv hh hrange hsupport hpos x hfive hdiam
    · exact certified_family_degree_five_capacity_of_no_diameter_neighbor
        p hp hn v hv hh hrange hsupport hpos height assignments x hfive
        (fun a hxa haD => hdiam ⟨a, haD, hxa⟩)
  · have hsix : (nearestGraph p).degree x = 6 := by omega
    have hz := certified_family_receiver_total_eq_zero_of_degree_six
      p (tightHullBadVertices p v) height assignments x hsix
    change (∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x) ≤ _
    rw [hz]
    exact Nat.zero_le _

/-- An actual charge certificate, with the geometric exceptional set retained. -/
noncomputable def supporting_family_charge_certificate
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k) : ChargeCertificate p :=
  chargeCertificate_of_weighted_localPackets p (tightHullBadVertices p v)
    (certifiedFamilyPackets p (tightHullBadVertices p v)
      (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos))
    (fun x _ => supporting_family_receiver_capacity
      p hp hn v hv hh hrange hsupport hpos x)

theorem supporting_family_count_bound
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k) :
    sMin p + 2 * diameterEndpointCount p ≤
      3 * n + (tightHullBadVertices p v).card :=
  (supporting_family_charge_certificate p hp hn v hv hh hrange hsupport hpos).count_bound
    (by omega) hp

end Erdos957

