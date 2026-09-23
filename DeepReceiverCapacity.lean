import IndirectChargeUnitBound
import DeepCenterPacking

/-! Full incoming capacity at deep receivers of degree at most four. This
includes all simultaneous certified rules, not only one center's packets. -/

namespace Erdos957

/-- In the absence of diameter neighbors, the complete certified charge is
bounded by the number of diameter endpoints within two nearest distances. -/
theorem certified_family_total_le_nearby_diameter_card_of_no_diameter_neighbor {n : ℕ}
    (p : Fin n → Point) (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n)
    (hno : ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
        ((diameterEndpoints p).filter fun u =>
          dist (p u) (p x) ≤ 2 * pairDist p ij).card := by
  classical
  let packets := certifiedFamilyPackets p bad height assignments
  have hunit := certified_family_total_le_positive_sources_card_of_no_diameter_neighbor
    p bad height assignments x hno
  have hsub : ((chargeDonors p bad).filter (fun u =>
      0 < localPacketCharge p bad packets u x)) ⊆
      ((diameterEndpoints p).filter (fun u => dist (p u) (p x) ≤ 2 * pairDist p ij)) := by
    intro u hu
    obtain ⟨hudonor, hpos⟩ := Finset.mem_filter.mp hu
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hudonor).1, ?_⟩
    apply (packets u hudonor).positive_dist_le_two_min hmin
    simpa only [localPacketCharge, dite_eq_left hudonor] using hpos
  exact hunit.trans (Finset.card_le_card hsub)

/-- All certified charge into an actually deep receiver totals at most
three doubled units, because each positive source is indirect and unit-sized. -/
theorem certified_family_deep_receiver_total_le_three {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤ 3 := by
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  have hunit := certified_family_total_le_nearby_diameter_card_of_no_diameter_neighbor
    p ij hmin bad height assignments x hno
  have hcard := tight_flat_deep_nearby_diameter_endpoints_card_le_three
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu x hclose hdeep
  exact hunit.trans hcard

/-- The complete incoming certified charge respects capacity at any deep
receiver of degree at most four, including every direct and indirect branch. -/
theorem certified_family_deep_receiver_capacity_of_degree_le_four {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hdegree : (nearestGraph p).degree x ≤ 4) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
        2 * (6 - (nearestGraph p).degree x) := by
  have ht := certified_family_deep_receiver_total_le_three p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep bad height assignments
  omega

/-- The retained shared-five bottom receives at most three doubled units
from the entire certified family when either endpoint is an actual good diameter endpoint.
The family need not use this particular retained center choice. -/
theorem certified_family_sharedFive_bottom_total_le_three {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (q : Fin n) (choice : SharedFiveCenterChoice p q)
    (hsource : v i = choice.left ∨ v i = choice.right)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments)
        u choice.selection.bottom ≤ 3 := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  have hno := sharedFive_bottom_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood q choice hsource
  have htotal := certified_family_total_le_nearby_diameter_card_of_no_diameter_neighbor
    p ij hmin bad height assignments choice.selection.bottom hno
  exact htotal.trans (sharedFive_bottom_nearby_diameter_card_le_three
    p hp hn v hv hh hsupport hpos ij hmin i hgood q choice hsource)

/-- The complete incoming certified charge respects capacity at any retained
shared-five bottom of degree at most four with an actual good endpoint. -/
theorem certified_family_sharedFive_bottom_capacity_of_degree_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (q : Fin n) (choice : SharedFiveCenterChoice p q)
    (hsource : v i = choice.left ∨ v i = choice.right)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hdegree : (nearestGraph p).degree choice.selection.bottom ≤ 4) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments)
        u choice.selection.bottom ≤ 2 * (6 - (nearestGraph p).degree choice.selection.bottom) := by
  have ht := certified_family_sharedFive_bottom_total_le_three p hp hn v hv hh
    hsupport hpos i hgood q choice hsource bad height assignments
  omega

/-- The nearest-partner depth criterion also supplies full receiver capacity
without a separate depth premise in the actual outgoing hull-edge frame. -/
theorem certified_family_deep_base_receiver_capacity_of_degree_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p)
    (w : Fin n) (hw : w ∈ diameterEndpoints p) (huw : (nearestGraph p).Adj (v i) w)
    (x : Fin n) (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (5 / 3 : ℝ) ≤ |(edgeCoordinate (p (v i)) (p w) (p x)).im|)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hdegree : (nearestGraph p).degree x ≤ 4) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
        2 * (6 - (nearestGraph p).degree x) := by
  exact certified_family_deep_receiver_capacity_of_degree_le_four p hp hn v hv hh
    hsupport hpos ij hmin i hgood hu x hclose
    (tight_flat_deep_base_receiver_depth p hp hn v hv hh hsupport hpos
      ij hmin i hgood hu w hw huw x hclose hdeep) bad height assignments hdegree

end Erdos957
