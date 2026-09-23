import DeepExactRadiusPacking

/-! A hypothetical third incoming unit at a deep receiver forces every
nearby diameter endpoint to be an actual positive donor. This closes the
finite-set step needed to use pair compatibility in a simultaneous sum. -/

namespace Erdos957

/-- Over two units at a deep receiver forces exactly three nearby diameter
endpoints, all eligible, each contributing exactly one unit. -/
theorem certified_family_deep_overload_saturates_nearby {n h : ℕ} [NeZero h]
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
    (hover : 2 < ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x) :
    (∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x) = 3 ∧
    ((diameterEndpoints p).filter (fun u => dist (p u) (p x) ≤ 2 * pairDist p ij)).card = 3 ∧
    ∀ w, w ∈ diameterEndpoints p → dist (p w) (p x) ≤ 2 * pairDist p ij →
      w ∈ chargeDonors p bad ∧
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) w x = 1 := by
  classical
  let packets := certifiedFamilyPackets p bad height assignments
  let S := (chargeDonors p bad).filter (fun u => 0 < localPacketCharge p bad packets u x)
  let B := (diameterEndpoints p).filter (fun u => dist (p u) (p x) ≤ 2 * pairDist p ij)
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  have hunit := certified_family_total_le_positive_sources_card_of_no_diameter_neighbor
    p bad height assignments x hno
  change (∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x) ≤ S.card at hunit
  have hcard : B.card ≤ 3 := tight_flat_deep_nearby_diameter_endpoints_card_le_three
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu x hclose hdeep
  have hsub : S ⊆ B := by
    intro u huS
    obtain ⟨hud, hux⟩ := Finset.mem_filter.mp huS
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hud).1,
      localPacketCharge_pos_dist_le_two_min p bad packets hmin hux⟩
  have hscard := Finset.card_le_card hsub
  have htotal : (∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x) = 3 := by
    change 2 < ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x at hover
    omega
  have heq : S = B := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨htotal, ?_, ?_⟩
  · change B.card = 3
    omega
  intro w hwD hwnear
  have hwS : w ∈ S := heq ▸ (Finset.mem_filter.mpr ⟨hwD, hwnear⟩ : w ∈ B)
  obtain ⟨hwd, hwpositive⟩ := Finset.mem_filter.mp hwS
  change 0 < localPacketCharge p bad packets w x at hwpositive
  have hwunit := certified_family_charge_le_one_of_not_adj p bad height assignments w x
    (fun hwx => hno w hwx.symm hwD)
  change localPacketCharge p bad packets w x ≤ 1 at hwunit
  refine ⟨hwd, ?_⟩
  change localPacketCharge p bad packets w x = 1
  omega

/-- Three incoming units cannot all come from the exact-distance-two circle.
At least one positive source must use a short-distance branch. -/
theorem certified_family_deep_overload_has_nonexact_source {n h : ℕ} [NeZero h]
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
    (hover : 2 < ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x) :
    ∃ u, u ∈ chargeDonors p bad ∧
      0 < localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ∧
      dist (p u) (p x) ≠ 2 * pairDist p ij := by
  by_contra hnot
  push Not at hnot
  have hle := certified_family_deep_receiver_total_le_two_of_exact_distance
    p hp hn v hv hh hsupport hpos ij hmin i hgood hu x hclose hdeep bad height assignments
    (fun u hud hx => hnot u hud hx)
  omega

end Erdos957
