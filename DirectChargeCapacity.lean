import DirectChargeAccounting
import FlatUnitCircleSources
import WeightedChargeAssembly

/-! Simultaneous capacity for all transfers along actual nearest edges. The
complementary indirect transfers remain explicit in the exact total. -/

namespace Erdos957

/-- At most two eligible donors are nearest neighbors of any receiver in
the actual tight-flat hull, whether or not their packets use that receiver. -/
theorem tight_flat_direct_sources_card_le_two {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i) (x : Fin n) :
    (directChargeSources p (tightHullBadVertices p v) x).card ≤ 2 := by
  classical
  by_cases hex : (directChargeSources p (tightHullBadVertices p v) x).Nonempty
  · obtain ⟨u, hu⟩ := hex
    obtain ⟨hudonor, hux⟩ := Finset.mem_filter.mp hu
    obtain ⟨huD, hugood, _hudegree⟩ := Finset.mem_filter.mp hudonor
    have hurange : u ∈ Set.range v := by
      rw [hrange]
      exact diameterEndpoints_subset_hullVertexIndices p hp huD
    obtain ⟨i, rfl⟩ := hurange
    have hDcard := tight_flat_diameter_neighbors_card_le_two p hp hn v hv hh
      hsupport hpos i hugood huD x hux
    apply le_trans (Finset.card_le_card ?_) hDcard
    intro w hw
    obtain ⟨hwdonor, hwx⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hwdonor).1, hwx.symm⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hex]
    simp

/-- Every simultaneous direct contribution is included. The arbitrary
packets may also have indirect transfers; those are not bounded here. -/
theorem tight_flat_direct_charge_le_capacity {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (packets : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) → LocalChargePacket p u)
    (x : Fin n) :
    directPacketChargeTotal p (tightHullBadVertices p v) packets x ≤
      2 * (6 - (nearestGraph p).degree x) :=
  directPacketChargeTotal_le_capacity_of_card p (tightHullBadVertices p v) packets x
    (tight_flat_direct_sources_card_le_two p hp hn v hv hh hrange hsupport hpos x)

/-- For the actual hull the full remaining capacity obligation is precisely
the indirect incoming weight versus capacity left after direct contributions. -/
theorem tight_flat_total_capacity_iff_indirect {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (packets : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) → LocalChargePacket p u)
    (x : Fin n) :
    (∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v) packets u x ≤
        2 * (6 - (nearestGraph p).degree x)) ↔
    indirectPacketChargeTotal p (tightHullBadVertices p v) packets x ≤
      2 * (6 - (nearestGraph p).degree x) -
        directPacketChargeTotal p (tightHullBadVertices p v) packets x :=
  total_capacity_iff_indirect_le_remaining p (tightHullBadVertices p v) packets x
    (tight_flat_direct_charge_le_capacity p hp hn v hv hh hrange hsupport hpos packets x)

end Erdos957
