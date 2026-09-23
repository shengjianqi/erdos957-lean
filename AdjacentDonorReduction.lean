import ShortDiameterChord
import DonorNearestShared
import SupportedSharedCharge

/-! Every unresolved large-configuration donor shares a nearest triangle
along an actual hull edge. Remote cyclic positions are excluded uniformly. -/

namespace Erdos957

/-- Large cardinality supplies the scale needed to support every nearest
edge whose two endpoints are diameter endpoints. -/
theorem nearest_diameter_chord_support_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {u w : Fin n} (hu : u ∈ diameterEndpoints p)
    (hw : w ∈ diameterEndpoints p) (huw : (nearestGraph p).Adj u w) :
    (∀ k, 0 ≤ turn (p u) (p w) (p k)) ∨
      (∀ k, 0 ≤ turn (p w) (p u) (p k)) := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  apply short_diameter_chord_support p hp hmax hu hw huw
  have hten := ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  have hr := pairDist_pos p hp hmin.1
  rw [nearestGraph_adj_dist_eq p hmin huw]
  linarith

/-- Such an edge joins consecutive vertices of any actual oriented hull
cycle. No flatness, central-neighbor, or degree premise is needed. -/
theorem nearest_diameter_endpoints_cyclic_adjacent_of_large_card
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n)
    (hu : v i ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (huw : (nearestGraph p).Adj (v i) w) :
    w = v (i + 1) ∨ w = v (i - 1) := by
  exact supporting_hull_chord_cyclic_adjacent p hp v hv hh hrange hsupport i w
    (diameterEndpoints_subset_hullVertexIndices p hp hw) huw.ne.symm
    (nearest_diameter_chord_support_of_large_card p hp hn hu hw huw)

/-- The complete donor reduction now retains only actual adjacent shared
triangles. In particular there is no unclassified remote hull witness. -/
theorem donor_packet_or_adjacent_shared_of_large_card
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (bad : Finset (Fin n)) (i : Fin h) (hu : v i ∈ chargeDonors p bad) :
    ∃ ctx : DonorContext p bad (v i),
      Nonempty (LocalChargePacket p (v i)) ∨
        (((nearestGraph p).degree ctx.q = 5 ∨
            (nearestGraph p).degree ctx.q = 6) ∧
          ∃ w : Fin n, w ∈ diameterEndpoints p ∧
            (nearestGraph p).Adj (v i) w ∧ (nearestGraph p).Adj ctx.q w ∧
            (w = v (i + 1) ∨ w = v (i - 1))) := by
  obtain ⟨ctx, hpacket | ⟨hdegree, w, hwD, huw, hqw⟩⟩ :=
    donor_packet_or_nearest_shared_of_large_card p hp hn bad (v i) hu
  · exact ⟨ctx, Or.inl hpacket⟩
  · refine ⟨ctx, Or.inr ⟨hdegree, w, hwD, huw, hqw, ?_⟩⟩
    exact nearest_diameter_endpoints_cyclic_adjacent_of_large_card
      p hp hn v hv hh hrange hsupport i w ctx.endpoint hwD huw

/-- On the tight-flat donor set, the verified forward shared-six packet
discharges that orientation. What remains is shared-five (either side), or
shared-six on the predecessor side. This is still a local reduction and
does not claim a global charge-capacity bound. -/
theorem tight_flat_donor_packet_or_five_or_backward_six
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v)) :
    ∃ ctx : DonorContext p (tightHullBadVertices p v) (v i),
      Nonempty (LocalChargePacket p (v i)) ∨
        ∃ w : Fin n, w ∈ diameterEndpoints p ∧
          (nearestGraph p).Adj (v i) w ∧ (nearestGraph p).Adj ctx.q w ∧
          (((nearestGraph p).degree ctx.q = 5 ∧
              (w = v (i + 1) ∨ w = v (i - 1))) ∨
            ((nearestGraph p).degree ctx.q = 6 ∧ w = v (i - 1))) := by
  obtain ⟨ctx, hpacket | ⟨hdegree, w, hwD, huw, hqw, hwhere⟩⟩ :=
    donor_packet_or_adjacent_shared_of_large_card p hp hn v hv hh hrange
      hsupport (tightHullBadVertices p v) i hu
  · exact ⟨ctx, Or.inl hpacket⟩
  · rcases hdegree with hfive | hsix
    · exact ⟨ctx, Or.inr ⟨w, hwD, huw, hqw, Or.inl ⟨hfive, hwhere⟩⟩⟩
    · rcases hwhere with hnext | hprev
      · have hchord : ∀ k, 0 ≤ turn (p (v i)) (p w) (p k) := by
          rw [hnext]
          exact hsupport i
        exact ⟨ctx, Or.inl ⟨localChargePacket_of_supported_shared_six_of_large_card
          p hp hn v hv hh hrange hsupport hpos i ctx.q w huw hqw
          ctx.central_adj.symm hsix ctx.outside_bad hwD hchord⟩⟩
      · exact ⟨ctx, Or.inr ⟨w, hwD, huw, hqw, Or.inr ⟨hsix, hprev⟩⟩⟩

end Erdos957
