import SharedHexagonBound
import SharedHexagonCoordinates
import SharedOuterDegree
import NormalizedReceiverInterior
import LocalCharge
import InteriorExclusion

/-! A complete local charge packet for the right donor of a supported shared
six-neighbor edge, given a shallow span in the actual convex hull. -/

namespace Erdos957

noncomputable def localChargePacket_of_shared_six_hull_span {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v j : Fin n}
    (hvu : (nearestGraph p).Adj v u)
    (hvw : (nearestGraph p).Adj v w)
    (huw : (nearestGraph p).Adj u w)
    (hvdeg : (nearestGraph p).degree v = 6)
    (hw : w ∈ hullVertexIndices p)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) : LocalChargePacket p w :=
  Classical.choice (by
    obtain ⟨b, t, hvb, hwb, _hvt, hbt, _htw, hbsum, htsum, hcases⟩ :=
      degree_six_shared_edge_low_degree_extension p hn hp hvu hvw huw hvdeg hw hsupport
    obtain ⟨h, hh, hhsq, hMv, hMb, hMt⟩ :=
      shared_hexagon_base_coordinates p hn hp hvu hvw huw hsupport hbsum htsum
    obtain ⟨hbreg, htreg, ht₂reg, hdreg⟩ := hexagon_receiver_sites_in_region h hh hhsq
    have hout (k : Fin n)
        (hk : sharedReceiverRegion (edgeCoordinate (p u) (p w) (p k))) :
        k ∉ diameterEndpoints p :=
      interior_not_diameterEndpoints p hp k
        (span.receiver_mem_interior p (hp.ne huw.ne) hdiam hscale
          (hsupport j) (p k) hk)
    have hbout : b ∉ diameterEndpoints p := hout b (hMb.symm ▸ hbreg)
    have hbdeg : (nearestGraph p).degree b ≤ 5 :=
      shared_outer_neighbor_degree_le_five p hn hp hvw hvb hwb hbsum hw huw.ne.symm
    have packet (k : Fin n) (hbk : (nearestGraph p).Adj b k)
        (hkout : k ∉ diameterEndpoints p) (hkdeg : (nearestGraph p).degree k ≤ 5) :
        Nonempty (LocalChargePacket p w) := by
      exact ⟨{
        left := b
        right := k
        left_outside := hbout
        right_outside := hkout
        left_degree := hbdeg
        right_degree := hkdeg
        repeated_degree := fun heq => False.elim (hbk.ne heq)
        left_reachable := Or.inl hwb
        right_reachable := Or.inr ⟨b, hwb, hbk⟩
      }⟩
    rcases hcases with htlow | ⟨t₂, _htt₂, hbt₂, ht₂sum, hcases₂⟩
    · exact packet t hbt (hout t (hMt.symm ▸ htreg)) htlow
    have hMt₂ := shared_hexagon_t2_coordinate p h hMv hMb hMt ht₂sum
    rcases hcases₂ with ht₂low | ⟨d, _ht₂d, hbd, hdeq, hddeg⟩
    · exact packet t₂ hbt₂ (hout t₂ (hMt₂.symm ▸ ht₂reg)) ht₂low
    have hMd := shared_hexagon_d_coordinate p h hMv hMb hdeq
    exact packet d hbd (hout d (hMd.symm ▸ hdreg)) (by omega))

end Erdos957
