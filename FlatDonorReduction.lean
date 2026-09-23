import DonorNearestShared
import TightFlatChord

/-! An unresolved tight-flat donor has a genuine nearest shared triangle,
whose other diameter endpoint is not two or three local hull steps away. -/

namespace Erdos957

/-- A total donor reduction using the actual hull enumeration. The witness
index is neither the donor itself nor any two-step or three-step hull position.
This does not yet exclude remote cyclic positions. -/
theorem tight_flat_donor_packet_or_shared_hull_witness {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v)) :
    ∃ ctx : DonorContext p (tightHullBadVertices p v) (v i),
      Nonempty (LocalChargePacket p (v i)) ∨
        (((nearestGraph p).degree ctx.q = 5 ∨
            (nearestGraph p).degree ctx.q = 6) ∧
          ∃ k : Fin h, v k ∈ diameterEndpoints p ∧
            (nearestGraph p).Adj (v i) (v k) ∧
            (nearestGraph p).Adj ctx.q (v k) ∧
            k ≠ i ∧ k ≠ (i + 1) + 1 ∧ k ≠ (i - 1) - 1 ∧
            k ≠ ((i + 1) + 1) + 1 ∧ k ≠ ((i - 1) - 1) - 1) := by
  obtain ⟨ctx, hpacket | ⟨hdegree, w, hwD, huw, hqw⟩⟩ :=
    donor_packet_or_nearest_shared_of_large_card p hp hn
      (tightHullBadVertices p v) (v i) hu
  · exact ⟨ctx, Or.inl hpacket⟩
  · have hwhull := diameterEndpoints_subset_hullVertexIndices p hp hwD
    have hwrange : w ∈ Set.range v := by rw [hrange]; exact hwhull
    obtain ⟨k, rfl⟩ := hwrange
    have hnot2 := tight_flat_two_step_not_nearest p hp v hv hh
      ctx.minPair ctx.minPair_spec i hpos ctx.outside_bad (v k)
    have hnot3 := tight_flat_three_step_no_common_nearest p hp v hv hh
      ctx.minPair ctx.minPair_spec i hpos ctx.outside_bad (v k)
    refine ⟨ctx, Or.inr ⟨hdegree, k, hwD, huw, hqw, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro heq
      exact huw.ne (congrArg v heq.symm)
    · intro heq
      exact hnot2 (Or.inl (congrArg v heq)) huw
    · intro heq
      exact hnot2 (Or.inr (congrArg v heq)) huw
    · intro heq
      exact hnot3 (Or.inl (congrArg v heq)) ⟨ctx.q, ctx.central_adj, hqw⟩
    · intro heq
      exact hnot3 (Or.inr (congrArg v heq)) ⟨ctx.q, ctx.central_adj, hqw⟩

end Erdos957
