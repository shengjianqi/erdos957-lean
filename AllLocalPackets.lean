import BackwardSharedSix
import BackwardSharedFive
import CollinearBound

/-! Complete local packet existence for all configurations, outside a
uniformly bounded exceptional set. Global capacity is not asserted. -/

namespace Erdos957

/-- Every tight-flat donor in a sufficiently large configuration has a
checked local packet; both shared-five and shared-six orientations are covered. -/
theorem tight_flat_donor_has_local_packet {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v)) :
    Nonempty (LocalChargePacket p (v i)) := by
  obtain ⟨ctx, hpacket | ⟨hfive, w, hwD, huw, hqw, hwhere⟩⟩ :=
    tight_flat_donor_packet_or_shared_five p hp hn v hv hh hrange hsupport hpos i hu
  · exact hpacket
  · rcases hwhere with rfl | rfl
    · exact ⟨localChargePacket_of_forward_shared_five_of_large_card
        p hp hn v hv hh hrange hsupport hpos i ctx.q huw hqw
        ctx.central_adj.symm hfive ctx.outside_bad hwD ctx.endpoint⟩
    · exact ⟨localChargePacket_of_backward_shared_five_of_large_card
        p hp hn v hv hh hrange hsupport hpos i ctx.q huw hqw
        ctx.central_adj.symm hfive ctx.outside_bad hwD ctx.endpoint⟩

/-- One actual local packet can now be selected for each donor. The choice
has no proved simultaneous weighted-capacity guarantee. -/
noncomputable def localChargePackets_of_tight_flat_hull
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (u : Fin n) (hu : u ∈ chargeDonors p (tightHullBadVertices p v)) :
    LocalChargePacket p u := by
  apply Classical.choice
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hu).1
  have huhull := diameterEndpoints_subset_hullVertexIndices p hp huD
  have hurange : u ∈ Set.range v := by rw [hrange]; exact huhull
  obtain ⟨i, rfl⟩ := hurange
  exact tight_flat_donor_has_local_packet p hp hn v hv hh hrange hsupport hpos i hu

/-- A bounded exceptional set and local packets exist for every large
noncollinear configuration, using the actual convex-hull enumeration. -/
theorem exists_local_packets_of_large_noncollinear {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    ∃ bad : Finset (Fin n), bad.card ≤ 25200 ∧
      Nonempty (∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u) := by
  have hh := hullVertexCount_ge_three_of_noncollinear p hnot
  let : NeZero (hullVertexCount p) := ⟨by omega⟩
  obtain ⟨v, hv, hrange, hsupport, hpos, _hsum, hcard, _hsub, _hgood⟩ :=
    exists_tight_hull_bad_vertices_of_noncollinear p (by omega) hp hnot
  exact ⟨tightHullBadVertices p v, hcard,
    ⟨localChargePackets_of_tight_flat_hull p hp hn v hv hh hrange
      hsupport (fun i => (hpos i).1)⟩⟩

/-- All sizes and degenerate configurations have a uniformly bounded
exceptional set outside which every donor has a local packet. Small sets and
collinear sets put all diameter endpoints in the exceptional set. This local
existence result still requires a separate global capacity proof. -/
theorem exists_uniform_local_packets {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) :
    ∃ bad : Finset (Fin n), bad.card ≤ 25200 ∧
      Nonempty (∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u) := by
  have hall : Nonempty (∀ u, u ∈ chargeDonors p (diameterEndpoints p) →
      LocalChargePacket p u) := by
    refine ⟨fun u hu => False.elim ?_⟩
    obtain ⟨huD, hunot, _⟩ := Finset.mem_filter.mp hu
    exact hunot huD
  by_cases hsmall : n ≤ 1681
  · refine ⟨diameterEndpoints p, ?_, hall⟩
    have hc := diameterEndpointCount_le p
    change (diameterEndpoints p).card ≤ n at hc
    omega
  by_cases hcol : Collinear ℝ (Set.range p)
  · refine ⟨diameterEndpoints p, ?_, hall⟩
    have hc := diameterEndpointCount_le_two_of_collinear p hp hcol
    change (diameterEndpoints p).card ≤ 2 at hc
    omega
  exact exists_local_packets_of_large_noncollinear p hp (by omega) hcol

end Erdos957
