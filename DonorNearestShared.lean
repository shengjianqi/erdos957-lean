import DonorCases

/-! A donor needing further analysis shares an actual nearest-distance
triangle with another diameter endpoint. -/

namespace Erdos957

/-- The degree-five and degree-six common-neighbor theorems reduce every
unresolved donor to an actual nearest-distance triangle `u-q-w`, where `w`
is another diameter endpoint. -/
theorem donorContext_packet_or_nearest_shared {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u : Fin n}
    (ctx : DonorContext p bad u) :
    Nonempty (LocalChargePacket p u) ∨
      (((nearestGraph p).degree ctx.q = 5 ∨
          (nearestGraph p).degree ctx.q = 6) ∧
        ∃ w : Fin n, w ∈ diameterEndpoints p ∧
          (nearestGraph p).Adj u w ∧
          (nearestGraph p).Adj ctx.q w) := by
  classical
  have hscale : 2 * pairDist p ctx.minPair < dist (p u) (p ctx.j) := by
    have hr := pairDist_pos p hp ctx.minPair_spec.1
    nlinarith [ctx.long_diameter]
  by_cases hlow : (nearestGraph p).degree ctx.q ≤ 4
  · left
    exact ⟨localChargePacket_of_central_low_degree p hn hp
      ctx.diameter_adj ctx.degree_three ctx.minPair ctx.minPair_spec
      hscale ctx.central_adj ctx.central_lo ctx.central_hi hlow⟩
  by_cases hfive : (nearestGraph p).degree ctx.q = 5
  · obtain ⟨a, hua, hqa⟩ :=
      degree_five_central_neighbor_has_common_neighbor p hn hp
        ctx.diameter_adj ctx.degree_three ctx.central_adj
        ctx.central_lo ctx.central_hi hfive
    have hadeg : (nearestGraph p).degree a ≤ 5 :=
      common_neighbor_degree_le_five_of_central p hn hp
        ctx.diameter_adj ctx.central_adj ctx.central_lo ctx.central_hi hua hqa
    by_cases haD : a ∈ diameterEndpoints p
    · right
      exact ⟨Or.inl hfive, a, haD, hua, hqa⟩
    · left
      refine ⟨{
        left := ctx.q
        right := a
        left_outside := ctx.central_outside
        right_outside := haD
        left_degree := by omega
        right_degree := hadeg
        repeated_degree := ?_
        left_reachable := Or.inl ctx.central_adj
        right_reachable := Or.inl hua
      }⟩
      intro h
      exact False.elim (hqa.ne h)
  have hsix : (nearestGraph p).degree ctx.q = 6 := by
    have hle := ctx.central_degree_le_six
    omega
  obtain ⟨a, b, hab, hua, hqa, hadeg, hub, hqb, hbdeg⟩ :=
    diameterEndpoint_six_neighbor_common_degree_bounds p hn hp
      ctx.endpoint ctx.central_adj hsix
  by_cases haD : a ∈ diameterEndpoints p
  · right
    exact ⟨Or.inr hsix, a, haD, hua, hqa⟩
  by_cases hbD : b ∈ diameterEndpoints p
  · right
    exact ⟨Or.inr hsix, b, hbD, hub, hqb⟩
  · left
    refine ⟨{
      left := a
      right := b
      left_outside := haD
      right_outside := hbD
      left_degree := hadeg
      right_degree := hbdeg
      repeated_degree := ?_
      left_reachable := Or.inl hua
      right_reachable := Or.inl hub
    }⟩
    intro h
    exact False.elim (hab h)

/-- Every large-configuration donor has a real local packet or a second
diameter endpoint that forms a nearest-distance triangle with it and its
central neighbor. No hull adjacency or flatness is assumed. -/
theorem donor_packet_or_nearest_shared_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    (hlarge : 1681 < n) (bad : Finset (Fin n))
    (u : Fin n) (hu : u ∈ chargeDonors p bad) :
    ∃ ctx : DonorContext p bad u,
      Nonempty (LocalChargePacket p u) ∨
        (((nearestGraph p).degree ctx.q = 5 ∨
            (nearestGraph p).degree ctx.q = 6) ∧
          ∃ w : Fin n, w ∈ diameterEndpoints p ∧
            (nearestGraph p).Adj u w ∧
            (nearestGraph p).Adj ctx.q w) := by
  let ctx := donorContext_of_large_card p hp hlarge bad u hu
  exact ⟨ctx, donorContext_packet_or_nearest_shared p (by omega) hp ctx⟩

end Erdos957
