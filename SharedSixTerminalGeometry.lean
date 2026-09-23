import FarDeepReceiverExclusion
import SharedSixLowDegreeReduction
import BlockedNeighborRouting

namespace Erdos957

/-- The extended deep strip excludes every diameter neighbor, including
points up to three minimum lengths away from the anchor. -/
theorem SharedSixPacketChoice.deep_strip_no_diameter_neighbor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (a : Fin n) (c : ℝ) (hc : -1 ≤ c ∧ c ≤ 3)
    (hcoord : edgeCoordinate (p partner) (p (v i)) (p a) =
      (c : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I) :
    ∀ z, (nearestGraph p).Adj a z → z ∉ diameterEndpoints p := by
  have hpartner := choice.partner_eq_successor p hp hn v hv hh hrange hsupport i ctx partner
  have hne := hp.ne choice.base.symm.ne
  let M := edgeCoordinate (p (v i)) (p partner)
  have hM : M (p a) = (1 - c : ℝ) + ((2 * choice.height : ℝ) : ℂ) * Complex.I := by
    dsimp [M]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne choice.base.ne), hcoord]
    push_cast
    ring
  have hparts : (M (p a)).re = 1 - c ∧ (M (p a)).im = 2 * choice.height := by
    rw [hM]
    simp
  have hre : |(M (p a)).re| ≤ 2 := by
    rw [hparts.1]
    exact abs_le.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hnorm : ‖M (p a)‖ ≤ 3 := by
    have hsq := Complex.normSq_eq_norm_sq (M (p a))
    rw [Complex.normSq_apply, hparts.1, hparts.2] at hsq
    have hr : (1 - c) ^ 2 ≤ 4 := by
      have ht := (sq_le_sq₀ (abs_nonneg (1-c)) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        (by simpa only [hparts.1] using hre)
      nlinarith [sq_abs (1-c)]
    nlinarith [choice.height_sq, norm_nonneg (M (p a))]
  have hδ := pairDist_pos p hp ctx.minPair_spec.1
  have hL := nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base.symm
  have hclose : dist (p (v i)) (p a) ≤ 3 * pairDist p ctx.minPair := by
    dsimp [M] at hnorm
    rw [edgeCoordinate_norm _ _ _ hne, hL] at hnorm
    exact (div_le_iff₀ hδ).mp hnorm
  apply tight_flat_far_deep_receiver_no_diameter_neighbor p hp hn v hv hh
    hsupport hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint a hclose
  · rw [← hpartner, hL, div_self hδ.ne']
    simpa only [mul_one, M] using hre
  · rw [← hpartner, hL, div_self hδ.ne', mul_one]
    change (3 / 2 : ℝ) ≤ (M (p a)).im
    rw [hparts.2]
    nlinarith [choice.height_pos, choice.height_sq]

/-- A terminal shared-six site forces two distinct unusable route vertices.
One has degree six; the other has no diameter neighbors at all. -/
theorem SharedSixPacketChoice.terminal_blocked_neighbors
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (t₂ : Fin n) (hdeg : (nearestGraph p).degree t₂ = 6)
    (houter : (nearestGraph p).Adj choice.outer t₂)
    (hadj : (nearestGraph p).Adj t₂ choice.packet.right)
    (hcoord₂ : edgeCoordinate (p partner) (p (v i)) (p t₂) =
      (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)
    (hcoordx : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
      (5 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) :
    ∃ z, t₂ ≠ z ∧ (nearestGraph p).Adj choice.packet.right t₂ ∧
      (nearestGraph p).Adj choice.packet.right z ∧
      t₂ ∉ diameterEndpoints p ∧ z ∉ diameterEndpoints p ∧
      ∀ a, (nearestGraph p).Adj z a → a ∉ diameterEndpoints p := by
  have hbx : (nearestGraph p).Adj choice.outer choice.packet.right := by
    simpa only [choice.packet_left] using choice.sites_adjacent
  obtain ⟨z, _, ht₂z, hxz, hsum⟩ := degree_six_triangle_completion
    p (by omega) hp hdeg hadj houter.symm hbx.symm
  have hcoordz : edgeCoordinate (p partner) (p (v i)) (p z) =
      (3 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p partner) (p (v i))
      (p choice.outer) (p z) (p t₂) (p choice.packet.right) hsum
    rw [choice.outer_coordinate, hcoord₂, hcoordx] at hs
    linear_combination hs
  have hno₂ := choice.deep_strip_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    i ctx partner hrange t₂ 2 (by norm_num) (by simpa using hcoord₂)
  have hnoz := choice.deep_strip_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    i ctx partner hrange z 3 (by norm_num) (by simpa using hcoordz)
  have ht₂D : t₂ ∉ diameterEndpoints p := by
    intro hd
    have ht := nearestGraph_degree_le_three_of_diameterEndpoint p (by omega) hp t₂ hd
    omega
  exact ⟨z, ht₂z.ne, hadj.symm, hxz, ht₂D, hno₂ z ht₂z, hnoz⟩

end Erdos957



