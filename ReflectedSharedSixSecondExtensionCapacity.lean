import SharedSixSecondExtensionCapacity
import ReflectedSharedSixLowerCapacity

/-! Reflection transports the forward second-extension exclusion and therefore
also the full incoming capacity theorem.  In the reflected frame the left
endpoint needed by the forward obstruction is the original shared-five right
endpoint, which is available in every saturated shared-five pair produced by
the deep degree-five overload reduction. -/

namespace Erdos957

/-- A reflected shared-six degree-five second extension cannot be the selected
bottom of a retained shared-five pair when the shared-five right endpoint is
an actual donor.  This is the reflected transport of the complete forward
`t₂` obstruction, including the third-neighbor argument. -/
theorem tight_flat_reflectedSharedSix_second_extension_ne_sharedFive_bottom_of_right_donor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n)
    (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.reflected.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hrightDonor : five.right ∈ chargeDonors p (tightHullBadVertices p v)) :
    five.selection.bottom ≠ choice.packet.right := by
  classical
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdegreeMap := nearestGraph_degree_eq_of_dist_eq p pR hdist
  have hvR := reversedHullCycle_injective v hv
  have hrangeR : Set.range (reversedHullCycle v) =
      (hullVertexIndices pR : Set (Fin n)) := reflectedHull_range p v hrange
  have hsupportR : ∀ a k, 0 ≤ turn (pR (reversedHullCycle v a))
      (pR (reversedHullCycle v (a + 1))) (pR k) := reflectedHull_support p v hsupport
  have hposR : ∀ a, 0 < hullExteriorAngle pR (reversedHullCycle v) a := by
    intro a
    simpa only [pR, hullExteriorAngle_planeReflection_reversed] using hpos (-a)

  have hgoodR : v i ∉ tightHullBadVertices pR (reversedHullCycle v) := by
    have ht := tightHull_not_bad_planeReflection_reversed p v hv (-i)
      (by simpa only [neg_neg] using ctx.outside_bad)
    simpa only [reversedHullCycle_neg] using ht
  have hdonorR : v i ∈ chargeDonors pR
      (tightHullBadVertices pR (reversedHullCycle v)) := by
    simp only [chargeDonors, Finset.mem_filter]
    exact ⟨by simpa only [hD] using ctx.endpoint,
      hgoodR, (hdegreeMap (v i)).trans ctx.degree_three⟩
  let ctxR := donorContext_of_large_card pR hpR hn
    (tightHullBadVertices pR (reversedHullCycle v)) (v i) hdonorR

  have hpartnerD : partner ∈ diameterEndpoints p := by
    simpa only [pR, hD] using choice.reflected.partner_diameter
  have hqpartner := choice.center_adj_partner (by omega : 2 ≤ n) hp
  have hbase : (nearestGraph p).Adj partner (v i) := by
    simpa only [pR, hG] using choice.reflected.base
  have hwhere := (tight_flat_shared_central_neighbor_nearest p hp hn v hv hh
    hsupport hpos i ctx partner hpartnerD hqpartner hbase.ne).2
  have hctxq : ctxR.q = ctx.q := by
    apply (supported_nearest_triangle_center_eq pR (by omega) hpR ctxR
      (by simpa only [hG] using hbase.symm)
      (by simpa only [hG] using ctx.central_adj)
      (by simpa only [hG] using hqpartner.symm) ?_).symm
    rcases hwhere with hnext | hprev
    · right
      intro k
      dsimp [pR]
      rw [turn_planeReflection, turn_reverse, neg_neg, hnext]
      exact hsupport i k
    · left
      intro k
      dsimp [pR]
      rw [turn_planeReflection, turn_reverse, neg_neg, hprev]
      simpa only [sub_add_cancel] using hsupport (i - 1) k

  have hrightD : five.right ∈ diameterEndpoints p :=
    (Finset.mem_filter.mp hrightDonor).1
  have hrightGood : five.right ∉ tightHullBadVertices p v :=
    (Finset.mem_filter.mp hrightDonor).2.1
  have hrightDegree : (nearestGraph p).degree five.right = 3 :=
    (Finset.mem_filter.mp hrightDonor).2.2
  have hrightHull : five.right ∈ hullVertexIndices p :=
    diameterEndpoints_subset_hullVertexIndices p hp hrightD
  have hrightRange : five.right ∈ Set.range v := by
    rw [hrange]
    exact hrightHull
  obtain ⟨j, hj⟩ := hrightRange
  have hrightGoodR : five.right ∉
      tightHullBadVertices pR (reversedHullCycle v) := by
    have ht := tightHull_not_bad_planeReflection_reversed p v hv (-j) (by
      simpa only [neg_neg, hj] using hrightGood)
    simpa only [reversedHullCycle_neg, hj] using ht
  have hrightDonorR : five.right ∈ chargeDonors pR
      (tightHullBadVertices pR (reversedHullCycle v)) := by
    simp only [chargeDonors, Finset.mem_filter]
    exact ⟨by simpa only [hD] using hrightD,
      hrightGoodR, (hdegreeMap five.right).trans hrightDegree⟩
  have hleftDonorR : (five.reflection_swap hp).left ∈ chargeDonors pR
      (tightHullBadVertices pR (reversedHullCycle v)) := by
    change five.right ∈ chargeDonors pR
      (tightHullBadVertices pR (reversedHullCycle v))
    exact hrightDonorR

  have hdegreeR : (nearestGraph pR).degree choice.reflected.packet.right = 5 := by
    rw [← choice.packet_sites.2]
    exact (hdegreeMap choice.packet.right).trans hdegree
  have hnotLowerR : choice.reflected.packet.right ≠ choice.reflected.lower := by
    simpa only [choice.packet_sites.2] using hnot_lower

  have hexclude :=
    tight_flat_sharedSix_second_extension_ne_sharedFive_bottom_of_left_donor
      pR hpR hn (reversedHullCycle v) hvR hh hrangeR hsupportR hposR (-i)
  rw [show reversedHullCycle v (-i) = v i by exact reversedHullCycle_neg v i] at hexclude
  specialize hexclude ctxR
  rw [hctxq] at hexclude
  have ht := hexclude partner qfive choice.reflected hdegreeR hnotLowerR
    (five.reflection_swap hp) hleftDonorR
  simpa only [SharedFiveCenterChoice.reflection_swap_bottom, choice.packet_sites.2] using ht

/-- Full simultaneous incoming capacity at the reflected shared-six second
extension.  The degree-five case is discharged by the reflected mixed
shared-five exclusion above; degree five is already part of the branch data
here, so the right-hand side is exactly two doubled half-charges. -/
theorem certified_family_reflectedSharedSix_second_extension_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n)
    (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.reflected.lower)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
        u choice.packet.right ≤
      2 * (6 - (nearestGraph p).degree choice.packet.right) := by
  have hG := nearestGraph_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hD := diameterEndpoints_eq_of_dist_eq p (fun k => planeReflection (p k))
    (fun a b => planeReflection.dist_map (p a) (p b))
  have hbase : (nearestGraph p).Adj partner (v i) := by
    simpa only [hG] using choice.reflected.base
  have hpartnerD : partner ∈ diameterEndpoints p := by
    simpa only [hD] using choice.reflected.partner_diameter
  have hpositive : 0 < choice.packet.weight choice.packet.right := by
    rw [choice.site_weights.2]
    omega
  have hclose := choice.packet.positive_dist_le_two_min ctx.minPair_spec hpositive
  obtain ⟨t₂, hright, _, _, _, _, ht₂coord, _⟩ :=
    choice.degree_five_right_second_extension_data hdegree hnot_lower
  have hrightCoord :
      edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
        (2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I := by
    rw [hright]
    exact ht₂coord
  have hbaseDepth : (5 / 3 : ℝ) ≤
      |(edgeCoordinate (p (v i)) (p partner) (p choice.packet.right)).im| := by
    have hhgt : (5 / 3 : ℝ) ≤ 2 * choice.reflected.height := by
      nlinarith [choice.reflected.height_pos, choice.reflected.height_sq]
    rw [edgeCoordinate_swap_base _ _ _ (hp.ne hbase.ne), hrightCoord]
    simpa [abs_of_pos choice.reflected.height_pos] using hhgt
  have hdeep := tight_flat_deep_base_receiver_depth p hp hn v hv hh hsupport hpos
    ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint partner
    hpartnerD hbase.symm choice.packet.right hclose hbaseDepth
  have hle := certified_family_deep_five_capacity_of_no_sharedFive_pair
    p hp hn v hv hh hrange hsupport hpos ctx.minPair ctx.minPair_spec i
    ctx.outside_bad ctx.endpoint choice.packet.right hclose hdeep hdegree height
    assignments (by
      intro q available _hleft hright
      exact (tight_flat_reflectedSharedSix_second_extension_ne_sharedFive_bottom_of_right_donor
        p hp hn v hv hh hrange hsupport hpos i ctx partner q choice hdegree
        hnot_lower (selectedSharedFiveCenter p q available) hright).symm)
  simpa only [hdegree] using hle

end Erdos957
