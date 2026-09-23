import DeepFiveCenterReduction
import DeepCenterPacking

/-! Completion of the deep degree-five receiver capacity.  A hypothetical
third incoming unit gives a third nearby diameter donor.  Its retained center
also has degree five.  Both shared-five endpoint pairs then lie in the same
three-element nearby-diameter set, so the pairs overlap.  Supported-triangle
uniqueness identifies the centers, forcing the third donor back into the
original pair, a contradiction. -/

namespace Erdos957

/-- Any positive indirect transfer from a degree-five retained center lands at
an actual nearest neighbor of that center.  Constructor cases of other center
degrees are impossible. -/
theorem CertifiedDonorRule.indirect_degree_five_receiver_adj_center
    {n : ℕ} {p : Fin n → Point} {u q x : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height)
    (hq : (nearestGraph p).degree q = 5)
    (hu : u ∈ diameterEndpoints p) (hqu : (nearestGraph p).Adj q u)
    (hx : 0 < rule.packet.weight x) (hnot : ¬ (nearestGraph p).Adj u x) :
    (nearestGraph p).Adj q x := by
  cases rule with
  | low choice =>
      have hlow := choice.central_degree
      omega
  | unique choice high =>
      exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available endpoint central =>
      let choice := selectedSharedFiveCenter p q available
      have hcharge : 0 < choice.charge u x := by
        simpa only [CertifiedDonorRule.sharedFive_weight] using hx
      rcases choice.diameter_neighbor_cases u hu hqu with hul | hur
      · subst u
        have hpos : 0 < choice.selection.first.weight x := by
          simpa [SharedFiveCenterChoice.charge, choice.base.ne] using hcharge
        have hxq : x ≠ q := by
          intro heq
          exact hnot (heq ▸ central.symm)
        by_cases hxr : x = choice.selection.first.right
        · exact hxr ▸ choice.selection.first_secondary.1
        · simp [LocalChargePacket.weight, choice.selection.first_central, hxq, hxr] at hpos
      · subst u
        have hpos : 0 < choice.selection.second.weight x := by
          simpa [SharedFiveCenterChoice.charge, choice.base.ne.symm] using hcharge
        have hxq : x ≠ q := by
          intro heq
          exact hnot (heq ▸ central.symm)
        by_cases hxr : x = choice.selection.second.right
        · exact hxr ▸ choice.selection.second_secondary.1
        · simp [LocalChargePacket.weight, choice.selection.second_central, hxq, hxr] at hpos
  | sharedSix choice =>
      have hsix := choice.center_degree
      omega
  | reflectedSharedSix choice =>
      have hsix := choice.original_neighbors.1
      omega

/-- Two retained shared-five triangles whose endpoint pairs overlap have the
same center.  No receiver or bottom choice is needed. -/
theorem sharedFive_centers_eq_of_endpoint_overlap {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {q q' : Fin n} (choice : SharedFiveCenterChoice p q)
    (other : SharedFiveCenterChoice p q')
    (hoverlap : choice.left = other.left ∨ choice.left = other.right ∨
      choice.right = other.left ∨ choice.right = other.right) : q = q' := by
  have htriangle (q₀ : Fin n) (ch : SharedFiveCenterChoice p q₀)
      (u : Fin n) (hu : u = ch.left ∨ u = ch.right) :
      ∃ w, u ∈ diameterEndpoints p ∧ w ∈ diameterEndpoints p ∧
        (nearestGraph p).Adj u w ∧ (nearestGraph p).Adj u q₀ ∧
        (nearestGraph p).Adj w q₀ ∧
        ((∀ k, 0 ≤ turn (p u) (p w) (p k)) ∨
          (∀ k, 0 ≤ turn (p w) (p u) (p k))) := by
    rcases hu with rfl | rfl
    · exact ⟨ch.right, ch.left_diameter, ch.right_diameter, ch.base,
        ch.center_left.symm, ch.center_right.symm, Or.inr ch.support⟩
    · exact ⟨ch.left, ch.right_diameter, ch.left_diameter, ch.base.symm,
        ch.center_right.symm, ch.center_left.symm, Or.inl ch.support⟩
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u, (u = choice.left ∨ u = choice.right) ∧
      (u = other.left ∨ u = other.right) := by
    rcases hoverlap with hll | hlr | hrl | hrr
    · exact ⟨choice.left, Or.inl rfl, Or.inl hll⟩
    · exact ⟨choice.left, Or.inl rfl, Or.inr hlr⟩
    · exact ⟨choice.right, Or.inr rfl, Or.inl hrl⟩
    · exact ⟨choice.right, Or.inr rfl, Or.inr hrr⟩
  obtain ⟨w₁, huD, hw₁, huw₁, huq₁, hwq₁, hs₁⟩ := htriangle q choice u hu₁
  obtain ⟨w₂, _huD, hw₂, huw₂, huq₂, hwq₂, hs₂⟩ := htriangle q' other u hu₂
  have hdeg₁ : 4 ≤ (nearestGraph p).degree q := by rw [choice.center_degree]; omega
  have hdeg₂ : 4 ≤ (nearestGraph p).degree q' := by rw [other.center_degree]; omega
  exact high_degree_supported_triangle_centers_eq_of_diameterEndpoint p hp hn
    huD hw₁ hw₂ huw₁ huw₂ huq₁ huq₂ hwq₁ hwq₂ hdeg₁ hdeg₂ hs₁ hs₂

/-- If two shared-five centers are both adjacent to one receiver and at most
three diameter endpoints lie within two minimum distances of that receiver,
their selected endpoint pairs overlap. -/
theorem sharedFive_endpoint_pairs_overlap_of_common_receiver
    {n : ℕ} (p : Fin n → Point)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    {q q' x : Fin n} (choice : SharedFiveCenterChoice p q)
    (other : SharedFiveCenterChoice p q')
    (hqx : (nearestGraph p).Adj q x) (hq'x : (nearestGraph p).Adj q' x)
    (hcard : ((diameterEndpoints p).filter (fun a =>
      dist (p a) (p x) ≤ 2 * pairDist p ij)).card ≤ 3) :
    choice.left = other.left ∨ choice.left = other.right ∨
      choice.right = other.left ∨ choice.right = other.right := by
  classical
  let B := (diameterEndpoints p).filter (fun a =>
    dist (p a) (p x) ≤ 2 * pairDist p ij)
  have hmem (q₀ : Fin n) (hqx₀ : (nearestGraph p).Adj q₀ x)
      (a : Fin n) (haD : a ∈ diameterEndpoints p)
      (hqa : (nearestGraph p).Adj q₀ a) : a ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨haD, ?_⟩
    have ht := dist_triangle (p a) (p q₀) (p x)
    rw [nearestGraph_adj_dist_eq p hmin hqa.symm,
      nearestGraph_adj_dist_eq p hmin hqx₀] at ht
    linarith
  have hal := hmem q hqx choice.left choice.left_diameter choice.center_left
  have har := hmem q hqx choice.right choice.right_diameter choice.center_right
  have hbl := hmem q' hq'x other.left other.left_diameter other.center_left
  have hbr := hmem q' hq'x other.right other.right_diameter other.center_right
  by_contra hnone
  simp only [not_or] at hnone
  obtain ⟨hll, hlr, hrl, hrr⟩ := hnone
  have hsub : ({choice.left, choice.right, other.left, other.right} :
      Finset (Fin n)) ⊆ B := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hfour : ({choice.left, choice.right, other.left, other.right} :
      Finset (Fin n)).card = 4 := by
    simp [choice.base.ne, other.base.ne, hll, hlr, hrl, hrr]
  have hle := Finset.card_le_card hsub
  change B.card ≤ 3 at hcard
  omega

/-- The complete assembled family has at most two doubled charge units at any
deep degree-five receiver. -/
theorem certified_family_deep_five_total_le_two
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤ 2 := by
  classical
  by_contra hnot
  have hover : 2 < ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x := by
    omega
  let bad := tightHullBadVertices p v
  let packets := certifiedFamilyPackets p bad height assignments
  obtain ⟨q, available, hbottom, _hl, _hr⟩ :=
    certified_family_deep_five_overload_has_sharedFive_pair p hp hn v hv hh hrange
      hsupport hpos ij hmin i hgood hu x hclose hdeep hdegree height assignments hover
  let choice := selectedSharedFiveCenter p q available
  have hsat := certified_family_deep_overload_saturates_nearby p hp hn v hv hh
    hsupport hpos ij hmin i hgood hu x hclose hdeep bad height assignments hover
  let B := (diameterEndpoints p).filter (fun a => dist (p a) (p x) ≤ 2 * pairDist p ij)
  have hBcard : B.card = 3 := by
    simpa only [B] using hsat.2.1
  have hnear (a : Fin n) (haD : a ∈ diameterEndpoints p)
      (hqa : (nearestGraph p).Adj q a) : a ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨haD, ?_⟩
    rw [hbottom]
    have ht := dist_triangle (p a) (p q) (p choice.selection.bottom)
    rw [nearestGraph_adj_dist_eq p hmin hqa.symm,
      nearestGraph_adj_dist_eq p hmin choice.selection.bottom_adj] at ht
    linarith
  have hlB : choice.left ∈ B := hnear choice.left choice.left_diameter choice.center_left
  have hrB : choice.right ∈ B := hnear choice.right choice.right_diameter choice.center_right
  have hpaircard : ({choice.left, choice.right} : Finset (Fin n)).card = 2 := by
    simp [choice.base.ne]
  have hlt : ({choice.left, choice.right} : Finset (Fin n)).card < B.card := by
    rw [hpaircard, hBcard]
    omega
  obtain ⟨w, hwB, hwNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hwne : w ≠ choice.left ∧ w ≠ choice.right := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hwNot
  obtain ⟨hwD, hwclose⟩ := Finset.mem_filter.mp hwB
  obtain ⟨hwd, hwone⟩ := hsat.2.2 w hwD hwclose
  have hwpos : 0 < localPacketCharge p bad packets w x := by
    change localPacketCharge p bad packets w x = 1 at hwone
    omega
  let aW := assignments w hwd
  have hxW : 0 < aW.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hwd, packets, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aW] using hwpos
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  have hnotW : ¬ (nearestGraph p).Adj w x := fun hwx => hno w hwx.symm hwD
  have hqfive := certified_family_deep_five_overload_active_center_degree_five
    p hp hn v hv hh hrange hsupport hpos ij hmin i hgood hu x hclose hdeep hdegree
      height assignments hover w hwd hwpos
  let otherAvailable := aW.rule.sharedFive_available_of_indirect hqfive x hxW hnotW
  let other := selectedSharedFiveCenter p aW.context.q otherAvailable
  have hq'x : (nearestGraph p).Adj aW.context.q x :=
    aW.rule.indirect_degree_five_receiver_adj_center hqfive aW.context.endpoint
      aW.context.central_adj.symm hxW hnotW
  have hqx : (nearestGraph p).Adj q x := by
    rw [hbottom]
    exact choice.selection.bottom_adj
  have hcard : ((diameterEndpoints p).filter (fun a =>
      dist (p a) (p x) ≤ 2 * pairDist p ij)).card ≤ 3 := by
    simpa only [B] using hBcard.le
  have hoverlap := sharedFive_endpoint_pairs_overlap_of_common_receiver
    p ij hmin choice other hqx hq'x hcard
  have hcenters : q = aW.context.q :=
    sharedFive_centers_eq_of_endpoint_overlap p hp hn choice other hoverlap
  have hwcase := choice.diameter_neighbor_cases w hwD (by
    rw [hcenters]
    exact aW.context.central_adj.symm)
  exact hwcase.elim hwne.1 hwne.2

/-- Degree-five form of the full deep receiver capacity, in the exact shape
needed by the global weighted assembly. -/
theorem certified_family_deep_five_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  rw [hdegree]
  norm_num
  exact certified_family_deep_five_total_le_two p hp hn v hv hh hrange hsupport hpos
    ij hmin i hgood hu x hclose hdeep hdegree height assignments


/-- Degree six has zero receiver slack, so every local packet vanishes there. -/
theorem certified_family_receiver_total_eq_zero_of_degree_six
    {n : ℕ} (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 6) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  simp only [localPacketCharge, dite_eq_left hu, certifiedFamilyPackets,
    CertifiedDonorAssignment.packet]
  have hle := (assignments u hu).packet.weight_le_degree_slack x
  rw [hdegree] at hle
  exact Nat.eq_zero_of_le_zero (by
    simpa only [CertifiedDonorAssignment.packet, Nat.sub_self] using hle)

/-- Full certified receiver capacity at every deep receiver, with no remaining
case split on its nearest-graph degree. -/
theorem certified_family_deep_receiver_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u)) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have hdeg6 : (nearestGraph p).degree x ≤ 6 :=
    nearestGraph_degree_le_six p (by omega) hp x
  by_cases hle4 : (nearestGraph p).degree x ≤ 4
  · exact certified_family_deep_receiver_capacity_of_degree_le_four p hp hn v hv hh
      hsupport hpos ij hmin i hgood hu x hclose hdeep
      (tightHullBadVertices p v) height assignments hle4
  · have hge5 : 5 ≤ (nearestGraph p).degree x := by omega
    by_cases h5 : (nearestGraph p).degree x = 5
    · exact certified_family_deep_five_capacity p hp hn v hv hh hrange hsupport hpos
        ij hmin i hgood hu x hclose hdeep h5 height assignments
    · have h6 : (nearestGraph p).degree x = 6 := by omega
      have hz := certified_family_receiver_total_eq_zero_of_degree_six p
        (tightHullBadVertices p v) height assignments x h6
      rw [hz, h6]

end Erdos957
