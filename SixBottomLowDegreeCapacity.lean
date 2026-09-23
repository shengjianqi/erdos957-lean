import NeighborRoutingCapacity

/-! Complete low-degree receiver capacity whenever an actual six-bottom
source occurs, using endpoint packing and three forced non-diameter neighbors. -/

namespace Erdos957

theorem certified_family_total_le_active_add_direct {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
      ((chargeDonors p bad).filter (fun u => 0 < localPacketCharge p bad
        (certifiedFamilyPackets p bad height assignments) u x)).card +
      (directChargeSources p bad x).card := by
  classical
  have hbool (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≤ 1 := by
    by_cases hP : P <;> simp only [hP, ite_true, ite_false] <;> omega
  let f := fun u => localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x
  let A := (chargeDonors p bad).filter fun u => 0 < f u
  have hsum : ∑ u ∈ chargeDonors p bad, f u = ∑ u ∈ A, f u := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u _hu hnot
    exact Nat.eq_zero_of_not_pos (fun hpos => hnot (Finset.mem_filter.mpr ⟨_hu, hpos⟩))
  have hsub : A.filter (fun u => (nearestGraph p).Adj u x) ⊆ directChargeSources p bad x := by
    intro u hu
    obtain ⟨huA, hadj⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huA).1, hadj⟩
  change ∑ u ∈ chargeDonors p bad, f u ≤ A.card + _
  rw [hsum]
  calc
    _ ≤ ∑ u ∈ A, (1 + if (nearestGraph p).Adj u x then 1 else 0) := by
      apply Finset.sum_le_sum
      intro u hu
      have hud := (Finset.mem_filter.mp hu).1
      by_cases hadj : (nearestGraph p).Adj u x
      · simp only [ite_eq_left hadj]
        simp only [f, localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
          CertifiedDonorAssignment.packet, LocalChargePacket.weight]
        exact Nat.add_le_add (hbool _) (hbool _)
      · simpa only [ite_eq_right hadj, add_zero] using
          certified_family_charge_le_one_of_not_adj p bad height assignments u x hadj
    _ = A.card + (A.filter (fun u => (nearestGraph p).Adj u x)).card := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ A.card + (directChargeSources p bad x).card :=
      Nat.add_le_add_left (Finset.card_le_card hsub) _

/-- The partner endpoint of an actual six-bottom source is nearby but
inactive. Removing it from the four-endpoint bound leaves at most three
active sources of any rules. -/
theorem SixBottomIndirectSource.active_card_le_three
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i)) :
    ((chargeDonors p (tightHullBadVertices p v)).filter (fun u =>
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)).card ≤ 3 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  have hcap := hi.nearby_diameter_card_le_four p hp hn v hv hh hrange hsupport hpos
    height assignments ij hmin
  obtain ⟨hid, av, _hbx, hqx⟩ := hi.receiver_adj_center_and_bottom p v height assignments
  let choice := selectedSharedFiveCenter p (assignments (v i) hid).context.q av
  have hsource := choice.diameter_neighbor_cases (v i) (assignments (v i) hid).context.endpoint
    (assignments (v i) hid).context.central_adj.symm
  obtain ⟨a, haD, haadj, hane, hapair⟩ : ∃ a, a ∈ diameterEndpoints p ∧
      (nearestGraph p).Adj (assignments (v i) hid).context.q a ∧ a ≠ v i ∧
      (a = choice.left ∨ a = choice.right) := by
    rcases hsource with hl | hr
    · exact ⟨choice.right, choice.right_diameter, choice.center_right,
        by simpa only [hl] using choice.base.ne.symm, Or.inr rfl⟩
    · exact ⟨choice.left, choice.left_diameter, choice.center_left,
        by simpa only [hr] using choice.base.ne, Or.inl rfl⟩
  let A := (chargeDonors p (tightHullBadVertices p v)).filter fun u =>
    0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x
  let B := (diameterEndpoints p).filter fun u => dist (p u) (p x) ≤ 2 * pairDist p ij
  have haB : a ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨haD, ?_⟩
    have ht := dist_triangle (p a) (p (assignments (v i) hid).context.q) (p x)
    rw [nearestGraph_adj_dist_eq p hmin haadj.symm,
      nearestGraph_adj_dist_eq p hmin hqx] at ht
    linarith
  have haA : a ∉ A := by
    intro ha
    obtain ⟨had, hapos⟩ := Finset.mem_filter.mp ha
    have hnot := hi.active_not_selected_endpoint p (by omega) hp v height assignments
      hid av had hapos hane
    exact hapair.elim hnot.1 hnot.2
  have hsub : insert a A ⊆ B := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact haB
    · obtain ⟨hud, hupos⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hud).1,
        localPacketCharge_pos_dist_le_two_min p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) hmin hupos⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem haA] at hc
  change B.card ≤ 4 at hcap
  change A.card ≤ 3
  omega

/-- Six-degree triangle completion forces three distinct non-diameter
neighbors. A receiver of degree at most four can therefore have at most
one direct donor, including donors whose packets are inactive there. -/
theorem SixBottomIndirectSource.direct_card_le_one_of_degree_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hxdeg : (nearestGraph p).degree x ≤ 4) :
    (directChargeSources p (tightHullBadVertices p v) x).card ≤ 1 := by
  classical
  have hiCopy := hi
  obtain ⟨hid, _hix, _hinot, av, hbdeg⟩ := hiCopy
  let q := (assignments (v i) hid).context.q
  let choice := selectedSharedFiveCenter p q av
  let b := choice.selection.bottom
  obtain ⟨hid', av', hbx, hqx⟩ := hi.receiver_adj_center_and_bottom p v height assignments
  have hhud : hid' = hid := Subsingleton.elim _ _
  subst hid'
  have hav : av' = av := Subsingleton.elim _ _
  subst av'
  change (nearestGraph p).Adj b x at hbx
  change (nearestGraph p).degree b = 6 at hbdeg
  have hqb := choice.selection.bottom_adj
  change (nearestGraph p).Adj q b at hqb
  obtain ⟨t, htq, hbt, hxt, _hsum⟩ := degree_six_triangle_completion p
    (by omega) hp hbdeg hbx hqb.symm hqx.symm
  have hqD : q ∉ diameterEndpoints p := by
    intro hD
    have ht := nearestGraph_degree_le_three_of_diameterEndpoint p (by omega) hp q hD
    have hd := choice.center_degree
    omega
  have hbD : b ∉ diameterEndpoints p := by
    intro hD
    have ht := nearestGraph_degree_le_three_of_diameterEndpoint p (by omega) hp b hD
    omega
  have htD : t ∉ diameterEndpoints p := by
    exact sharedFive_bottom_no_diameter_neighbor p hp hn v hv hh hsupport hpos
      (assignments (v i) hid).context.minPair (assignments (v i) hid).context.minPair_spec
      i (Finset.mem_filter.mp hid).2.1 q choice
      (choice.diameter_neighbor_cases (v i) (assignments (v i) hid).context.endpoint
        (assignments (v i) hid).context.central_adj.symm) t hbt
  apply Finset.card_le_one.mpr
  intro u hu w hw
  by_contra huw
  obtain ⟨hud, hux⟩ := Finset.mem_filter.mp hu
  obtain ⟨hwd, hwx⟩ := Finset.mem_filter.mp hw
  have huD := (Finset.mem_filter.mp hud).1
  have hwD := (Finset.mem_filter.mp hwd).1
  have huneq : u ≠ q ∧ u ≠ b ∧ u ≠ t := by
    exact ⟨fun heq => hqD (heq ▸ huD), fun heq => hbD (heq ▸ huD), fun heq => htD (heq ▸ huD)⟩
  have hwneq : w ≠ q ∧ w ≠ b ∧ w ≠ t := by
    exact ⟨fun heq => hqD (heq ▸ hwD), fun heq => hbD (heq ▸ hwD), fun heq => htD (heq ▸ hwD)⟩
  have hsub : ({q, b, t, u, w} : Finset (Fin n)) ⊆ (nearestGraph p).neighborFinset x := by
    intro a ha
    apply ((nearestGraph p).mem_neighborFinset x a).mpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hqx.symm
    · exact hbx.symm
    · exact hxt
    · exact hux.symm
    · exact hwx.symm
  have hc : ({q, b, t, u, w} : Finset (Fin n)).card = 5 := by
    simp [hqb.ne, htq.symm, hbt.ne, huw, huneq.1.symm, huneq.2.1.symm,
      huneq.2.2.symm, hwneq.1.symm, hwneq.2.1.symm, hwneq.2.2.symm]
  have hle := Finset.card_le_card hsub
  rw [hc, (nearestGraph p).card_neighborFinset_eq_degree] at hle
  omega

/-- Full weighted capacity at every low-degree receiver reached by a
six-bottom source, including all other simultaneous direct/indirect rules. -/
theorem SixBottomIndirectSource.capacity_of_degree_le_four
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hxdeg : (nearestGraph p).degree x ≤ 4) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have hactive := hi.active_card_le_three p hp hn v hv hh hrange hsupport hpos height assignments
  have hdirect := hi.direct_card_le_one_of_degree_le_four p hp hn v hv hh hsupport hpos
    height assignments hxdeg
  have hsum := certified_family_total_le_active_add_direct p (tightHullBadVertices p v)
    height assignments x
  omega

/-- Every indirect source with a five-degree center gives full low-degree
capacity: its receiver is either the deep low bottom or a six-bottom site. -/
theorem certified_family_low_capacity_of_indirect_five_center
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n} (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hnot : ¬ (nearestGraph p).Adj u x)
    (hfive : (nearestGraph p).degree (assignments u hud).context.q = 5)
    (hxdeg : (nearestGraph p).degree x ≤ 4) :
    ∑ a ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) a x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp (Finset.mem_filter.mp hud).1
  obtain ⟨i, rfl⟩ := hurange
  have hxrule : 0 < (assignments (v i) hud).rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  have av : Nonempty (SharedFiveCenterChoice p (assignments (v i) hud).context.q) :=
    (assignments (v i) hud).rule.sharedFive_available_of_indirect hfive x hxrule hnot
  let choice := selectedSharedFiveCenter p (assignments (v i) hud).context.q av
  have hxcharge : 0 < choice.charge (v i) x := by
    simpa only [(assignments (v i) hud).rule.weight_eq_selected_sharedFive av x] using hxrule
  have hxq : x ≠ (assignments (v i) hud).context.q :=
    fun heq => hnot (heq ▸ (assignments (v i) hud).context.central_adj)
  rcases choice.selection.branch with hlow | hsix
  · have hxb : x = choice.selection.bottom := by
      by_contra hxb
      simp only [SharedFiveCenterChoice.charge, LocalChargePacket.weight,
        choice.selection.first_central, choice.selection.second_central,
        hlow.2.1, hlow.2.2, ite_eq_right hxq, ite_eq_right hxb,
        zero_add, ite_self] at hxcharge
      omega
    subst x
    have hcap := certified_family_sharedFive_bottom_capacity_of_degree_le_four
      p hp hn v hv hh hsupport hpos i (Finset.mem_filter.mp hud).2.1
      (assignments (v i) hud).context.q choice
      (choice.diameter_neighbor_cases (v i) (assignments (v i) hud).context.endpoint
        (assignments (v i) hud).context.central_adj.symm)
      (tightHullBadVertices p v) height assignments hxdeg
    exact hcap
  · have hi : SixBottomIndirectSource p v height assignments x (v i) :=
      ⟨hud, hx, hnot, av, hsix.1⟩
    exact hi.capacity_of_degree_le_four p hp hn v hv hh hrange hsupport hpos
      height assignments hxdeg

/-- All indirect sources in any remaining low-degree overload must use
six-degree centers. Five-center rules and direct-only overloads are excluded
by full sums, not by checking sources independently. -/
theorem low_degree_overload_has_six_center_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hxdeg : (nearestGraph p).degree x ≤ 4)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ a ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) a x) :
    (nearestGraph p).degree x = 4 ∧ ∃ u,
      ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
        0 < localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
        ¬ (nearestGraph p).Adj u x ∧
        (nearestGraph p).degree (assignments u hud).context.q = 6 := by
  classical
  have hdeg : (nearestGraph p).degree x = 4 := by
    by_contra hne
    have hc := certified_family_receiver_capacity_of_degree_le_three
      p hp hn v hv hh hrange hsupport hpos height assignments x (by omega)
    omega
  refine ⟨hdeg, ?_⟩
  let packets := certifiedFamilyPackets p (tightHullBadVertices p v) height assignments
  have hex : ∃ u, 0 < localPacketCharge p (tightHullBadVertices p v) packets u x ∧
      ¬ (nearestGraph p).Adj u x := by
    by_contra hnone
    have hall : ∀ u, 0 < localPacketCharge p (tightHullBadVertices p v) packets u x →
        (nearestGraph p).Adj u x := by
      intro u hu
      by_contra hnot
      exact hnone ⟨u, hu, hnot⟩
    have hz := indirectPacketChargeTotal_eq_zero_of_positive_adj p
      (tightHullBadVertices p v) packets x hall
    have hs := localPacketCharge_sum_eq_direct_add_indirect p
      (tightHullBadVertices p v) packets x
    have hc := tight_flat_direct_charge_le_capacity p hp hn v hv hh hrange hsupport hpos packets x
    change 2 * (6 - (nearestGraph p).degree x) <
      ∑ a ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v) packets a x at hover
    omega
  obtain ⟨u, hx, hnot⟩ := hex
  have hud := localPacketCharge_pos_donor p (tightHullBadVertices p v) packets u x hx
  have hxrule : 0 < (assignments u hud).rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, packets, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  refine ⟨u, hud, hx, hnot, ?_⟩
  rcases (assignments u hud).rule.center_degree_five_or_six_of_indirect x hxrule hnot with h5 | h6
  · have hc := certified_family_low_capacity_of_indirect_five_center
      p hp hn v hv hh hrange hsupport hpos height assignments hud hx hnot h5 hxdeg
    omega
  · exact h6

end Erdos957
