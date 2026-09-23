import ShallowDegreeFiveStructure

/-! A degree-five receiver has only one unit of packet slack per donor.  Thus
any capacity violation is already a genuinely three-source phenomenon.  This
isolates the final shallow task as a source-overlap exclusion rather than a
weight estimate. -/

namespace Erdos957

/-- Every assembled contribution to a degree-five receiver is at most one
(doubled half-charge) unit. -/
theorem certified_family_charge_le_one_of_receiver_degree_five {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5) (u : Fin n) :
    localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤ 1 := by
  classical
  by_cases hu : u ∈ chargeDonors p bad
  · have hw := (assignments u hu).packet.weight_le_degree_slack x
    simp only [localPacketCharge, dite_eq_left hu, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet]
    simpa only [CertifiedDonorAssignment.packet, hdegree] using hw
  · simp [localPacketCharge, hu]

/-- If a degree-five receiver exceeds its two-unit capacity, then at least
three distinct certified donors contribute positively there. -/
theorem certified_family_degree_five_overload_active_card_ge_three {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ u ∈ chargeDonors p bad,
        localPacketCharge p bad
          (certifiedFamilyPackets p bad height assignments) u x) :
    3 ≤ ((chargeDonors p bad).filter (fun u =>
      0 < localPacketCharge p bad
        (certifiedFamilyPackets p bad height assignments) u x)).card := by
  classical
  let f := fun u : Fin n => localPacketCharge p bad
    (certifiedFamilyPackets p bad height assignments) u x
  let A := (chargeDonors p bad).filter (fun u => 0 < f u)
  have hsum : (∑ u ∈ chargeDonors p bad, f u) ≤ A.card := by
    calc
      (∑ u ∈ chargeDonors p bad, f u) = ∑ u ∈ A, f u := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro u hu hnot
        exact Nat.eq_zero_of_not_pos (fun hpos =>
          hnot (Finset.mem_filter.mpr ⟨hu, hpos⟩))
      _ ≤ ∑ _u ∈ A, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact certified_family_charge_le_one_of_receiver_degree_five
          p bad height assignments x hdegree u
      _ = A.card := by simp
  change 3 ≤ A.card
  have hover' : 2 < ∑ u ∈ chargeDonors p bad, f u := by
    simpa only [hdegree] using hover
  omega

/-- In a mixed degree-five overload, every positive indirect donor is in the
six-bottom shared-five branch.  Thus all remaining indirect units are the
separated secondary half-charges of Case 4, never its repeated low bottom. -/
theorem certified_family_degree_five_mixed_overload_indirect_forces_six_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    (u : Fin n) (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hnot : ¬ (nearestGraph p).Adj u x) :
    ∃ available : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q),
      (nearestGraph p).degree
        (selectedSharedFiveCenter p (assignments u hud).context.q available).selection.bottom = 6 := by
  have hfive := certified_family_degree_five_overload_indirect_center_degree_five
    p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover u hud hx hnot
  exact certified_indirect_degree_five_center_mixed_forces_six_bottom
    p hp hn v hv hh hrange hsupport hpos height assignments hud hx hnot hfive hdiam

end Erdos957
