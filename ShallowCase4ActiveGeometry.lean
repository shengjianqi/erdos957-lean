import ShallowCase4ThreeStepExclusion
import SupportingFamilyShallowNormalForm

/-! Geometry extracted from an actual active semantic Case-4 source.  The
semantic degree-five/shared-diameter condition forces the retained certified
rule to be the center-indexed shared-five rule.  Hence a positive receiver is
either the center itself or a nearest neighbor of that center. -/

namespace Erdos957

/-- A certified rule whose retained center is genuinely paper Case 4 must be
one of the shared-five constructors; the low, unique, and degree-six
constructors contradict the semantic Case-4 data. -/
theorem CertifiedDonorRule.sharedFive_available_of_paperCase4
    {n : ℕ} {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height)
    (hcase : PaperCase4 p u q) :
    Nonempty (SharedFiveCenterChoice p q) := by
  rcases hcase with ⟨hq5, hshared⟩
  cases rule with
  | low choice =>
      have hlow := choice.central_degree
      omega
  | unique choice high =>
      obtain ⟨w, hwu, hqw, hwD⟩ := hshared
      exact False.elim (hwu (choice.unique w hqw hwD))
  | sharedFive available endpoint central => exact available
  | sharedSix choice =>
      have hsix := choice.center_degree
      omega
  | reflectedSharedSix choice =>
      have hsix := choice.original_neighbors.1
      omega

/-- A positive packet from a semantic Case-4 source reaches either its
retained center or a nearest neighbor of that center. -/
theorem CertifiedDonorAssignment.paperCase4_positive_center_or_adj
    {n : ℕ} (p : Fin n → Point) {bad : Finset (Fin n)}
    {u : Fin n} {height : Fin n → ℝ}
    (assignment : CertifiedDonorAssignment p bad u height)
    (hcase : PaperCase4 p u assignment.context.q)
    (x : Fin n) (hx : 0 < assignment.packet.weight x) :
    x = assignment.context.q ∨
      (nearestGraph p).Adj assignment.context.q x := by
  rcases hcase with ⟨hq5, hshared⟩
  cases hrule : assignment.rule with
  | low choice =>
      have hlow := choice.central_degree
      omega
  | unique choice high =>
      obtain ⟨w, hwu, hqw, hwD⟩ := hshared
      exact False.elim (hwu (choice.unique w hqw hwD))
  | sharedFive available endpoint central =>
      let selected := selectedSharedFiveCenter p assignment.context.q available
      have hx' : 0 < (selected.packetFor u endpoint central).weight x := by
        simpa only [CertifiedDonorAssignment.packet, hrule, CertifiedDonorRule.packet]
          using hx
      rw [selected.packetFor_weight] at hx'
      by_cases hul : u = selected.left
      · have hxfirst : 0 < selected.selection.first.weight x := by
          simpa [SharedFiveCenterChoice.charge, hul, selected.base.ne] using hx'
        by_cases hxc : x = assignment.context.q
        · exact Or.inl hxc
        · right
          have hxr : x = selected.selection.first.right := by
            by_contra hne
            simp [LocalChargePacket.weight, selected.selection.first_central,
              hxc, hne] at hxfirst
          rw [hxr]
          exact selected.selection.first_secondary.1
      · have hur := (selected.diameter_neighbor_cases u endpoint central).resolve_left hul
        have hxsecond : 0 < selected.selection.second.weight x := by
          simpa [SharedFiveCenterChoice.charge, hur, selected.base.ne.symm] using hx'
        by_cases hxc : x = assignment.context.q
        · exact Or.inl hxc
        · right
          have hxr : x = selected.selection.second.right := by
            by_contra hne
            simp [LocalChargePacket.weight, selected.selection.second_central,
              hxc, hne] at hxsecond
          rw [hxr]
          exact selected.selection.second_secondary.1
  | sharedSix choice =>
      have hsix := choice.center_degree
      omega
  | reflectedSharedSix choice =>
      have hsix := choice.original_neighbors.1
      omega

end Erdos957
