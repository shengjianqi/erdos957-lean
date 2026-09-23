import CenterChargeGroups

/-! Two distinct indirect positive sources at one degree-five center force
the selected low bottom and both endpoints of that center's fixed pair. -/

namespace Erdos957

/-- An indirect positive rule at a degree-five center must retain an actual
shared-five choice. The direct constructors cannot supply such a receiver. -/
theorem CertifiedDonorRule.sharedFive_available_of_indirect {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height)
    (hq : (nearestGraph p).degree q = 5) (x : Fin n)
    (hx : 0 < rule.packet.weight x) (hnot : ¬ (nearestGraph p).Adj u x) :
    Nonempty (SharedFiveCenterChoice p q) := by
  cases rule with
  | low choice => have hlow := choice.central_degree; omega
  | unique choice high => exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available endpoint central => exact available
  | sharedSix choice => have hsix := choice.center_degree; omega
  | reflectedSharedSix choice =>
      have hsix := choice.original_neighbors.1
      omega

/-- Both sources of a degree-five center can charge the same noncentral
receiver only in its low-bottom branch. This identifies the exact selected
endpoint pair and the bottom, without assuming any extra hull geometry. -/
theorem certified_sharedFive_paired_indirect_receiver {n : ℕ}
    {p : Fin n → Point} {u w q x : Fin n} {heightU heightW : Fin n → ℝ}
    (ruleU : CertifiedDonorRule p u q heightU)
    (ruleW : CertifiedDonorRule p w q heightW)
    (hq : (nearestGraph p).degree q = 5)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (hne : u ≠ w)
    (hxU : 0 < ruleU.packet.weight x) (hxW : 0 < ruleW.packet.weight x)
    (hnotU : ¬ (nearestGraph p).Adj u x) (_hnotW : ¬ (nearestGraph p).Adj w x) :
    ∃ available : Nonempty (SharedFiveCenterChoice p q),
      x = (selectedSharedFiveCenter p q available).selection.bottom ∧
      ((u = (selectedSharedFiveCenter p q available).left ∧
          w = (selectedSharedFiveCenter p q available).right) ∨
        (u = (selectedSharedFiveCenter p q available).right ∧
          w = (selectedSharedFiveCenter p q available).left)) ∧
      (nearestGraph p).degree (selectedSharedFiveCenter p q available).selection.bottom ≤ 5 := by
  classical
  let available := ruleU.sharedFive_available_of_indirect hq x hxU hnotU
  let selected := selectedSharedFiveCenter p q available
  have hxp : x ≠ q := fun heq => hnotU (heq ▸ hqu.symm)
  have hposU : 0 < selected.charge u x := by
    simpa only [ruleU.weight_eq_selected_sharedFive available x] using hxU
  have hposW : 0 < selected.charge w x := by
    simpa only [ruleW.weight_eq_selected_sharedFive available x] using hxW
  have hpair : (u = selected.left ∧ w = selected.right) ∨
      (u = selected.right ∧ w = selected.left) := by
    rcases selected.diameter_neighbor_cases u hu hqu with hul | hur <;>
      rcases selected.diameter_neighbor_cases w hw hqw with hwl | hwr
    · exact False.elim (hne (hul.trans hwl.symm))
    · exact Or.inl ⟨hul, hwr⟩
    · exact Or.inr ⟨hur, hwl⟩
    · exact False.elim (hne (hur.trans hwr.symm))
  have hlow : (nearestGraph p).degree selected.selection.bottom ≤ 5 := by
    rcases selected.selection.branch with hlow | hsix
    · exact hlow.1
    · have hbound := selected.noncentral_sum_charge_le_one {u, w} hsix.1 x hxp
      have hsum : ∑ a ∈ ({u, w} : Finset (Fin n)), selected.charge a x =
          selected.charge u x + selected.charge w x := by simp [hne]
      rw [hsum] at hbound
      omega
  have hright : selected.selection.first.right = selected.selection.bottom ∧
      selected.selection.second.right = selected.selection.bottom := by
    rcases selected.selection.branch with hbranch | hbranch
    · exact hbranch.2
    · omega
  have hbottom : x = selected.selection.bottom := by
    by_contra hx
    simp only [SharedFiveCenterChoice.charge, LocalChargePacket.weight,
      selected.selection.first_central, selected.selection.second_central,
      hright.1, hright.2, ite_eq_right hxp, ite_eq_right hx, zero_add, ite_self] at hposU
    omega
  exact ⟨available, hbottom, hpair, hlow⟩

end Erdos957
