import DonorCases

/-! The low-degree central rule applies whether or not another diameter
endpoint shares the center. Its certificate deliberately has no UniqueD field.
Global sums from several donors are a separate obligation. -/

namespace Erdos957

/-- Both half-units go to the actual interior central neighbor of degree at
most four. No restriction is imposed on its other diameter endpoint neighbors. -/
structure CertifiedLowCentralPacket {n : ℕ} (p : Fin n → Point)
    (u q : Fin n) where
  packet : LocalChargePacket p u
  central_adj : (nearestGraph p).Adj u q
  central_degree : (nearestGraph p).degree q ≤ 4
  central_interior : p q ∈ interior (convexHull ℝ (Set.range p))
  left_eq : packet.left = q
  right_eq : packet.right = q

/-- Every actual low-degree donor context has this rule certificate,
including contexts whose central neighbor is shared. -/
def certifiedLowCentralPacket_of_context {n : ℕ}
    (p : Fin n → Point) {bad : Finset (Fin n)} {u : Fin n}
    (ctx : DonorContext p bad u)
    (hlow : (nearestGraph p).degree ctx.q ≤ 4) :
    CertifiedLowCentralPacket p u ctx.q where
  packet := localChargePacket_of_low_degree_neighbor p
    ctx.central_adj ctx.central_outside hlow
  central_adj := ctx.central_adj
  central_degree := hlow
  central_interior := ctx.central_interior
  left_eq := rfl
  right_eq := rfl

theorem CertifiedLowCentralPacket.weight_eq {n : ℕ}
    {p : Fin n → Point} {u q : Fin n}
    (choice : CertifiedLowCentralPacket p u q) (x : Fin n) :
    choice.packet.weight x = if x = q then 2 else 0 := by
  simp only [LocalChargePacket.weight, choice.left_eq, choice.right_eq]
  split_ifs <;> norm_num

theorem CertifiedLowCentralPacket.positive_iff {n : ℕ}
    {p : Fin n → Point} {u q x : Fin n}
    (choice : CertifiedLowCentralPacket p u q) :
    0 < choice.packet.weight x ↔ x = q := by
  rw [choice.weight_eq]
  split_ifs with h <;> simp_all

theorem CertifiedLowCentralPacket.positive_geometry {n : ℕ}
    {p : Fin n → Point} {u q x : Fin n}
    (choice : CertifiedLowCentralPacket p u q)
    (hx : 0 < choice.packet.weight x) :
    (nearestGraph p).Adj u x ∧
      p x ∈ interior (convexHull ℝ (Set.range p)) ∧
      (nearestGraph p).degree x ≤ 4 := by
  have heq := choice.positive_iff.mp hx
  subst x
  exact ⟨choice.central_adj, choice.central_interior, choice.central_degree⟩

end Erdos957
