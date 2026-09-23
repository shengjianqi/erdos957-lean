import BoundarySixNeighbors
import ChargingAccounting

/-! Local two-unit charge packets. Global receiver congestion is a separate question. -/

namespace Erdos957

/-- Two half-unit destinations for one diameter endpoint, with their local
degree slack and paths in the nearest-distance graph. -/
structure LocalChargePacket {n : ℕ} (p : Fin n → Point) (u : Fin n) where
  left : Fin n
  right : Fin n
  left_outside : left ∉ diameterEndpoints p
  right_outside : right ∉ diameterEndpoints p
  left_degree : (nearestGraph p).degree left ≤ 5
  right_degree : (nearestGraph p).degree right ≤ 5
  repeated_degree : left = right → (nearestGraph p).degree left ≤ 4
  left_reachable : (nearestGraph p).Adj u left ∨
    ∃ v, (nearestGraph p).Adj u v ∧ (nearestGraph p).Adj v left
  right_reachable : (nearestGraph p).Adj u right ∨
    ∃ v, (nearestGraph p).Adj u v ∧ (nearestGraph p).Adj v right

/-- Each destination receives one of the two charge units. -/
def LocalChargePacket.weight {n : ℕ} {p : Fin n → Point} {u : Fin n}
    (packet : LocalChargePacket p u) (k : Fin n) : ℕ :=
  (if k = packet.left then 1 else 0) + (if k = packet.right then 1 else 0)

/-- Both units land outside the diameter endpoint set. -/
theorem LocalChargePacket.sum_weight_outside {n : ℕ} {p : Fin n → Point}
    {u : Fin n} (packet : LocalChargePacket p u) :
    ∑ k ∈ Finset.univ.filter (fun i : Fin n => i ∉ diameterEndpoints p),
      packet.weight k = 2 := by
  classical
  have hleft : packet.left ∈ Finset.univ.filter
      (fun i : Fin n => i ∉ diameterEndpoints p) := by
    simp [packet.left_outside]
  have hright : packet.right ∈ Finset.univ.filter
      (fun i : Fin n => i ∉ diameterEndpoints p) := by
    simp [packet.right_outside]
  simp only [LocalChargePacket.weight, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', hleft, hright]

/-- An individual receiver's packet weight fits its own degree slack. -/
theorem LocalChargePacket.weight_le_degree_slack {n : ℕ}
    {p : Fin n → Point} {u : Fin n}
    (packet : LocalChargePacket p u) (k : Fin n) :
    packet.weight k ≤ 6 - (nearestGraph p).degree k := by
  by_cases hl : k = packet.left <;> by_cases hr : k = packet.right
  · have hd : (nearestGraph p).degree k ≤ 4 := by
      rw [hl]
      exact packet.repeated_degree (hl.symm.trans hr)
    have hrl : packet.left = packet.right := hl.symm.trans hr
    have hw : packet.weight k = 2 := by simp [LocalChargePacket.weight, hl, hrl]
    rw [hw]
    omega
  · have hd : (nearestGraph p).degree k ≤ 5 := by rw [hl]; exact packet.left_degree
    have hrl : packet.left ≠ packet.right := fun h => hr (hl.trans h)
    have hw : packet.weight k = 1 := by simp [LocalChargePacket.weight, hl, hrl]
    rw [hw]
    omega
  · have hd : (nearestGraph p).degree k ≤ 5 := by rw [hr]; exact packet.right_degree
    have hrl : packet.right ≠ packet.left := fun h => hl (hr.trans h)
    have hw : packet.weight k = 1 := by simp [LocalChargePacket.weight, hr, hrl]
    rw [hw]
    omega
  · simp [LocalChargePacket.weight, hl, hr]

/-- The weaker doubled-slack bound follows from the sharper single-packet
bound, and matches the receiver capacity used in global accounting. -/
theorem LocalChargePacket.weight_le_local_capacity {n : ℕ}
    {p : Fin n → Point} {u : Fin n}
    (packet : LocalChargePacket p u) (k : Fin n) :
    packet.weight k ≤ 2 * (6 - (nearestGraph p).degree k) := by
  have h := packet.weight_le_degree_slack k
  omega

/-- A positive packet weight is sent to a neighbor or a vertex at distance
two in the nearest-distance graph. -/
theorem LocalChargePacket.positive_reachable {n : ℕ}
    {p : Fin n → Point} {u : Fin n}
    (packet : LocalChargePacket p u) (k : Fin n)
    (hk : 0 < packet.weight k) :
    (nearestGraph p).Adj u k ∨
      ∃ v, (nearestGraph p).Adj u v ∧ (nearestGraph p).Adj v k := by
  by_cases hl : k = packet.left
  · simpa only [hl] using packet.left_reachable
  by_cases hr : k = packet.right
  · simpa only [hr] using packet.right_reachable
  simp [LocalChargePacket.weight, hl, hr] at hk

/-- Paper Case 1: the two common neighbors of a diameter endpoint and its
degree-six neighbor give two distinct outside receivers with spare degree. -/
noncomputable def localChargePacket_of_six_neighbor {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u v : Fin n} (hu : u ∈ diameterEndpoints p)
    (huv : (nearestGraph p).Adj u v)
    (hvdegree : (nearestGraph p).degree v = 6)
    (hunique : ∀ w, (nearestGraph p).Adj v w →
      w ∈ diameterEndpoints p → w = u) :
    LocalChargePacket p u := by
  classical
  let hex := diameterEndpoint_six_neighbor_common_degree_bounds p hn hp hu huv hvdegree
  let a := Classical.choose hex
  let hex' := Classical.choose_spec hex
  let b := Classical.choose hex'
  obtain ⟨hab, hua, hva, hda, hub, hvb, hdb⟩ := Classical.choose_spec hex'
  have haout : a ∉ diameterEndpoints p := by
    intro ha
    exact ((nearestGraph p).ne_of_adj hua) ((hunique a hva ha).symm)
  have hbout : b ∉ diameterEndpoints p := by
    intro hb
    exact ((nearestGraph p).ne_of_adj hub) ((hunique b hvb hb).symm)
  exact {
    left := a
    right := b
    left_outside := haout
    right_outside := hbout
    left_degree := hda
    right_degree := hdb
    repeated_degree := fun h => False.elim (hab h)
    left_reachable := Or.inl hua
    right_reachable := Or.inl hub
  }

/-- Paper Case 3 local singleton packet, when an outside nearest neighbor
already has at least two units of degree slack. -/
def localChargePacket_of_low_degree_neighbor {n : ℕ}
    (p : Fin n → Point) {u v : Fin n}
    (huv : (nearestGraph p).Adj u v)
    (hvout : v ∉ diameterEndpoints p)
    (hvdegree : (nearestGraph p).degree v ≤ 4) :
    LocalChargePacket p u := {
  left := v
  right := v
  left_outside := hvout
  right_outside := hvout
  left_degree := by omega
  right_degree := by omega
  repeated_degree := fun _ => hvdegree
  left_reachable := Or.inl huv
  right_reachable := Or.inl huv
}

end Erdos957
