import SharedFivePairReflection

/-! One certified shared-five choice per central vertex. Contributions of
arbitrary subsets of its two endpoints are controlled here; sums across
different centers and other rules require a separate geometric bound. -/

namespace Erdos957

/-- The center's selected pair retains its actual diameter endpoints,
minimum-distance triangle and supporting orientation as well as its packets. -/
structure SharedFiveCenterChoice {n : ℕ} (p : Fin n → Point) (q : Fin n) where
  left : Fin n
  right : Fin n
  left_diameter : left ∈ diameterEndpoints p
  right_diameter : right ∈ diameterEndpoints p
  center_left : (nearestGraph p).Adj q left
  center_right : (nearestGraph p).Adj q right
  base : (nearestGraph p).Adj left right
  center_degree : (nearestGraph p).degree q = 5
  support : ∀ k, 0 ≤ turn (p right) (p left) (p k)
  selection : SharedFivePairSelection p left right q

/-- Choice is indexed only by the point configuration and the center.
Different proofs of availability cannot select independent pairs. -/
noncomputable def selectedSharedFiveCenter {n : ℕ} (p : Fin n → Point)
    (q : Fin n) (available : Nonempty (SharedFiveCenterChoice p q)) :
    SharedFiveCenterChoice p q := Classical.choice available

theorem selectedSharedFiveCenter_proof_independent {n : ℕ}
    (p : Fin n → Point) (q : Fin n)
    (h₁ h₂ : Nonempty (SharedFiveCenterChoice p q)) :
    selectedSharedFiveCenter p q h₁ = selectedSharedFiveCenter p q h₂ := rfl

/-- Any diameter neighbor of this center is one of the selected endpoints. -/
theorem SharedFiveCenterChoice.diameter_neighbor_cases {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (u : Fin n) (hu : u ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) : u = choice.left ∨ u = choice.right :=
  choice.selection.diameter_neighbors u hqu hu

/-- The unordered endpoint pair is determined by the center, even before
fixing a single selected object. This does not assert equality of packets. -/
theorem SharedFiveCenterChoice.endpoint_pair_unique {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (a b : SharedFiveCenterChoice p q) :
    (a.left = b.left ∧ a.right = b.right) ∨
      (a.left = b.right ∧ a.right = b.left) := by
  have hl := b.diameter_neighbor_cases a.left a.left_diameter a.center_left
  have hr := b.diameter_neighbor_cases a.right a.right_diameter a.center_right
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact False.elim (a.base.ne (hl.trans hr.symm))
  · exact Or.inl ⟨hl, hr⟩
  · exact Or.inr ⟨hl, hr⟩
  · exact False.elim (a.base.ne (hl.trans hr.symm))

/-- Project the donor's packet from the one selected object. The endpoint
case proof is derived from actual diameter membership and center adjacency. -/
noncomputable def SharedFiveCenterChoice.packetFor {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (u : Fin n) (hu : u ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) : LocalChargePacket p u := by
  classical
  exact if h : u = choice.left then h.symm ▸ choice.selection.first
    else ((choice.diameter_neighbor_cases u hu hqu).resolve_left h).symm ▸
      choice.selection.second

/-- Charge from the two selected endpoints, zero at all other source indices. -/
noncomputable def SharedFiveCenterChoice.charge {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (u x : Fin n) : ℕ := by
  classical
  exact (if u = choice.left then choice.selection.first.weight x else 0) +
    (if u = choice.right then choice.selection.second.weight x else 0)

/-- The projected packet uses precisely the center's fixed charge function. -/
theorem SharedFiveCenterChoice.packetFor_weight {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (u : Fin n) (hu : u ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) (x : Fin n) :
    (choice.packetFor u hu hqu).weight x = choice.charge u x := by
  classical
  by_cases hl : u = choice.left
  · subst u
    simp [packetFor, charge, choice.base.ne]
  · have hr := (choice.diameter_neighbor_cases u hu hqu).resolve_left hl
    subst u
    simp [packetFor, charge, choice.base.ne.symm]

/-- Each finite subset of sources contributes only the selected endpoints
it actually contains. This also handles an exceptional or ineligible partner. -/
theorem SharedFiveCenterChoice.sum_charge_eq {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (sources : Finset (Fin n)) (x : Fin n) :
    ∑ u ∈ sources, choice.charge u x =
      (if choice.left ∈ sources then choice.selection.first.weight x else 0) +
      (if choice.right ∈ sources then choice.selection.second.weight x else 0) := by
  classical
  simp only [charge, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

theorem SharedFiveCenterChoice.sum_charge_le_pair {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (sources : Finset (Fin n)) (x : Fin n) :
    ∑ u ∈ sources, choice.charge u x ≤
      choice.selection.first.weight x + choice.selection.second.weight x := by
  classical
  rw [choice.sum_charge_eq]
  split_ifs <;> omega

/-- Capacity for one center, restricted to any actual donor subset. No
contribution from another center or charging rule is included in this sum. -/
theorem SharedFiveCenterChoice.sum_charge_le_capacity {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (sources : Finset (Fin n)) (x : Fin n) :
    ∑ u ∈ sources, choice.charge u x ≤ 2 * (6 - (nearestGraph p).degree x) :=
  (choice.sum_charge_le_pair sources x).trans
    (choice.selection.pair_weight_le_capacity x)

theorem SharedFiveCenterChoice.noncentral_sum_charge_le_one {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (sources : Finset (Fin n))
    (hsix : (nearestGraph p).degree choice.selection.bottom = 6)
    (x : Fin n) (hx : x ≠ q) : ∑ u ∈ sources, choice.charge u x ≤ 1 :=
  (choice.sum_charge_le_pair sources x).trans
    (choice.selection.noncentral_weight_le_one hsix x hx)

/-- Whenever the actual tight-flat shared triangle is available, the one
center-indexed selected object is available too. Its endpoints may have been
presented differently in the existence proof, but the center fixes the choice. -/
theorem sharedFiveCenterChoice_nonempty_of_either_tight_flat_endpoint
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hqu : (nearestGraph p).Adj q (v (i + 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v ∨
      v (i + 1) ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) (hw : v i ∈ diameterEndpoints p) :
    Nonempty (SharedFiveCenterChoice p q) := by
  exact ⟨{
    left := v (i + 1)
    right := v i
    left_diameter := hu
    right_diameter := hw
    center_left := hqu
    center_right := hqw
    base := hbase.symm
    center_degree := hqdeg
    support := hsupport i
    selection := sharedFivePairSelection_of_either_tight_flat_endpoint
      p hp hn v hv hh hsupport hpos i q hbase hqu hqw hqdeg hgood hu hw
  }⟩

end Erdos957
