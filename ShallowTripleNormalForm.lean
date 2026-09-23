import ShallowSourceTypes

/-! The final degree-five shallow obstruction in a finite cyclic normal form.
The purpose of this file is to remove all remaining global-source bookkeeping:
a hypothetical overload produces three distinct local hull indices, one
six-bottom anchor, and only direct/six-bottom source types. -/

namespace Erdos957

/-- Membership in the seven-source neighborhood, specialized to a distinct
source, removes the zero offset and leaves exactly the six nonzero cyclic
offsets. -/
theorem distinct_mem_hullSourceNeighborhood_iff_six_offsets
    {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (hv : Function.Injective v)
    (i j : Fin h) (hij : i ≠ j) :
    v j ∈ hullSourceNeighborhood v i ↔
      j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1 := by
  rw [mem_hullSourceNeighborhood_iff]
  constructor
  · intro h
    rcases h with h0 | h1 | hm1 | h2 | hm2 | h3 | hm3
    · exact False.elim (hij (hv h0).symm)
    · exact Or.inl (hv h1)
    · exact Or.inr (Or.inl (hv hm1))
    · exact Or.inr (Or.inr (Or.inl (hv h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hv hm2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hv h3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hv hm3)))))
  · intro h
    rcases h with h1 | hm1 | h2 | hm2 | h3 | hm3
    · exact Or.inr (Or.inl (congrArg v h1))
    · exact Or.inr (Or.inr (Or.inl (congrArg v hm1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg v h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg v hm2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg v h3))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg v hm3))))))

/-- A hypothetical degree-five mixed overload is reduced to a finite typed
three-source configuration.  Relative to the six-bottom anchor `i`, both
other sources lie at one of the six nonzero offsets ±1, ±2, ±3. -/
theorem degree_five_mixed_overload_has_typed_offset_triple
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ i j k : Fin h,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      SixBottomIndirectSource p v height assignments x (v i) ∧
      (DirectActiveSource p v height assignments x (v j) ∨
        SixBottomIndirectSource p v height assignments x (v j)) ∧
      (DirectActiveSource p v height assignments x (v k) ∨
        SixBottomIndirectSource p v height assignments x (v k)) ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) := by
  obtain ⟨i, j, k, hij, hik, hjk, hiSix, hjType, hkType,
      hji, hki, _hijLoc, _hkj, _hikLoc, _hjkLoc⟩ :=
    degree_five_mixed_overload_has_typed_local_triple
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  refine ⟨i, j, k, hij, hik, hjk, hiSix, hjType, hkType, ?_, ?_⟩
  · exact (distinct_mem_hullSourceNeighborhood_iff_six_offsets v hv i j hij).1 hji
  · exact (distinct_mem_hullSourceNeighborhood_iff_six_offsets v hv i k hik).1 hki

/-- The two non-anchor source types give only four syntactic branches; the
middle two are mirror versions of the same direct/indirect overlap. -/
theorem typed_pair_four_cases
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x u w : Fin n)
    (hu : DirectActiveSource p v height assignments x u ∨
      SixBottomIndirectSource p v height assignments x u)
    (hw : DirectActiveSource p v height assignments x w ∨
      SixBottomIndirectSource p v height assignments x w) :
    (DirectActiveSource p v height assignments x u ∧
      DirectActiveSource p v height assignments x w) ∨
    (DirectActiveSource p v height assignments x u ∧
      SixBottomIndirectSource p v height assignments x w) ∨
    (SixBottomIndirectSource p v height assignments x u ∧
      DirectActiveSource p v height assignments x w) ∨
    (SixBottomIndirectSource p v height assignments x u ∧
      SixBottomIndirectSource p v height assignments x w) := by
  rcases hu with huD | huI <;> rcases hw with hwD | hwI
  · exact Or.inl ⟨huD, hwD⟩
  · exact Or.inr (Or.inl ⟨huD, hwI⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨huI, hwD⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨huI, hwI⟩))

end Erdos957
