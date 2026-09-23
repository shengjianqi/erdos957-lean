import HullExteriorAngles

/-! Exceptional hull vertices selected by the actual exterior angles. -/

namespace Erdos957

open scoped BigOperators

/-- Positions whose radius-three cyclic neighborhood contains a turn of at
least one degree. -/
noncomputable def hullBadPositions {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun i => ∃ k : Fin 7,
    Real.pi / 180 ≤ hullExteriorAngle p v
      (i + (Fin.ofNat h k.val - 3))

/-- The actual configuration indices at exceptional hull positions. -/
noncomputable def hullBadVertices {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) : Finset (Fin n) :=
  (hullBadPositions p v).image v

/-- At most 2520 actual hull vertices have a nonflat radius-three neighborhood. -/
theorem hullBadVertices_card_le_2520 {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hnonneg : ∀ i, 0 ≤ hullExteriorAngle p v i)
    (hsum : ∑ i, hullExteriorAngle p v i ≤ 2 * Real.pi) :
    (hullBadVertices p v).card ≤ 2520 := by
  classical
  calc
    (hullBadVertices p v).card ≤ (hullBadPositions p v).card :=
      Finset.card_image_le
    _ ≤ 2520 := by
      exact card_cyclic_nonflat_le_2520 (hullExteriorAngle p v) hnonneg hsum

/-- Every exceptional index is a genuine extreme point of the finite hull. -/
theorem hullBadVertices_subset_hullVertexIndices {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n))) :
    hullBadVertices p v ⊆ hullVertexIndices p := by
  classical
  intro j hj
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  change v i ∈ (hullVertexIndices p : Set (Fin n))
  rw [← hrange]
  exact Set.mem_range_self i

/-- For an injective hull enumeration, a vertex is outside the exceptional
set exactly when each of its seven selected turns is below one degree. -/
theorem hull_vertex_not_bad_iff_all_seven_flat {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hv : Function.Injective v) (i : Fin h) :
    v i ∉ hullBadVertices p v ↔
      ∀ k : Fin 7,
        hullExteriorAngle p v (i + (Fin.ofNat h k.val - 3)) < Real.pi / 180 := by
  classical
  have himage : v i ∈ hullBadVertices p v ↔ i ∈ hullBadPositions p v := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have : j = i := hv hji
      simpa only [this] using hj
    · intro hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [not_iff_not.mpr himage]
  simp only [hullBadPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, not_exists, not_le]

/-- The actual noncollinear configuration has a cyclic hull enumeration with
at most 2520 exceptional original indices. Every other hull vertex has all
seven nearby exterior angles below one degree. -/
theorem exists_hull_bad_vertices_of_noncollinear {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    letI : NeZero (hullVertexCount p) :=
      ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      (∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k)) ∧
      (hullBadVertices p v).card ≤ 2520 ∧
      hullBadVertices p v ⊆ hullVertexIndices p ∧
      (∀ i, v i ∉ hullBadVertices p v ↔
        ∀ k : Fin 7,
          hullExteriorAngle p v (i + (Fin.ofNat (hullVertexCount p) k.val - 3)) <
            Real.pi / 180) := by
  classical
  have : NeZero (hullVertexCount p) :=
    ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
  obtain ⟨v, hv, hrange, hsupport, _hpos, _hsum, hbad⟩ :=
    exists_hull_exterior_angles_and_exception_bound p hn hp hnot
  refine ⟨v, hv, hrange, hsupport, ?_, ?_, ?_⟩
  · have hbad' : (hullBadPositions p v).card ≤ 2520 := by
      simpa only [hullBadPositions] using hbad
    exact (Finset.card_image_le : (hullBadVertices p v).card ≤
      (hullBadPositions p v).card).trans hbad'
  · exact hullBadVertices_subset_hullVertexIndices p v hrange
  · intro i
    exact hull_vertex_not_bad_iff_all_seven_flat p v hv i

end Erdos957
