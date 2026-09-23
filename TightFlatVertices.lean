import HullFlatVertices
import Mathlib.Tactic.Abel

/-! Exceptional hull positions for the tighter one-tenth-degree flatness threshold. -/

namespace Erdos957

open scoped BigOperators

/-- A full turn contains at most 3600 nonnegative turns of at least one tenth degree. -/
theorem card_large_turns_le_3600 {ι : Type*} [Fintype ι]
    (turn : ι → ℝ) (hnonneg : ∀ i, 0 ≤ turn i)
    (htotal : ∑ i, turn i ≤ 2 * Real.pi) :
    (Finset.univ.filter fun i => Real.pi / 1800 ≤ turn i).card ≤ 3600 := by
  classical
  let B := Finset.univ.filter fun i => Real.pi / 1800 ≤ turn i
  have hsmall : (B.card : ℝ) * (Real.pi / 1800) ≤ ∑ i ∈ B, turn i := by
    calc
      (B.card : ℝ) * (Real.pi / 1800) = ∑ _i ∈ B, Real.pi / 1800 := by simp
      _ ≤ ∑ i ∈ B, turn i := Finset.sum_le_sum fun i hi =>
        (Finset.mem_filter.mp hi).2
  have hsum : ∑ i ∈ B, turn i ≤ ∑ i, turn i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun i _ _ => hnonneg i)
  have hcard : (B.card : ℝ) ≤ 3600 := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hcard

/-- A radius-three cyclic neighborhood is exceptional when one of its seven
exterior angles is at least one tenth degree. -/
noncomputable def tightHullBadPositions {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun i => ∃ k : Fin 7,
    Real.pi / 1800 ≤ hullExteriorAngle p v
      (i + (Fin.ofNat h k.val - 3))

noncomputable def tightHullBadVertices {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) : Finset (Fin n) :=
  (tightHullBadPositions p v).image v

/-- Seven cyclic translates of the large-turn set contain at most 25200 positions. -/
theorem card_cyclic_tight_nonflat_le_25200 {h : ℕ} [NeZero h]
    (turn : Fin h → ℝ) (hnonneg : ∀ i, 0 ≤ turn i)
    (htotal : ∑ i, turn i ≤ 2 * Real.pi) :
    (Finset.univ.filter fun i => ∃ k : Fin 7,
      Real.pi / 1800 ≤ turn (i + (Fin.ofNat h k.val - 3))).card ≤ 25200 := by
  classical
  let B := Finset.univ.filter fun i => Real.pi / 1800 ≤ turn i
  have heq : (Finset.univ.filter fun i => ∃ k : Fin 7,
      Real.pi / 1800 ≤ turn (i + (Fin.ofNat h k.val - 3))) =
      Finset.univ.biUnion (fun k => B.image (sevenCyclicOffsets h k).symm) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, i + (Fin.ofNat h k.val - 3), ?_, ?_⟩
      · simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      · simp [sevenCyclicOffsets]; abel
    · rintro ⟨k, j, hj, hji⟩
      have hj' : Real.pi / 1800 ≤ turn j := by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have h : j = i + (Fin.ofNat h k.val - 3) := by
        rw [← hji]
        simp [sevenCyclicOffsets]; abel
      exact ⟨k, h ▸ hj'⟩
  rw [heq]
  have hbase : B.card ≤ 3600 :=
    card_large_turns_le_3600 turn hnonneg htotal
  exact (card_seven_neighborhoods_le B (sevenCyclicOffsets h)).trans
    (by omega)

/-- The actual exceptional hull positions obey the 25200 bound. -/
theorem tightHullBadPositions_card_le_25200 {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hnonneg : ∀ i, 0 ≤ hullExteriorAngle p v i)
    (hsum : ∑ i, hullExteriorAngle p v i ≤ 2 * Real.pi) :
    (tightHullBadPositions p v).card ≤ 25200 := by
  simpa only [tightHullBadPositions] using
    card_cyclic_tight_nonflat_le_25200 (hullExteriorAngle p v) hnonneg hsum

theorem tightHullBadVertices_card_le_25200 {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hnonneg : ∀ i, 0 ≤ hullExteriorAngle p v i)
    (hsum : ∑ i, hullExteriorAngle p v i ≤ 2 * Real.pi) :
    (tightHullBadVertices p v).card ≤ 25200 := by
  classical
  exact (Finset.card_image_le : (tightHullBadVertices p v).card ≤
    (tightHullBadPositions p v).card).trans
    (tightHullBadPositions_card_le_25200 p v hnonneg hsum)

theorem tightHullBadVertices_subset_hullVertexIndices {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n))) :
    tightHullBadVertices p v ⊆ hullVertexIndices p := by
  classical
  intro j hj
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  change v i ∈ (hullVertexIndices p : Set (Fin n))
  rw [← hrange]
  exact Set.mem_range_self i

/-- Outside the tight exceptional set, all seven nearby true hull exterior
angles are strictly below one tenth degree. -/
theorem tight_hull_vertex_not_bad_iff_all_seven_flat {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hv : Function.Injective v) (i : Fin h) :
    v i ∉ tightHullBadVertices p v ↔
      ∀ k : Fin 7,
        hullExteriorAngle p v (i + (Fin.ofNat h k.val - 3)) <
          Real.pi / 1800 := by
  classical
  have himage : v i ∈ tightHullBadVertices p v ↔
      i ∈ tightHullBadPositions p v := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have : j = i := hv hji
      simpa only [this] using hj
    · intro hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [not_iff_not.mpr himage]
  simp only [tightHullBadPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, not_exists, not_le]

/-- A noncollinear finite configuration has a true supporting hull order,
positive exterior angles summing to a full turn, and at most 25200 vertices
whose seven-position neighborhood fails the one-tenth-degree threshold. -/
theorem exists_tight_hull_bad_vertices_of_noncollinear {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    letI : NeZero (hullVertexCount p) :=
      ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      (∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k)) ∧
      (∀ i, 0 < hullExteriorAngle p v i ∧
        hullExteriorAngle p v i < Real.pi) ∧
      (∑ i, hullExteriorAngle p v i) = 2 * Real.pi ∧
      (tightHullBadVertices p v).card ≤ 25200 ∧
      tightHullBadVertices p v ⊆ hullVertexIndices p ∧
      (∀ i, v i ∉ tightHullBadVertices p v ↔
        ∀ k : Fin 7,
          hullExteriorAngle p v
            (i + (Fin.ofNat (hullVertexCount p) k.val - 3)) <
              Real.pi / 1800) := by
  classical
  have : NeZero (hullVertexCount p) :=
    ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
  obtain ⟨v, hv, hrange, hsupport, hpos, hsum, _⟩ :=
    exists_hull_exterior_angles_and_exception_bound p hn hp hnot
  refine ⟨v, hv, hrange, hsupport, hpos, hsum, ?_, ?_, ?_⟩
  · exact tightHullBadVertices_card_le_25200 p v
      (fun i => (hpos i).1.le) hsum.le
  · exact tightHullBadVertices_subset_hullVertexIndices p v hrange
  · intro i
    exact tight_hull_vertex_not_bad_iff_all_seven_flat p v hv i

end Erdos957
