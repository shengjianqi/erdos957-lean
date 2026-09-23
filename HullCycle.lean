import HullEdgeOrder
import HullStrictTurn
import Mathlib.Algebra.Group.Fin.Basic

/-! Modular indexing and strict turns for the actual supporting hull order. -/

namespace Erdos957

theorem cyclic_index_cases {h : ℕ} [NeZero h] (hh : 2 ≤ h) (i : Fin h) :
    i.val + 1 = (i + 1).val ∨ (i.val + 1 = h ∧ (i + 1).val = 0) := by
  have hv : (i + 1).val = (i.val + 1) % h := by
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < h)]
  by_cases hlt : i.val + 1 < h
  · left
    rw [hv, Nat.mod_eq_of_lt hlt]
  · right
    have heq : i.val + 1 = h := by omega
    exact ⟨heq, by rw [hv, heq, Nat.mod_self]⟩

theorem cyclic_three_distinct {h : ℕ} [NeZero h] (hh : 3 ≤ h) (i : Fin h) :
    i ≠ i + 1 ∧ (i + 1) + 1 ≠ i ∧ (i + 1) + 1 ≠ i + 1 := by
  have hne (j : Fin h) : j ≠ j + 1 := by
    intro heq
    have hv := congrArg Fin.val heq
    rcases cyclic_index_cases (by omega : 2 ≤ h) j with hs | ⟨hl, hf⟩ <;> omega
  refine ⟨hne i, ?_, (hne (i + 1)).symm⟩
  intro heq
  have hv := congrArg Fin.val heq
  rcases cyclic_index_cases (by omega : 2 ≤ h) i with hs | ⟨hl, hf⟩ <;>
    rcases cyclic_index_cases (by omega : 2 ≤ h) (i + 1) with hs' | ⟨hl', hf'⟩ <;>
    omega

theorem hull_cycle_edge_turn_pos {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hh : 3 ≤ h)
    (v : Fin h → Fin n) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ hullVertexIndices p)
    (hsupport : ∀ s t, (s.val + 1 = t.val ∨
        (s.val + 1 = h ∧ t.val = 0)) →
      ∀ k : Fin n, 0 ≤ turn (p (v s)) (p (v t)) (p k)) :
    ∀ i, 0 < turn (p (v i)) (p (v (i + 1))) (p (v ((i + 1) + 1))) := by
  classical
  intro i
  have hdist := cyclic_three_distinct hh i
  apply supporting_edge_strict p hp
    (Finset.mem_filter.mp (hmem i)).2
    (Finset.mem_filter.mp (hmem (i + 1))).2
    (Finset.mem_filter.mp (hmem ((i + 1) + 1))).2
    (hv.ne hdist.1) (hv.ne hdist.2.1) (hv.ne hdist.2.2)
  exact hsupport i (i + 1) (cyclic_index_cases (by omega) i)

/-- The true radial gaps, lifted across the closing edge, lie in (0,π). -/
theorem hull_cycle_radial_gap {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) (hh : 3 ≤ h)
    (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hmono : StrictMono (fun i => (pointToComplex (p (v i) - c)).arg)) :
    ∀ i, 0 < (pointToComplex (p (v (i + 1)) - c)).arg +
        (if i.val + 1 = h then 2 * Real.pi else 0) -
        (pointToComplex (p (v i) - c)).arg ∧
      (pointToComplex (p (v (i + 1)) - c)).arg +
        (if i.val + 1 = h then 2 * Real.pi else 0) -
        (pointToComplex (p (v i) - c)).arg < Real.pi := by
  have hmem (i) : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  intro i
  rcases cyclic_index_cases (by omega : 2 ≤ h) i with hs | ⟨hl, hf⟩
  · have hnlast : i.val + 1 ≠ h := by have := (i + 1).isLt; omega
    simp only [hnlast, ↓reduceIte, add_zero]
    have hlt : i < i + 1 := by change i.val < (i + 1).val; omega
    refine ⟨sub_pos.mpr (hmono hlt), ?_⟩
    apply hull_adjacent_arg_gap_lt_pi p c hc (v i) (v (i + 1))
      (hmem i) (hmem (i + 1)) (hmono hlt)
    intro k hk hbetween
    have hk' : k ∈ Set.range v := by rw [hrange]; exact hk
    obtain ⟨j, rfl⟩ := hk'
    have hleft := hmono.lt_iff_lt.mp hbetween.1
    have hright := hmono.lt_iff_lt.mp hbetween.2
    change i.val < j.val at hleft
    change j.val < (i + 1).val at hright
    omega
  · simp only [hl, ↓reduceIte]
    have hspan := hull_arg_extremal_span_gt_pi p c hc (v (i + 1)) (v i)
      (hmem (i + 1)) (hmem i) (by
        intro k hk
        have hk' : k ∈ Set.range v := by rw [hrange]; exact hk
        obtain ⟨j, rfl⟩ := hk'
        apply hmono.monotone
        change (i + 1).val ≤ j.val
        omega) (by
        intro k hk
        have hk' : k ∈ Set.range v := by rw [hrange]; exact hk
        obtain ⟨j, rfl⟩ := hk'
        apply hmono.monotone
        change j.val ≤ i.val
        omega)
    have hlow := (Complex.arg_mem_Ioc (pointToComplex (p (v (i + 1)) - c))).1
    have hhigh := (Complex.arg_mem_Ioc (pointToComplex (p (v i) - c))).2
    constructor <;> linarith

/-- Consecutive hull rays have strictly positive signed area. -/
theorem hull_cycle_radial_turn_pos {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) (hh : 3 ≤ h)
    (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hmono : StrictMono (fun i => (pointToComplex (p (v i) - c)).arg)) :
    ∀ i, 0 < turn c (p (v i)) (p (v (i + 1))) := by
  classical
  have hne (i) : p (v i) ≠ c := by
    have hmem : v i ∈ hullVertexIndices p := by
      change v i ∈ (hullVertexIndices p : Set (Fin n))
      rw [← hrange]
      exact Set.mem_range_self i
    have hext := (Finset.mem_filter.mp hmem).2
    intro heq
    exact Set.disjoint_left.mp (disjoint_interior_extremePoints
      (convexHull ℝ (Set.range p))) hc (heq ▸ hext)
  intro i
  have hgap := hull_cycle_radial_gap p c hc hh v hrange hmono i
  by_cases hlast : i.val + 1 = h
  · simp only [hlast, ↓reduceIte] at hgap
    apply turn_pos_of_wrapped_arg_gap c _ _ (hne i) (hne (i + 1))
    linarith [hgap.2]
  · simp only [hlast, ↓reduceIte, add_zero] at hgap
    exact turn_pos_of_arg_gap c _ _ (hne i) (hne (i + 1))
      (sub_pos.mp hgap.1) hgap.2

end Erdos957
