import HullCycle

/-! A supporting chord between actual hull vertices has consecutive cyclic
indices. This does not assert support for arbitrary nearest-neighbor chords. -/

namespace Erdos957

/-- An oriented supporting chord from a hull vertex ends at its successor
in any injective cyclic order with the same support orientation. -/
theorem supporting_hull_chord_eq_successor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hchord : ∀ k, 0 ≤ turn (p (v i)) (p w) (p k)) :
    w = v (i + 1) := by
  classical
  have hmem (j : Fin h) : v j ∈ hullVertexIndices p := by
    change v j ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self j
  by_contra hne
  have hstrict := supporting_edge_strict p hp
    (Finset.mem_filter.mp (hmem i)).2
    (Finset.mem_filter.mp (hmem (i + 1))).2
    (Finset.mem_filter.mp hw).2
    (hv.ne (cyclic_three_distinct hh i).1) hwne hne (hsupport i)
  have hnonneg := hchord (v (i + 1))
  rw [turn_swap] at hnonneg
  linarith

/-- A chord supported with the reverse orientation ends at the predecessor. -/
theorem supporting_hull_chord_eq_predecessor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hchord : ∀ k, 0 ≤ turn (p w) (p (v i)) (p k)) :
    w = v (i - 1) := by
  have hwrange : w ∈ Set.range v := by rw [hrange]; exact hw
  obtain ⟨j, rfl⟩ := hwrange
  have hi : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  have hnext := supporting_hull_chord_eq_successor p hp v hv hh hrange hsupport
    j (v i) hi (Ne.symm hwne) hchord
  have hij : i = j + 1 := hv hnext
  have hj : j = i - 1 := by rw [hij]; simp
  rw [hj]

/-- A line through two distinct hull vertices that supports the entire
configuration joins adjacent positions of the actual cyclic hull order. -/
theorem supporting_hull_chord_cyclic_adjacent {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hchord : (∀ k, 0 ≤ turn (p (v i)) (p w) (p k)) ∨
      (∀ k, 0 ≤ turn (p w) (p (v i)) (p k))) :
    w = v (i + 1) ∨ w = v (i - 1) := by
  rcases hchord with hforward | hreverse
  · exact Or.inl (supporting_hull_chord_eq_successor p hp v hv hh hrange
      hsupport i w hw hwne hforward)
  · exact Or.inr (supporting_hull_chord_eq_predecessor p hp v hv hh hrange
      hsupport i w hw hwne hreverse)

end Erdos957
