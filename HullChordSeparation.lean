import HullChordAdjacency

/-! A nonadjacent hull chord strictly separates the two neighboring hull
vertices at its initial endpoint.  Consequently one local sign test suffices
to recognize a supported hull edge. -/

namespace Erdos957

private theorem turn_cyclic (a b c : Point) : turn a b c = turn b c a := by
  simp only [turn]
  ring

/-- Every distinct hull endpoint other than the successor lies strictly on
the opposite side of the chord from the successor. -/
theorem hull_chord_successor_turn_neg {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i) (hwnext : w ≠ v (i + 1)) :
    turn (p (v i)) (p w) (p (v (i + 1))) < 0 := by
  classical
  have hmem (j : Fin h) : v j ∈ hullVertexIndices p := by
    change v j ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self j
  have hstrict := supporting_edge_strict p hp
    (Finset.mem_filter.mp (hmem i)).2
    (Finset.mem_filter.mp (hmem (i + 1))).2
    (Finset.mem_filter.mp hw).2
    (hv.ne (cyclic_three_distinct hh i).1) hwne hwnext (hsupport i)
  rw [turn_swap]
  linarith

/-- Every distinct hull endpoint other than the predecessor lies strictly
on the same side of the oriented chord as the predecessor. -/
theorem hull_chord_predecessor_turn_pos {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i) (hwprev : w ≠ v (i - 1)) :
    0 < turn (p (v i)) (p w) (p (v (i - 1))) := by
  classical
  have hmem (j : Fin h) : v j ∈ hullVertexIndices p := by
    change v j ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self j
  have hnext : i - 1 + 1 = i := by simp
  have hne : v (i - 1) ≠ v i := by
    have ht := hv.ne (cyclic_three_distinct hh (i - 1)).1
    simpa only [hnext] using ht
  have hstrict := supporting_edge_strict p hp
    (Finset.mem_filter.mp (hmem (i - 1))).2
    (Finset.mem_filter.mp (hmem i)).2
    (Finset.mem_filter.mp hw).2 hne hwprev hwne (by
      simpa only [hnext] using hsupport (i - 1))
  rwa [turn_cyclic] at hstrict

/-- A nonadjacent hull chord separates the predecessor and successor
strictly; the statement has no unproved locality assumption. -/
theorem nonadjacent_hull_chord_separates_neighbors {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i) (hwnext : w ≠ v (i + 1))
    (hwprev : w ≠ v (i - 1)) :
    0 < turn (p (v i)) (p w) (p (v (i - 1))) ∧
    turn (p (v i)) (p w) (p (v (i + 1))) < 0 := by
  exact ⟨hull_chord_predecessor_turn_pos p hp v hv hh hrange hsupport
    i w hw hwne hwprev,
    hull_chord_successor_turn_neg p hp v hv hh hrange hsupport
    i w hw hwne hwnext⟩

/-- A nonnegative turn at the successor already identifies the chord as
the oriented successor edge. -/
theorem hull_chord_eq_successor_of_local_turn {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hlocal : 0 ≤ turn (p (v i)) (p w) (p (v (i + 1)))) :
    w = v (i + 1) := by
  by_contra hwnext
  have ht := hull_chord_successor_turn_neg p hp v hv hh hrange hsupport
    i w hw hwne hwnext
  linarith

/-- A nonpositive turn at the predecessor already identifies the chord
as the predecessor edge with its reversed orientation. -/
theorem hull_chord_eq_predecessor_of_local_turn {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hlocal : turn (p (v i)) (p w) (p (v (i - 1))) ≤ 0) :
    w = v (i - 1) := by
  by_contra hwprev
  have ht := hull_chord_predecessor_turn_pos p hp v hv hh hrange hsupport
    i w hw hwne hwprev
  linarith

/-- The two adjacent hull vertices being on the same weak side of a
chord forces its endpoints to be cyclically adjacent. -/
theorem hull_chord_adjacent_of_neighbors_same_side {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hsame : (0 ≤ turn (p (v i)) (p w) (p (v (i - 1))) ∧
        0 ≤ turn (p (v i)) (p w) (p (v (i + 1)))) ∨
      (turn (p (v i)) (p w) (p (v (i - 1))) ≤ 0 ∧
        turn (p (v i)) (p w) (p (v (i + 1))) ≤ 0)) :
    w = v (i + 1) ∨ w = v (i - 1) := by
  rcases hsame with hleft | hright
  · exact Or.inl (hull_chord_eq_successor_of_local_turn p hp v hv hh hrange
      hsupport i w hw hwne hleft.2)
  · exact Or.inr (hull_chord_eq_predecessor_of_local_turn p hp v hv hh hrange
      hsupport i w hw hwne hright.1)

/-- The same local condition supplies a supporting orientation for all
configuration points, not only for hull vertices. -/
theorem hull_chord_support_of_neighbors_same_side {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (i : Fin h) (w : Fin n) (hw : w ∈ hullVertexIndices p)
    (hwne : w ≠ v i)
    (hsame : (0 ≤ turn (p (v i)) (p w) (p (v (i - 1))) ∧
        0 ≤ turn (p (v i)) (p w) (p (v (i + 1)))) ∨
      (turn (p (v i)) (p w) (p (v (i - 1))) ≤ 0 ∧
        turn (p (v i)) (p w) (p (v (i + 1))) ≤ 0)) :
    (∀ k, 0 ≤ turn (p (v i)) (p w) (p k)) ∨
      (∀ k, 0 ≤ turn (p w) (p (v i)) (p k)) := by
  rcases hull_chord_adjacent_of_neighbors_same_side p hp v hv hh hrange
      hsupport i w hw hwne hsame with hnext | hprev
  · exact Or.inl (hnext ▸ hsupport i)
  · right
    rw [hprev]
    simpa only [sub_add_cancel] using hsupport (i - 1)

end Erdos957
