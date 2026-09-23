import HullAngularGaps
import HullInterior
import WrappedSector

/-! Actual cyclic hull order with a supporting line at every consecutive edge. -/

namespace Erdos957

private theorem hull_vertex_ne_center {n : ℕ} (p : Fin n → Point)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i : Fin n) (hi : i ∈ hullVertexIndices p) : p i ≠ c := by
  classical
  have he := (Finset.mem_filter.mp hi).2
  intro h
  exact Set.disjoint_left.mp (disjoint_interior_extremePoints
    (convexHull ℝ (Set.range p))) hc (h ▸ he)

/-- Consecutive principal arguments give a supporting chord, with the short
angular gap derived from the actual hull rather than assumed. -/
theorem supporting_chord_of_adjacent_args {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j : Fin n) (hi : i ∈ hullVertexIndices p) (hj : j ∈ hullVertexIndices p)
    (harg : (pointToComplex (p i - c)).arg < (pointToComplex (p j - c)).arg)
    (hempty : ∀ k ∈ hullVertexIndices p,
      ¬ ((pointToComplex (p i - c)).arg < (pointToComplex (p k - c)).arg ∧
         (pointToComplex (p k - c)).arg < (pointToComplex (p j - c)).arg)) :
    ∀ k : Fin n, 0 ≤ turn (p i) (p j) (p k) := by
  classical
  have hgap := hull_adjacent_arg_gap_lt_pi p c hc i j hi hj harg hempty
  have hic := hull_vertex_ne_center p c hc i hi
  have hjc := hull_vertex_ne_center p c hc j hj
  apply supporting_chord_of_empty_radial_sector p hn hp c hc i j
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    (turn_pos_of_arg_gap c (p i) (p j) hic hjc harg hgap)
  intro k hk ht
  exact hempty k hk (radial_sector_arg_between c (p i) (p j) (p k)
    hic hjc (hull_vertex_ne_center p c hc k hk) harg hgap ht.1 ht.2)

/-- The chord from largest to smallest principal argument supports the hull. -/
theorem supporting_chord_of_extremal_args {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j : Fin n) (hi : i ∈ hullVertexIndices p) (hj : j ∈ hullVertexIndices p)
    (hmin : ∀ k ∈ hullVertexIndices p,
      (pointToComplex (p j - c)).arg ≤ (pointToComplex (p k - c)).arg)
    (hmax : ∀ k ∈ hullVertexIndices p,
      (pointToComplex (p k - c)).arg ≤ (pointToComplex (p i - c)).arg) :
    ∀ k : Fin n, 0 ≤ turn (p i) (p j) (p k) := by
  classical
  have hspan := hull_arg_extremal_span_gt_pi p c hc j i hj hi hmin hmax
  apply supporting_chord_of_empty_radial_sector p hn hp c hc i j
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    (turn_pos_of_wrapped_arg_gap c (p i) (p j)
      (hull_vertex_ne_center p c hc i hi) (hull_vertex_ne_center p c hc j hj) hspan)
  intro k hk
  exact not_two_pos_turns_of_wrapped_arg_between c (p i) (p j) (p k)
    (hmin k hk) (hmax k hk)

/-- The actual extreme vertices have an angular enumeration whose successive
chords, including the closing chord, support the whole configuration. -/
theorem hull_cyclic_supporting_order {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p))) :
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      StrictMono (fun i => (pointToComplex (p (v i) - c)).arg) ∧
      (∀ s t, (s.val + 1 = t.val ∨
          (s.val + 1 = hullVertexCount p ∧ t.val = 0)) →
        ∀ k : Fin n, 0 ≤ turn (p (v s)) (p (v t)) (p k)) := by
  obtain ⟨v, hvinj, hrange, hmono, _⟩ := hull_extreme_radial_order p hp c hc
  have hmem (i) : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  refine ⟨v, hvinj, hrange, hmono, ?_⟩
  intro s t hnext
  rcases hnext with hstep | ⟨hlast, hfirst⟩
  · have hst : s < t := by change s.val < t.val; omega
    apply supporting_chord_of_adjacent_args p hn hp c hc (v s) (v t)
      (hmem s) (hmem t) (hmono hst)
    intro k hk hbetween
    have hkrange : k ∈ Set.range v := by rw [hrange]; exact hk
    obtain ⟨u, rfl⟩ := hkrange
    have hsu : s < u := hmono.lt_iff_lt.mp hbetween.1
    have hut : u < t := hmono.lt_iff_lt.mp hbetween.2
    change s.val < u.val at hsu
    change u.val < t.val at hut
    omega
  · apply supporting_chord_of_extremal_args p hn hp c hc (v s) (v t)
      (hmem s) (hmem t)
    · intro k hk
      have hkrange : k ∈ Set.range v := by rw [hrange]; exact hk
      obtain ⟨u, rfl⟩ := hkrange
      apply hmono.monotone
      change t.val ≤ u.val
      omega
    · intro k hk
      have hkrange : k ∈ Set.range v := by rw [hrange]; exact hk
      obtain ⟨u, rfl⟩ := hkrange
      apply hmono.monotone
      change u.val ≤ s.val
      omega

/-- A noncollinear finite configuration has a genuine cyclic supporting hull
order, with an interior center constructed from noncollinearity. -/
theorem exists_hull_cyclic_supporting_order {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    ∃ c : Point, c ∈ interior (convexHull ℝ (Set.range p)) ∧
      ∃ v : Fin (hullVertexCount p) → Fin n,
        Function.Injective v ∧
        Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
        StrictMono (fun i => (pointToComplex (p (v i) - c)).arg) ∧
        (∀ s t, (s.val + 1 = t.val ∨
            (s.val + 1 = hullVertexCount p ∧ t.val = 0)) →
          ∀ k : Fin n, 0 ≤ turn (p (v s)) (p (v t)) (p k)) := by
  obtain ⟨c, hc⟩ := hull_interior_nonempty_of_not_collinear p hn hnot
  exact ⟨c, hc, hull_cyclic_supporting_order p hn hp c hc⟩

end Erdos957
