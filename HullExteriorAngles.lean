import HullCardinality
import HullEdgeLifts
import PolygonTurning
import FlatExceptionalCount

/-! Exterior angles of the true finite convex hull and its exceptional vertices. -/

namespace Erdos957

open scoped ComplexConjugate BigOperators

/-- The directed edge leaving vertex `i` in a cyclic enumeration. -/
noncomputable def hullEdgeDirection {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h) : ℂ :=
  pointToComplex (p (v (i + 1)) - p (v i))

/-- The principal positive exterior angle at vertex `i`, from its incoming
edge to its outgoing edge. Positivity is proved for the actual hull below. -/
noncomputable def hullExteriorAngle {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h) : ℝ :=
  (hullEdgeDirection p v i / hullEdgeDirection p v (i - 1)).arg

/-- The real exterior angles of a cyclic supporting hull order are positive,
less than π, and sum to exactly one full turn. -/
theorem hull_exterior_angles_of_order {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) (hh : 3 ≤ h)
    (v : Fin h → Fin n) (hv : Function.Injective v)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hmono : StrictMono (fun i => (pointToComplex (p (v i) - c)).arg))
    (hsupport : ∀ s t, (s.val + 1 = t.val ∨
        (s.val + 1 = h ∧ t.val = 0)) →
      ∀ k : Fin n, 0 ≤ turn (p (v s)) (p (v t)) (p k)) :
    (∀ i, 0 < hullExteriorAngle p v i ∧ hullExteriorAngle p v i < Real.pi) ∧
      ∑ i, hullExteriorAngle p v i = 2 * Real.pi := by
  obtain ⟨E, hbetween, hE⟩ := hull_edges_have_lifted_angles p c hc hh v hrange hmono
  let θ : Fin h → ℝ := fun i => (pointToComplex (p (v i) - c)).arg
  have hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi := by
    have hlo := (Complex.arg_mem_Ioc (pointToComplex (p (v ⟨0, by omega⟩) - c))).1
    have hhi := (Complex.arg_mem_Ioc (pointToComplex (p (v ⟨h - 1, by omega⟩) - c))).2
    change (pointToComplex (p (v ⟨h - 1, by omega⟩) - c)).arg -
      (pointToComplex (p (v ⟨0, by omega⟩) - c)).arg < 2 * Real.pi
    linarith only [hlo, hhi]
  have hmem (i) : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  have hcross (i : Fin h) :
      0 < (conj (hullEdgeDirection p v i) *
        hullEdgeDirection p v (cyclicNext i)).im := by
    have ht := hull_cycle_edge_turn_pos p hp hh v hv hmem hsupport i
    rw [turn_eq_im_conj_mul_edges] at ht
    simpa only [hullEdgeDirection, cyclicNext] using ht
  have hbounds : ∀ i, wrapLift θ i < E i ∧ E i < θ i + Real.pi := by
    simpa only [wrapLift, cyclicNext, θ] using hbetween
  exact polygon_vertex_exterior_angles hh θ E (hullEdgeDirection p v)
    hmono hspan hbounds hE hcross

/-- Every noncollinear injective finite configuration has a genuine hull
enumeration with positive exterior angles summing to 2π. The actual seven
position nonflat-neighborhood set then has size at most 2520. -/
theorem exists_hull_exterior_angles_and_exception_bound {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    letI : NeZero (hullVertexCount p) :=
      ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      (∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k)) ∧
      (∀ i, 0 < hullExteriorAngle p v i ∧ hullExteriorAngle p v i < Real.pi) ∧
      (∑ i, hullExteriorAngle p v i) = 2 * Real.pi ∧
      (Finset.univ.filter fun i => ∃ k : Fin 7,
        Real.pi / 180 ≤ hullExteriorAngle p v
          (i + (Fin.ofNat (hullVertexCount p) k.val - 3))).card ≤ 2520 := by
  classical
  have hh := hullVertexCount_ge_three_of_noncollinear p hnot
  have : NeZero (hullVertexCount p) := ⟨by omega⟩
  obtain ⟨c, hc, v, hv, hrange, hmono, hsupport⟩ :=
    exists_hull_cyclic_supporting_order p hn hp hnot
  obtain ⟨hpos, hsum⟩ := hull_exterior_angles_of_order p hp c hc hh v hv hrange hmono hsupport
  refine ⟨v, hv, hrange, ?_, hpos, hsum, ?_⟩
  · intro i k
    exact hsupport i (i + 1) (cyclic_index_cases (by omega) i) k
  · exact card_cyclic_nonflat_le_2520 (hullExteriorAngle p v)
      (fun i => (hpos i).1.le) hsum.le

end Erdos957
