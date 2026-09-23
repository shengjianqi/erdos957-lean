import RadialSupport
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-! A strict orientation criterion for the interior of a planar triangle. -/

namespace Erdos957

private theorem continuous_turn_right (a b : Point) :
    Continuous (fun q : Point => turn a b q) := by
  unfold turn
  fun_prop

private theorem turn_cyclic_sum (a b c q : Point) :
    turn b c q + turn c a q + turn a b q = turn a b c := by
  unfold turn
  ring

/-- Strictly positive signed areas against all three directed sides place a
point in the ordinary topological interior of the triangle. -/
theorem triangle_strict_turns_mem_interior (a b c q : Point)
    (hdet : 0 < turn a b c)
    (hab : 0 < turn a b q)
    (hbc : 0 < turn b c q)
    (hca : 0 < turn c a q) :
    q ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
  classical
  let U : Set Point := {x | 0 < turn a b x ∧ 0 < turn b c x ∧ 0 < turn c a x}
  have hUopen : IsOpen U := by
    have ho₁ : IsOpen {x : Point | 0 < turn a b x} := by
      simpa [Set.preimage] using
        ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage (continuous_turn_right a b))
    have ho₂ : IsOpen {x : Point | 0 < turn b c x} := by
      simpa [Set.preimage] using
        ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage (continuous_turn_right b c))
    have ho₃ : IsOpen {x : Point | 0 < turn c a x} := by
      simpa [Set.preimage] using
        ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage (continuous_turn_right c a))
    simpa [U, Set.inter_def] using ho₁.inter (ho₂.inter ho₃)
  have hUsub : U ⊆ convexHull ℝ ({a, b, c} : Set Point) := by
    intro x hx
    rcases hx with ⟨habx, hbcx, hcax⟩
    let D : ℝ := turn a b c
    let u : ℝ := 1 - turn a x c / D - turn a b x / D
    let v : ℝ := turn a x c / D
    let w : ℝ := turn a b x / D
    have hcu : turn a x c = turn c a x := by
      unfold turn
      ring
    have huEq : u = turn b c x / D := by
      dsimp [u]
      rw [hcu]
      calc
        1 - turn c a x / D - turn a b x / D =
            (D - turn c a x - turn a b x) / D := by
          field_simp [D, hdet.ne']
        _ = turn b c x / D := by
          congr 1
          dsimp [D]
          linarith [turn_cyclic_sum a b c x]
    have hu : 0 ≤ u := by rw [huEq]; exact (div_pos hbcx hdet).le
    have hv : 0 ≤ v := by
      change 0 ≤ turn a x c / D
      rw [hcu]
      exact (div_pos hcax hdet).le
    have hw : 0 ≤ w := (div_pos habx hdet).le
    let coeff : Fin 3 → ℝ := ![u, v, w]
    let vertex : Fin 3 → Point := ![a, b, c]
    have hcoeff : ∀ i, 0 ≤ coeff i := by
      intro i
      fin_cases i <;> simpa [coeff] using (by first | exact hu | exact hv | exact hw)
    have hsum : ∑ i, coeff i = 1 := by
      simp [coeff, Fin.sum_univ_three, u, v, w]
      ring
    have hvertex : ∀ i, vertex i ∈ ({a, b, c} : Set Point) := by
      intro i
      fin_cases i <;> simp [vertex]
    have hrep : ∑ i, coeff i • vertex i = x := by
      have h := affine_coordinates_of_turn a b c x hdet.ne'
      simpa [coeff, vertex, Fin.sum_univ_three, u, v, w, D] using h.symm
    exact mem_convexHull_of_exists_fintype coeff vertex hcoeff hsum hvertex hrep
  exact mem_interior.mpr ⟨U, hUsub, hUopen, ⟨hab, hbc, hca⟩⟩

end Erdos957
