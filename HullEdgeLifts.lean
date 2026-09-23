import HullCycle
import EdgeAngleLift

/-! Consistent real lifts of the actual cyclic hull edge directions. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Each actual hull edge direction has a real lift between the next radial
angle and a half-turn beyond the current radial angle. -/
theorem hull_edges_have_lifted_angles {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) (hh : 3 ≤ h)
    (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hmono : StrictMono (fun i => (pointToComplex (p (v i) - c)).arg)) :
    ∃ E : Fin h → ℝ,
      (∀ i, (pointToComplex (p (v (i + 1)) - c)).arg +
          (if i.val + 1 = h then 2 * Real.pi else 0) < E i ∧
        E i < (pointToComplex (p (v i) - c)).arg + Real.pi) ∧
      (∀ i, (E i : Real.Angle) =
        ((pointToComplex (p (v (i + 1)) - p (v i))).arg : Real.Angle)) := by
  let z : Fin h → ℂ := fun i => pointToComplex (p (v i) - c)
  have hcross (i : Fin h) : 0 < (conj (z i) * z (i + 1)).im := by
    have ht := hull_cycle_radial_turn_pos p c hc hh v hrange hmono i
    rwa [turn_eq_im_conj_mul] at ht
  have hne (i : Fin h) : z i ≠ 0 := by
    intro heq
    have ht := hcross i
    simp [heq] at ht
  have hdistinct (i : Fin h) : z (i + 1) ≠ z i := by
    intro heq
    have ht := hcross i
    rw [heq] at ht
    simp [Complex.mul_im, mul_comm] at ht
  let E : Fin h → ℝ := fun i => (z i).arg + ((z (i + 1) - z i) / z i).arg
  refine ⟨E, ?_, ?_⟩
  · intro i
    let δ := (z (i + 1)).arg + (if i.val + 1 = h then 2 * Real.pi else 0) -
      (z i).arg
    have hδ : 0 < δ ∧ δ < Real.pi := hull_cycle_radial_gap p c hc hh v hrange hmono i
    have hδangle : (δ : Real.Angle) =
        ((z (i + 1)).arg : Real.Angle) - ((z i).arg : Real.Angle) := by
      dsimp [δ]
      by_cases hlast : i.val + 1 = h <;>
        simp [hlast, Real.Angle.coe_two_pi]
    have hquot := arg_div_eq_of_short_lift (hne i) (hne (i + 1)) δ hδ hδangle
    have hbetween := edge_ratio_arg_between (hne i) (hcross i)
    rw [hquot] at hbetween
    change (z (i + 1)).arg + (if i.val + 1 = h then 2 * Real.pi else 0) < E i ∧
      E i < (z i).arg + Real.pi
    dsimp [E, δ] at *
    constructor <;> linarith [hbetween.2.1, hbetween.2.2]
  · intro i
    have hdir := edge_lift_coe_angle (hne i) (hdistinct i)
    have heq : z (i + 1) - z i = pointToComplex (p (v (i + 1)) - p (v i)) := by
      simp only [z, map_sub]
      abel
    change (E i : Real.Angle) = _ at hdir
    rwa [heq] at hdir

end Erdos957
