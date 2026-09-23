import ShortEdgeChain
import NormalizedHullEdges
import Mathlib.Tactic.Linarith

/-! Short turns of the actual cyclic hull yield short relative edge directions. -/

namespace Erdos957

/-- The five nearby hull edges make at most a three-tenths-degree angle with the
chosen edge when the five intervening exterior turns are each tiny. -/
theorem tight_hull_nearby_edge_args {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hi : hullExteriorAngle p v i < Real.pi / 1800)
    (him1 : hullExteriorAngle p v (i - 1) < Real.pi / 1800)
    (him2 : hullExteriorAngle p v ((i - 1) - 1) < Real.pi / 1800)
    (hip1 : hullExteriorAngle p v (i + 1) < Real.pi / 1800)
    (hip2 : hullExteriorAngle p v ((i + 1) + 1) < Real.pi / 1800) :
    ∀ j : Fin h,
      (j = i + 1 ∨ j = (i + 1) + 1 ∨ j = i - 1 ∨
        j = (i - 1) - 1 ∨ j = ((i - 1) - 1) - 1) →
      |(hullEdgeDirection p v j / hullEdgeDirection p v i).arg| ≤ Real.pi / 600 := by
  let e : Fin h → ℂ := hullEdgeDirection p v
  have he (j : Fin h) : e j ≠ 0 := hullEdgeDirection_ne_zero p hp v hv hh j
  have hstep (j : Fin h) (hsmall : hullExteriorAngle p v j < Real.pi / 1800) :
      0 < (e j / e (j - 1)).arg ∧
        (e j / e (j - 1)).arg < Real.pi / 1800 := by
    exact ⟨hpos j, hsmall⟩
  have hs1 : 0 < (e (i + 1) / e i).arg ∧
      (e (i + 1) / e i).arg < Real.pi / 1800 := by
    simpa only [show (i + 1) - 1 = i by abel] using hstep (i + 1) hip1
  have hs2 : 0 < (e ((i + 1) + 1) / e (i + 1)).arg ∧
      (e ((i + 1) + 1) / e (i + 1)).arg < Real.pi / 1800 := by
    simpa only [show ((i + 1) + 1) - 1 = i + 1 by abel] using
      hstep ((i + 1) + 1) hip2
  have hsM1 : 0 < (e i / e (i - 1)).arg ∧
      (e i / e (i - 1)).arg < Real.pi / 1800 := hstep i hi
  have hsM2 : 0 < (e (i - 1) / e ((i - 1) - 1)).arg ∧
      (e (i - 1) / e ((i - 1) - 1)).arg < Real.pi / 1800 := hstep (i - 1) him1
  have hsM3 : 0 < (e ((i - 1) - 1) / e (((i - 1) - 1) - 1)).arg ∧
      (e ((i - 1) - 1) / e (((i - 1) - 1) - 1)).arg < Real.pi / 1800 :=
    hstep ((i - 1) - 1) him2
  have hL2 := arg_div_short_chain_two (he i) (he (i + 1))
    (he ((i + 1) + 1)) hs1 hs2
  have hR2 := arg_div_short_chain_two (he ((i - 1) - 1)) (he (i - 1))
    (he i) hsM2 hsM1
  have hR3 := arg_div_short_chain_three (he (((i - 1) - 1) - 1))
    (he ((i - 1) - 1)) (he (i - 1)) (he i) hsM3 hsM2 hsM1
  have hbound {z w : ℂ} (ha : 0 < (w / z).arg)
      (hb : (w / z).arg < 3 * (Real.pi / 1800)) :
      |(z / w).arg| ≤ Real.pi / 600 := by
    rw [abs_arg_div_reverse_eq z w, abs_of_pos ha]
    linarith [hb]
  have hL1bound : |(e (i + 1) / e i).arg| ≤ Real.pi / 600 := by
    rw [abs_of_pos hs1.1]
    linarith [hs1.2, Real.pi_pos]
  have hL2bound : |(e ((i + 1) + 1) / e i).arg| ≤ Real.pi / 600 := by
    rw [abs_of_pos hL2.1]
    linarith [hL2.2]
  have hR1bound : |(e (i - 1) / e i).arg| ≤ Real.pi / 600 :=
    hbound hsM1.1 (by linarith [hsM1.2, Real.pi_pos])
  have hR2bound : |(e ((i - 1) - 1) / e i).arg| ≤ Real.pi / 600 :=
    hbound hR2.1 (by linarith [hR2.2])
  have hR3bound : |(e (((i - 1) - 1) - 1) / e i).arg| ≤ Real.pi / 600 :=
    hbound hR3.1 hR3.2
  intro j hj
  rcases hj with hj | hj | hj | hj | hj
  · simpa only [e, hj] using hL1bound
  · simpa only [e, hj] using hL2bound
  · simpa only [e, hj] using hR1bound
  · simpa only [e, hj] using hR2bound
  · simpa only [e, hj] using hR3bound

end Erdos957
