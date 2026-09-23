import TightHullDirections
import TightFlatOffsets
import SmallAngleProjection

/-! Eight actual hull edges controlled by the existing seven-turn exceptional
set, together with a sharper estimate for the immediately preceding edge. -/

namespace Erdos957

open Fin.NatCast

private theorem projection_trig_bounds (θ : ℝ) (hθ : |θ| ≤ (1 / 75 : ℝ)) :
    (99 / 100 : ℝ) ≤ Real.cos θ ∧ |Real.sin θ| ≤ Real.cos θ / 30 := by
  have hu : θ ≤ (1 / 75 : ℝ) := (le_abs_self θ).trans hθ
  have hl : -(1 / 75 : ℝ) ≤ θ := neg_le_of_abs_le hθ
  have hp : 0 ≤ ((1 / 75 : ℝ) - θ) * ((1 / 75 : ℝ) + θ) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : θ ^ 2 ≤ (1 / 75 : ℝ) ^ 2 := by nlinarith
  have hcos : (99 / 100 : ℝ) ≤ Real.cos θ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hsin : |Real.sin θ| ≤ (1 / 75 : ℝ) := Real.abs_sin_le_abs.trans hθ
  exact ⟨hcos, by linarith⟩

/-- The wider angle bound still gives a 99-percent horizontal projection and
vertical slope at most one thirtieth. -/
theorem extended_small_arg_projection (z : ℂ)
    (harg : |z.arg| ≤ Real.pi / 300) :
    (99 / 100 : ℝ) * ‖z‖ ≤ z.re ∧ |z.im| ≤ z.re / 30 := by
  have hb : |z.arg| ≤ (1 / 75 : ℝ) := by linarith [Real.pi_le_four]
  obtain ⟨hcos, hsin⟩ := projection_trig_bounds z.arg hb
  have hre : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have him : z.im = ‖z‖ * Real.sin z.arg := (Complex.norm_mul_sin_arg z).symm
  have hn := norm_nonneg z
  constructor
  · rw [hre]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcos hn
  · rw [him, hre, abs_mul, abs_of_nonneg hn]
    nlinarith [mul_le_mul_of_nonneg_left hsin hn]

/-- A single tiny exterior turn has slope at most one hundredth. -/
theorem tiny_arg_projection (z : ℂ)
    (harg : |z.arg| ≤ Real.pi / 1800) :
    (99 / 100 : ℝ) * ‖z‖ ≤ z.re ∧ |z.im| ≤ z.re / 100 := by
  have hb : |z.arg| ≤ (1 / 450 : ℝ) := by linarith [Real.pi_le_four]
  have hcos := (projection_trig_bounds z.arg (by linarith :
    |z.arg| ≤ (1 / 75 : ℝ))).1
  have hs : |Real.sin z.arg| ≤ (1 / 450 : ℝ) := Real.abs_sin_le_abs.trans hb
  have hsin : |Real.sin z.arg| ≤ Real.cos z.arg / 100 := by linarith
  have hre : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have him : z.im = ‖z‖ * Real.sin z.arg := (Complex.norm_mul_sin_arg z).symm
  have hn := norm_nonneg z
  constructor
  · rw [hre]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcos hn
  · rw [him, hre, abs_mul, abs_of_nonneg hn]
    nlinarith [mul_le_mul_of_nonneg_left hsin hn]

/-- Four successive tiny positive turns remain in the principal branch. -/
theorem arg_div_short_chain_four {z0 z1 z2 z3 z4 : ℂ}
    (hz0 : z0 ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0)
    (h01 : 0 < (z1 / z0).arg ∧ (z1 / z0).arg < Real.pi / 1800)
    (h12 : 0 < (z2 / z1).arg ∧ (z2 / z1).arg < Real.pi / 1800)
    (h23 : 0 < (z3 / z2).arg ∧ (z3 / z2).arg < Real.pi / 1800)
    (h34 : 0 < (z4 / z3).arg ∧ (z4 / z3).arg < Real.pi / 1800) :
    0 < (z4 / z0).arg ∧ (z4 / z0).arg < 4 * (Real.pi / 1800) := by
  have h03 := arg_div_short_chain_three hz0 hz1 hz2 hz3 h01 h12 h23
  let δ : ℝ := (z3 / z0).arg + (z4 / z3).arg
  have hδ : 0 < δ ∧ δ < Real.pi := by
    dsimp [δ]
    constructor
    · linarith [h03.1, h34.1]
    · linarith [h03.2, h34.2, Real.pi_pos]
  have hangle : (δ : Real.Angle) =
      (z4.arg : Real.Angle) - (z0.arg : Real.Angle) := by
    dsimp [δ]
    rw [Complex.arg_div_coe_angle hz3 hz0, Complex.arg_div_coe_angle hz4 hz3]
    abel
  rw [arg_div_eq_of_short_lift hz0 hz4 δ hδ hangle]
  dsimp [δ]
  constructor
  · linarith [h03.1, h34.1]
  · linarith [h03.2, h34.2]

/-- The radius-three exceptional set also controls the two outermost turns
needed for the eight-edge chain. -/
theorem tight_hull_outer_turns_of_not_bad {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (hv : Function.Injective v)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v) :
    hullExteriorAngle p v (((i - 1) - 1) - 1) < Real.pi / 1800 ∧
      hullExteriorAngle p v (((i + 1) + 1) + 1) < Real.pi / 1800 := by
  have hall := (tight_hull_vertex_not_bad_iff_all_seven_flat p v hv i).mp hgood
  have hc3 : (3 : Fin h) = 1 + 1 + 1 := by
    calc
      (3 : Fin h) = (((1 + 1) + 1 : ℕ) : Fin h) := by norm_num
      _ = 1 + 1 + 1 := by rw [Nat.cast_add, Nat.cast_add]; norm_num
  have hc6 : (6 : Fin h) = 3 + 3 := by
    calc
      (6 : Fin h) = ((3 + 3 : ℕ) : Fin h) := by norm_num
      _ = 3 + 3 := by rw [Nat.cast_add]; norm_num
  have h0 : i + (Fin.ofNat h 0 - 3) = ((i - 1) - 1) - 1 := by
    rw [Fin.ofNat_eq_cast]
    simp only [Nat.cast_zero, zero_sub]
    rw [hc3]
    abel
  have h6 : i + (Fin.ofNat h 6 - 3) = ((i + 1) + 1) + 1 := by
    rw [Fin.ofNat_eq_cast]
    simp only [Nat.cast_ofNat]
    rw [hc6, hc3]
    abel
  exact ⟨by simpa only [h0] using hall (⟨0, by decide⟩ : Fin 7),
    by simpa only [h6] using hall (⟨6, by decide⟩ : Fin 7)⟩

/-- The eight edges from offset minus four through plus three are nearly
parallel to the outgoing edge. The outgoing edge need not be a nearest edge. -/
theorem tight_hull_eight_edge_args {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v)
    (j : Fin h)
    (hj : j = (((i - 1) - 1) - 1) - 1 ∨ j = ((i - 1) - 1) - 1 ∨
      j = (i - 1) - 1 ∨ j = i - 1 ∨ j = i ∨ j = i + 1 ∨
      j = (i + 1) + 1 ∨ j = ((i + 1) + 1) + 1) :
    |(hullEdgeDirection p v j / hullEdgeDirection p v i).arg| ≤ Real.pi / 300 := by
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i hgood
  obtain ⟨hm3, hp3⟩ := tight_hull_outer_turns_of_not_bad p v hv i hgood
  have hold := tight_hull_nearby_edge_args p hp v hv hh i hpos hi hm1 hm2 hp1 hp2
  let e : Fin h → ℂ := hullEdgeDirection p v
  have he (j : Fin h) : e j ≠ 0 := hullEdgeDirection_ne_zero p hp v hv hh j
  have hstep (j : Fin h) (hs : hullExteriorAngle p v j < Real.pi / 1800) :
      0 < (e j / e (j - 1)).arg ∧ (e j / e (j - 1)).arg < Real.pi / 1800 :=
    ⟨hpos j, hs⟩
  have hplus1 : 0 < (e (i + 1) / e i).arg ∧
      (e (i + 1) / e i).arg < Real.pi / 1800 := by
    simpa only [show (i + 1) - 1 = i by abel] using hstep (i + 1) hp1
  have hplus2 : 0 < (e ((i + 1) + 1) / e (i + 1)).arg ∧
      (e ((i + 1) + 1) / e (i + 1)).arg < Real.pi / 1800 := by
    simpa only [show ((i + 1) + 1) - 1 = i + 1 by abel] using
      hstep ((i + 1) + 1) hp2
  have hplus3 : 0 < (e (((i + 1) + 1) + 1) / e ((i + 1) + 1)).arg ∧
      (e (((i + 1) + 1) + 1) / e ((i + 1) + 1)).arg < Real.pi / 1800 := by
    simpa only [show (((i + 1) + 1) + 1) - 1 = (i + 1) + 1 by abel] using
      hstep (((i + 1) + 1) + 1) hp3
  have hright := arg_div_short_chain_three (he i) (he (i + 1))
    (he ((i + 1) + 1)) (he (((i + 1) + 1) + 1)) hplus1 hplus2 hplus3
  have hleft := arg_div_short_chain_four (he ((((i - 1) - 1) - 1) - 1))
    (he (((i - 1) - 1) - 1)) (he ((i - 1) - 1)) (he (i - 1)) (he i)
    (hstep (((i - 1) - 1) - 1) hm3) (hstep ((i - 1) - 1) hm2)
    (hstep (i - 1) hm1) (hstep i hi)
  have hshort (j : Fin h)
      (hj : j = i + 1 ∨ j = (i + 1) + 1 ∨ j = i - 1 ∨
        j = (i - 1) - 1 ∨ j = ((i - 1) - 1) - 1) :
      |(e j / e i).arg| ≤ Real.pi / 300 := by
    have hb := hold j hj
    change |(e j / e i).arg| ≤ Real.pi / 600 at hb
    linarith [Real.pi_pos]
  rcases hj with hj | hj | hj | hj | hj | hj | hj | hj
  · rw [hj]
    change |(e ((((i - 1) - 1) - 1) - 1) / e i).arg| ≤ _
    rw [abs_arg_div_reverse_eq, abs_of_pos hleft.1]
    linarith [hleft.2, Real.pi_pos]
  · exact hshort _ (by tauto)
  · exact hshort _ (by tauto)
  · exact hshort _ (by tauto)
  · rw [hj]
    change |(e i / e i).arg| ≤ _
    rw [div_self (he i), Complex.arg_one, abs_zero]
    positivity
  · exact hshort _ (by tauto)
  · exact hshort _ (by tauto)
  · rw [hj]
    change |(e (((i + 1) + 1) + 1) / e i).arg| ≤ _
    rw [abs_of_pos hright.1]
    linarith [hright.2, Real.pi_pos]

/-- The immediately preceding edge has the sharper one-hundredth slope.
No minimum-length or support premise is required for this direction bound. -/
theorem tight_hull_predecessor_slope {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (hv : Function.Injective v)
    (i : Fin h) (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v) :
    |(hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i).im| ≤
      (hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i).re / 100 := by
  have hi := (tight_hull_five_turns_of_not_bad p v hv i hgood).1
  have harg : |(hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i).arg| ≤
      Real.pi / 1800 := by
    rw [abs_arg_div_reverse_eq]
    change |hullExteriorAngle p v i| ≤ Real.pi / 1800
    rw [abs_of_pos (hpos i)]
    exact hi.le
  exact (tiny_arg_projection _ harg).2

end Erdos957
