import Foundations
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Signed orientation and half-plane separation for two segments in the
Euclidean plane.
-/

namespace Erdos957

def turn (a b c : Point) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

private theorem coord_smul (t : ℝ) (p : Point) (i : Fin 2) :
    (t • p) i = t * p i := by
  rfl

private theorem coord_add (p q : Point) (i : Fin 2) :
    (p + q) i = p i + q i := by
  rfl

theorem turn_swap (a b c : Point) : turn a c b = -turn a b c := by
  unfold turn
  ring

theorem turn_reverse (a b c : Point) : turn b a c = -turn a b c := by
  unfold turn
  ring

theorem turn_self_left (a b : Point) : turn a b a = 0 := by
  simp [turn]

theorem turn_self_right (a b : Point) : turn a b b = 0 := by
  unfold turn
  ring

theorem turn_affine (a b p q : Point) (t u : ℝ) (htu : t + u = 1) :
    turn a b (t • p + u • q) = t * turn a b p + u * turn a b q := by
  have ht : t = 1 - u := by linarith
  subst t
  simp only [turn, coord_add, coord_smul]
  ring

/-- A segment from `a` into the strict left half-plane of the oriented line
`a b` and a segment from `b` into its strict right half-plane are disjoint. -/
theorem segments_disjoint_of_opposite_left_turns
    {a b c d : Point}
    (h1 : 0 < turn a b c)
    (h2 : 0 < turn b a d) :
    Disjoint (segment ℝ a c) (segment ℝ b d) := by
  apply Set.disjoint_left.mpr
  intro x hxac hxbd
  obtain ⟨t, u, ht, hu, htu, hx⟩ := hxac
  obtain ⟨v, w, hv, hw, hvw, hx'⟩ := hxbd
  have hsame : t • a + u • c = v • b + w • d := hx.trans hx'.symm
  have hturn_eq := congrArg (turn a b) hsame
  rw [turn_affine a b a c t u htu,
      turn_affine a b b d v w hvw,
      turn_self_left, turn_self_right] at hturn_eq
  have hneg : turn a b d < 0 := by
    rw [turn_reverse] at h2
    linarith
  have hleft : 0 ≤ u * turn a b c := mul_nonneg hu h1.le
  have hright : w * turn a b d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw hneg.le
  have hleft0 : u * turn a b c = 0 := by linarith
  have hright0 : w * turn a b d = 0 := by linarith
  have hu0 : u = 0 := (mul_eq_zero.mp hleft0).resolve_right (ne_of_gt h1)
  have hw0 : w = 0 := (mul_eq_zero.mp hright0).resolve_right (ne_of_lt hneg)
  have ht1 : t = 1 := by linarith
  have hv1 : v = 1 := by linarith
  have hab : a = b := by simpa [ht1, hu0, hv1, hw0] using hsame
  have hzero : turn a b c = 0 := by rw [hab]; simp [turn]
  linarith

theorem inner_coords (p q : Point) :
    inner ℝ p q = p 0 * q 0 + p 1 * q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

end Erdos957
