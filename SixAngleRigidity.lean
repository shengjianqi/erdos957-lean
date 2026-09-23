import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Equality rigidity for six separated real parameters spanning at most five gaps. -/

namespace Erdos957

/-- Six increasing real parameters with gaps at least `r` and total span at most
`5r` form an exact arithmetic progression. -/
theorem six_angle_rigidity
    (s : Finset ℝ) (r : ℝ) (_hr : 0 < r) (hcard : s.card = 6)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ |a - b|)
    (hspan : ∀ a ∈ s, ∀ b ∈ s, |a - b| ≤ 5 * r) :
    ∀ i : Fin 6,
      s.orderEmbOfFin hcard i = s.orderEmbOfFin hcard 0 + (i : ℝ) * r := by
  let a := s.orderEmbOfFin hcard
  have hgap (i j : Fin 6) (hij : i < j) : r ≤ a j - a i := by
    have hlt : a i < a j := a.strictMono hij
    have hne : a i ≠ a j := ne_of_lt hlt
    have h := hsep (a i) (s.orderEmbOfFin_mem hcard i)
      (a j) (s.orderEmbOfFin_mem hcard j) hne
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlt.le)] at h
    exact h
  have hspan05 : a 5 - a 0 ≤ 5 * r := by
    have hlt : a 0 < a 5 := a.strictMono (by decide)
    have h := hspan (a 0) (s.orderEmbOfFin_mem hcard 0)
      (a 5) (s.orderEmbOfFin_mem hcard 5)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlt.le)] at h
    exact h
  have h01 : r ≤ a 1 - a 0 := hgap 0 1 (by decide)
  have h12 : r ≤ a 2 - a 1 := hgap 1 2 (by decide)
  have h23 : r ≤ a 3 - a 2 := hgap 2 3 (by decide)
  have h34 : r ≤ a 4 - a 3 := hgap 3 4 (by decide)
  have h45 : r ≤ a 5 - a 4 := hgap 4 5 (by decide)
  have heq1 : a 1 = a 0 + 1 * r := by linarith
  have heq2 : a 2 = a 0 + 2 * r := by linarith
  have heq3 : a 3 = a 0 + 3 * r := by linarith
  have heq4 : a 4 = a 0 + 4 * r := by linarith
  have heq5 : a 5 = a 0 + 5 * r := by linarith
  intro i
  fin_cases i <;> norm_num [a, heq1, heq2, heq3, heq4, heq5]

/-- The same conclusion as an equality of finite sets. -/
theorem six_angle_rigidity_image
    (s : Finset ℝ) (r : ℝ) (hr : 0 < r) (hcard : s.card = 6)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ |a - b|)
    (hspan : ∀ a ∈ s, ∀ b ∈ s, |a - b| ≤ 5 * r) :
    s = Finset.univ.image (fun i : Fin 6 => s.orderEmbOfFin hcard 0 + (i : ℝ) * r) := by
  calc
    s = Finset.univ.image (s.orderEmbOfFin hcard) :=
      (Finset.image_orderEmbOfFin_univ s hcard).symm
    _ = Finset.univ.image
        (fun i : Fin 6 => s.orderEmbOfFin hcard 0 + (i : ℝ) * r) := by
      apply Finset.image_congr
      intro i hi
      exact six_angle_rigidity s r hr hcard hsep hspan i

end Erdos957
