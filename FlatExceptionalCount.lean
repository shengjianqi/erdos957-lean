import Foundations
import Mathlib.Data.Finset.Preimage
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-! Counting the exceptional neighborhoods from a total turning bound.
The hypotheses about angles are explicit: this file does not construct a
convex polygon or prove its total exterior angle. -/

namespace Erdos957

open scoped BigOperators

/-- A nonnegative angle budget of one full turn permits at most 360
vertices whose exterior angle is at least one degree. -/
theorem card_large_turns_le_360 {ι : Type*} [Fintype ι]
    (turn : ι → ℝ) (hnonneg : ∀ i, 0 ≤ turn i)
    (htotal : ∑ i, turn i ≤ 2 * Real.pi) :
    (Finset.univ.filter fun i => Real.pi / 180 ≤ turn i).card ≤ 360 := by
  classical
  let B := Finset.univ.filter fun i => Real.pi / 180 ≤ turn i
  have hsmall : (B.card : ℝ) * (Real.pi / 180) ≤ ∑ i ∈ B, turn i := by
    calc
      (B.card : ℝ) * (Real.pi / 180) = ∑ _i ∈ B, Real.pi / 180 := by simp
      _ ≤ ∑ i ∈ B, turn i := Finset.sum_le_sum fun i hi =>
        (Finset.mem_filter.mp hi).2
  have hsum : ∑ i ∈ B, turn i ≤ ∑ i, turn i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun i _ _ => hnonneg i)
  have hcard : (B.card : ℝ) ≤ 360 := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hcard

/-- Looking at seven permuted positions can multiply the number of bad
vertices by at most seven. This includes cyclic neighborhoods of radius three. -/
theorem card_seven_neighborhoods_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset ι) (offset : Fin 7 → Equiv.Perm ι) :
    (Finset.univ.biUnion fun k => B.image (offset k).symm).card ≤ 7 * B.card := by
  classical
  calc
    _ ≤ ∑ k : Fin 7, (B.image (offset k).symm).card := Finset.card_biUnion_le
    _ = 7 * B.card := by
      simp only [Finset.card_image_of_injective _ (Equiv.injective _)]
      simp

/-- At most 2520 neighborhoods contain an exterior angle at least one
degree, provided the nonnegative exterior angles sum to at most a full turn. -/
theorem card_nonflat_neighborhoods_le_2520 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (turn : ι → ℝ) (offset : Fin 7 → Equiv.Perm ι)
    (hnonneg : ∀ i, 0 ≤ turn i) (htotal : ∑ i, turn i ≤ 2 * Real.pi) :
    (Finset.univ.biUnion fun k =>
      (Finset.univ.filter fun i => Real.pi / 180 ≤ turn i).image
        (offset k).symm).card ≤ 2520 := by
  exact (card_seven_neighborhoods_le _ offset).trans
    (by have h := card_large_turns_le_360 turn hnonneg htotal; omega)

/-- Membership in the exceptional set means that one of the seven selected
positions has an exterior angle of at least one degree. -/
theorem mem_nonflat_neighborhoods_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (turn : ι → ℝ) (offset : Fin 7 → Equiv.Perm ι) (i : ι) :
    i ∈ (Finset.univ.biUnion fun k =>
      (Finset.univ.filter fun j => Real.pi / 180 ≤ turn j).image
        (offset k).symm) ↔
      ∃ k : Fin 7, Real.pi / 180 ≤ turn (offset k i) := by
  classical
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨k, j, hj, hji⟩
    have : j = offset k i := by rw [← hji]; simp
    exact ⟨k, this ▸ hj⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, offset k i, hk, by simp⟩

/-- The seven circular offsets `-3,-2,-1,0,1,2,3`, interpreted modulo `h`.
Repeated offsets for small polygons cause no problem for the upper bound.
We include the center as well as the six neighboring positions; thus this
exception set is a conservative enlargement of the six-position list in
the paper, not a claim that the two definitions coincide. -/
def sevenCyclicOffsets (h : ℕ) [NeZero h] (k : Fin 7) : Equiv.Perm (Fin h) :=
  Equiv.addRight (Fin.ofNat h k.val - 3)

/-- Concrete cyclic-neighborhood version of the uniform exceptional bound. -/
theorem card_cyclic_nonflat_le_2520 {h : ℕ} [NeZero h]
    (turn : Fin h → ℝ) (hnonneg : ∀ i, 0 ≤ turn i)
    (htotal : ∑ i, turn i ≤ 2 * Real.pi) :
    (Finset.univ.filter fun i => ∃ k : Fin 7,
      Real.pi / 180 ≤ turn (i + (Fin.ofNat h k.val - 3))).card ≤ 2520 := by
  classical
  have heq : (Finset.univ.filter fun i => ∃ k : Fin 7,
      Real.pi / 180 ≤ turn (i + (Fin.ofNat h k.val - 3))) =
      Finset.univ.biUnion (fun k =>
        (Finset.univ.filter fun i => Real.pi / 180 ≤ turn i).image
          (sevenCyclicOffsets h k).symm) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_nonflat_neighborhoods_iff]
    rfl
  rw [heq]
  exact card_nonflat_neighborhoods_le_2520 turn (sevenCyclicOffsets h) hnonneg htotal

end Erdos957
