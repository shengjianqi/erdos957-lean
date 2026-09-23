import Foundations
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An elementary square-grid packing bound for points in a planar ball.
-/

namespace Erdos957

/-- Points separated by `r` inside a ball of radius `10*r` occupy distinct
cells of a `41 × 41` square grid of side length `r/2`. -/
theorem grid_packing_le_1681 {n : ℕ} (p : Fin n → Point) (center : Point)
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ i j : Fin n, i ≠ j → r ≤ dist (p i) (p j))
    (hball : ∀ i, dist center (p i) ≤ 10 * r) :
    n ≤ 1681 := by
  classical
  have hr2 : 0 < r / 2 := by positivity
  let q (i : Fin n) (k : Fin 2) : ℝ := ((p i) k - center k) / (r / 2)
  have hqbound (i : Fin n) (k : Fin 2) : -20 ≤ q i k ∧ q i k ≤ 20 := by
    have hcoord := (PiLp.dist_apply_le center (p i) k).trans (hball i)
    have habs : |(p i) k - center k| ≤ 10 * r := by
      simpa only [Real.dist_eq, abs_sub_comm] using hcoord
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    constructor
    · dsimp [q]
      apply (le_div_iff₀ hr2).mpr
      nlinarith
    · dsimp [q]
      apply (div_le_iff₀ hr2).mpr
      nlinarith
  have hfloorbound (i : Fin n) (k : Fin 2) :
      -20 ≤ ⌊q i k⌋ ∧ ⌊q i k⌋ ≤ 20 := by
    obtain ⟨hl, hu⟩ := hqbound i k
    constructor
    · apply Int.le_floor.mpr
      exact_mod_cast hl
    · apply Int.floor_le_iff.mpr
      norm_num at *
      linarith
  let cell (i : Fin n) : ℤ × ℤ := (⌊q i 0⌋, ⌊q i 1⌋)
  let box : Finset (ℤ × ℤ) :=
    (Finset.Icc (-20) 20).product (Finset.Icc (-20) 20)
  have hcellmem (i : Fin n) : cell i ∈ box := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr (hfloorbound i 0),
      Finset.mem_Icc.mpr (hfloorbound i 1)⟩
  have hsamecoord {i j : Fin n} (hij : cell i = cell j) (k : Fin 2) :
      |(p i) k - (p j) k| < r / 2 := by
    have hfloor : ⌊q i k⌋ = ⌊q j k⌋ := by
      fin_cases k
      · exact congrArg Prod.fst hij
      · exact congrArg Prod.snd hij
    have hqi := Int.floor_le (q i k)
    have hqj := Int.floor_le (q j k)
    have hqi' := Int.lt_floor_add_one (q i k)
    have hqj' := Int.lt_floor_add_one (q j k)
    have hqdiff : |q i k - q j k| < 1 := by
      rw [hfloor] at hqi hqi'
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hqsub : q i k - q j k = ((p i) k - (p j) k) / (r / 2) := by
      dsimp [q]
      ring
    rw [hqsub, abs_div, abs_of_pos hr2] at hqdiff
    have h := (div_lt_iff₀ hr2).mp hqdiff
    simpa only [one_mul] using h
  have hcellinj : Function.Injective cell := by
    intro i j hij
    by_contra hne
    have hx : dist ((p i) 0) ((p j) 0) < r / 2 := by
      simpa only [Real.dist_eq] using hsamecoord hij 0
    have hy : dist ((p i) 1) ((p j) 1) < r / 2 := by
      simpa only [Real.dist_eq] using hsamecoord hij 1
    have hx2 : dist ((p i) 0) ((p j) 0) ^ 2 < (r / 2) ^ 2 :=
      (sq_lt_sq₀ (dist_nonneg) hr2.le).mpr hx
    have hy2 : dist ((p i) 1) ((p j) 1) ^ 2 < (r / 2) ^ 2 :=
      (sq_lt_sq₀ (dist_nonneg) hr2.le).mpr hy
    have hsquares : dist (p i) (p j) ^ 2 =
        dist ((p i) 0) ((p j) 0) ^ 2 +
        dist ((p i) 1) ((p j) 1) ^ 2 := by
      simpa [Fin.sum_univ_two] using (EuclideanSpace.dist_sq_eq (p i) (p j))
    have hdsq : dist (p i) (p j) ^ 2 < r ^ 2 := by
      nlinarith [sq_pos_of_pos hr]
    have hdist : dist (p i) (p j) < r :=
      (sq_lt_sq₀ (dist_nonneg) hr.le).mp hdsq
    exact (not_lt_of_ge (hsep i j hne)) hdist
  have hsubset : Finset.univ.image cell ⊆ box := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact hcellmem i
  have hcard : (Finset.univ.image cell).card = n := by
    rw [Finset.card_image_of_injective _ hcellinj]
    simp
  have hbox : box.card = 1681 := by
    norm_num [box, Finset.card_product, Int.card_Icc]
  calc
    n = (Finset.univ.image cell).card := hcard.symm
    _ ≤ box.card := Finset.card_le_card hsubset
    _ = 1681 := hbox

end Erdos957
