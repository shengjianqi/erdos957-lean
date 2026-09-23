import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite packing of separated real numbers in an interval of width six times
the minimum gap. This is the combinatorial part of the six-neighbor bound for
the closest-pair graph; connecting geometric directions to real angles is a
separate obligation.
-/

namespace Erdos957

/-- Six half-open bins of width `r` contain at most one member each when
distinct members are at least `r` apart. -/
theorem card_le_six_of_separated_in_Ico
    (s : Finset ℝ) (r : ℝ) (hr : 0 < r)
    (hinterval : ∀ x ∈ s, 0 ≤ x ∧ x < 6 * r)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ |x - y|) :
    s.card ≤ 6 := by
  let bin : ℝ → ℕ := fun x => Nat.floor (x / r)
  have hbin_bounds (x : ℝ) (hx : 0 ≤ x) :
      (bin x : ℝ) * r ≤ x ∧ x < ((bin x : ℝ) + 1) * r := by
    have hxdiv : 0 ≤ x / r := div_nonneg hx hr.le
    constructor
    · exact (le_div_iff₀ hr).mp (Nat.floor_le hxdiv)
    · exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (x / r))
  have hmaps : Set.MapsTo bin (s : Set ℝ) (Finset.range 6 : Set ℕ) := by
    intro x hx
    have hxint := hinterval x hx
    have hxdiv : 0 ≤ x / r := div_nonneg hxint.1 hr.le
    have hxdiv6 : x / r < 6 := (div_lt_iff₀ hr).mpr hxint.2
    exact Finset.mem_range.mpr ((Nat.floor_lt hxdiv).mpr hxdiv6)
  have hinj : Set.InjOn bin (s : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hgap := hsep x hx y hy hne
    obtain ⟨hxlo, hxhi⟩ := hbin_bounds x (hinterval x hx).1
    obtain ⟨hylo, hyhi⟩ := hbin_bounds y (hinterval y hy).1
    have hbin_eq : (bin x : ℝ) = (bin y : ℝ) :=
      congrArg (fun k : ℕ => (k : ℝ)) hxy
    rw [← hbin_eq] at hylo hyhi
    rcases le_total x y with hxyord | hyxord
    · have habs : |x - y| = y - x := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxyord)]
      rw [habs] at hgap
      nlinarith
    · have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyxord)
      rw [habs] at hgap
      nlinarith
  simpa using (Finset.card_le_card_of_injOn bin hmaps hinj)

/-- The reflected version uses a half-open interval whose right endpoint is
included, matching the usual range of the planar argument function. -/
theorem card_le_six_of_separated_in_Ioc
    (s : Finset ℝ) (a r : ℝ) (hr : 0 < r)
    (hinterval : ∀ x ∈ s, a < x ∧ x ≤ a + 6 * r)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ |x - y|) :
    s.card ≤ 6 := by
  classical
  let reflect : ℝ → ℝ := fun x => a + 6 * r - x
  let t : Finset ℝ := s.image reflect
  have ht_interval : ∀ y ∈ t, 0 ≤ y ∧ y < 6 * r := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxa, hxb⟩ := hinterval x hx
    constructor <;> dsimp [reflect] <;> linarith
  have ht_sep : ∀ y ∈ t, ∀ z ∈ t, y ≠ z → r ≤ |y - z| := by
    intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hxw : x ≠ w := by
      intro heq
      exact hyz (congrArg reflect heq)
    have h := hsep x hx w hw hxw
    have hdiff : reflect x - reflect w = w - x := by
      dsimp [reflect]
      ring
    simpa only [hdiff, abs_sub_comm] using h
  have ht_card : t.card = s.card := by
    dsimp [t]
    apply Finset.card_image_of_injective
    intro x y h
    dsimp [reflect] at h
    linarith
  rw [← ht_card]
  exact card_le_six_of_separated_in_Ico t r hr ht_interval ht_sep

/-- Numerical form for directions represented by real angles in `(-π, π]`.
Only ordinary absolute separation is used here; the geometric bridge from
unit-distance edges to this hypothesis remains separate. -/
theorem card_le_six_of_angles
    (s : Finset ℝ)
    (hrange : ∀ θ ∈ s, -Real.pi < θ ∧ θ ≤ Real.pi)
    (hsep : ∀ θ ∈ s, ∀ φ ∈ s, θ ≠ φ → Real.pi / 3 ≤ |θ - φ|) :
    s.card ≤ 6 := by
  have hr : 0 < Real.pi / 3 := by positivity
  have hinterval : ∀ θ ∈ s,
      -Real.pi < θ ∧ θ ≤ -Real.pi + 6 * (Real.pi / 3) := by
    intro θ hθ
    obtain ⟨hlo, hhi⟩ := hrange θ hθ
    constructor
    · exact hlo
    · nlinarith
  exact card_le_six_of_separated_in_Ioc s (-Real.pi) (Real.pi / 3)
    hr hinterval hsep

end Erdos957
