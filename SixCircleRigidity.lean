import CircularGap
import SixAngleRigidity
import SixtyDegreeChord
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Rigidity of the six-point equality case in planar circle packing. -/

namespace Erdos957

/-- Six separated points on a circle have equally spaced direction parameters. -/
theorem circle_six_direction_regular
    (N : Finset Point) (x : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hcard : N.card = 6) :
    ∃ v : Fin 6 → Point,
      Function.Injective v ∧ Set.range v = (N : Set Point) ∧
      (∀ i, dist x (v i) = r) ∧
      (∀ i, directionArg x (v i) =
        directionArg x (v 0) + (i : ℝ) * (Real.pi / 3)) := by
  classical
  let directions : Finset ℝ := N.image (directionArg x)
  have hdirinj : Set.InjOn (directionArg x) (N : Set Point) :=
    neighbor_directionArg_injOn N x r hr hradius hsep
  have hdircard : directions.card = 6 := by
    calc
      directions.card = N.card := Finset.card_image_of_injOn hdirinj
      _ = 6 := hcard
  have hdirsep : ∀ θ ∈ directions, ∀ φ ∈ directions,
      θ ≠ φ → Real.pi / 3 ≤ |θ - φ| := by
    intro θ hθ φ hφ hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hφ
    have hyz : y ≠ z := fun heq => hne (congrArg (directionArg x) heq)
    exact neighbor_directionArg_separated N x r hr hradius hsep hy hz hyz
  have hdirspan : ∀ θ ∈ directions, ∀ φ ∈ directions,
      |θ - φ| ≤ 5 * (Real.pi / 3) := by
    intro θ hθ φ hφ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hφ
    by_cases hyz : y = z
    · subst z
      simp
      positivity
    · have h := equal_radius_arg_gap_le_five_pi_div_three x y z r hr
        (hradius y hy) (hradius z hz) (hsep y hy z hz hyz)
      convert h using 1; ring
  let a := directions.orderEmbOfFin hdircard
  have hpre (i : Fin 6) : ∃ y ∈ N, directionArg x y = a i := by
    have hai : a i ∈ directions := directions.orderEmbOfFin_mem hdircard i
    exact Finset.mem_image.mp hai
  choose v hvN hvArg using hpre
  have hvinj : Function.Injective v := by
    intro i j hij
    apply a.injective
    calc
      a i = directionArg x (v i) := (hvArg i).symm
      _ = directionArg x (v j) := congrArg (directionArg x) hij
      _ = a j := hvArg j
  have hrange : Set.range v = (N : Set Point) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact hvN i
    · intro hy
      have hyarg : directionArg x y ∈ directions :=
        Finset.mem_image.mpr ⟨y, hy, rfl⟩
      have hyarange : directionArg x y ∈ Set.range a := by
        rw [Finset.range_orderEmbOfFin]
        exact hyarg
      obtain ⟨i, hi⟩ := hyarange
      refine ⟨i, ?_⟩
      apply hdirinj (hvN i) hy
      rw [hvArg i, hi]
  have harg (i : Fin 6) : directionArg x (v i) =
      directionArg x (v 0) + (i : ℝ) * (Real.pi / 3) := by
    have hi := six_angle_rigidity directions (Real.pi / 3) (by positivity)
      hdircard hdirsep hdirspan i
    change a i = a 0 + (i : ℝ) * (Real.pi / 3) at hi
    simpa only [← hvArg] using hi
  exact ⟨v, hvinj, hrange, (fun i => hradius (v i) (hvN i)), harg⟩

/-- Equality in the six-neighbor bound forces a cyclic regular hexagon. -/
theorem circle_six_regular
    (N : Finset Point) (x : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hcard : N.card = 6) :
    ∃ v : Fin 6 → Point,
      Function.Injective v ∧ Set.range v = (N : Set Point) ∧
      (∀ i, dist x (v i) = r) ∧
      (∀ i, directionArg x (v i) =
        directionArg x (v 0) + (i : ℝ) * (Real.pi / 3)) ∧
      (∀ i, dist (v i) (v (i + 1)) = r) := by
  obtain ⟨v, hvinj, hrange, hv_radius, hv_arg⟩ :=
    circle_six_direction_regular N x r hr hradius hsep hcard
  refine ⟨v, hvinj, hrange, hv_radius, hv_arg, ?_⟩
  intro i
  apply dist_eq_radius_of_directionArg_gap x (v i) (v (i + 1)) r hr
    (hv_radius i) (hv_radius (i + 1))
  rw [hv_arg i, hv_arg (i + 1)]
  fin_cases i <;> norm_num
  all_goals
    first
    | left; positivity
    | left; rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]; ring
    | right; rw [abs_of_nonneg (by positivity)]; ring

end Erdos957
