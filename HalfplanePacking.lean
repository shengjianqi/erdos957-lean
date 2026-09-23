import PlanarDirections
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith

/-! Three-direction packing in a strict half-plane. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Three bins of width `r` cover an interval of width `3r`. -/
theorem card_le_three_of_separated_in_Ico
    (s : Finset ℝ) (r : ℝ) (hr : 0 < r)
    (hinterval : ∀ t ∈ s, 0 ≤ t ∧ t < 3 * r)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → r ≤ |t - u|) :
    s.card ≤ 3 := by
  let bin : ℝ → ℕ := fun t => Nat.floor (t / r)
  have hbin_bounds (t : ℝ) (ht : 0 ≤ t) :
      (bin t : ℝ) * r ≤ t ∧ t < ((bin t : ℝ) + 1) * r := by
    have htdiv : 0 ≤ t / r := div_nonneg ht hr.le
    constructor
    · exact (le_div_iff₀ hr).mp (Nat.floor_le htdiv)
    · exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
  have hmaps : Set.MapsTo bin (s : Set ℝ) (Finset.range 3 : Set ℕ) := by
    intro t ht
    have htint := hinterval t ht
    have htdiv : 0 ≤ t / r := div_nonneg htint.1 hr.le
    have htdiv3 : t / r < 3 := (div_lt_iff₀ hr).mpr htint.2
    exact Finset.mem_range.mpr ((Nat.floor_lt htdiv).mpr htdiv3)
  have hinj : Set.InjOn bin (s : Set ℝ) := by
    intro t ht u hu htu
    by_contra hne
    have hgap := hsep t ht u hu hne
    obtain ⟨htlo, hthi⟩ := hbin_bounds t (hinterval t ht).1
    obtain ⟨hulo, huhi⟩ := hbin_bounds u (hinterval u hu).1
    have hbin_eq : (bin t : ℝ) = (bin u : ℝ) :=
      congrArg (fun k : ℕ => (k : ℝ)) htu
    rw [← hbin_eq] at hulo huhi
    rcases le_total t u with htuord | hutord
    · have habs : |t - u| = u - t := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htuord)]
      rw [habs] at hgap
      nlinarith
    · have habs : |t - u| = t - u := abs_of_nonneg (sub_nonneg.mpr hutord)
      rw [habs] at hgap
      nlinarith
  simpa using (Finset.card_le_card_of_injOn bin hmaps hinj)

/-- At most three mutually `π/3`-separated parameters fit into an open semicircle. -/
theorem card_le_three_of_angles_in_open_semicircle
    (s : Finset ℝ)
    (hrange : ∀ θ ∈ s, -Real.pi / 2 < θ ∧ θ < Real.pi / 2)
    (hsep : ∀ θ ∈ s, ∀ φ ∈ s, θ ≠ φ → Real.pi / 3 ≤ |θ - φ|) :
    s.card ≤ 3 := by
  classical
  let shift : ℝ → ℝ := fun θ => θ + Real.pi / 2
  let t := s.image shift
  have ht_interval : ∀ u ∈ t, 0 ≤ u ∧ u < 3 * (Real.pi / 3) := by
    intro u hu
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hlo, hhi⟩ := hrange θ hθ
    constructor <;> dsimp [shift] <;> linarith
  have ht_sep : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → Real.pi / 3 ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hv
    have hne : θ ≠ φ := by
      intro heq
      exact huv (congrArg shift heq)
    simpa only [shift, add_sub_add_right_eq_sub] using hsep θ hθ φ hφ hne
  have ht_card : t.card = s.card := by
    dsimp [t]
    apply Finset.card_image_of_injective
    intro θ φ h
    dsimp [shift] at h
    linarith
  rw [← ht_card]
  exact card_le_three_of_separated_in_Ico t (Real.pi / 3)
    (by positivity) ht_interval ht_sep

/-- Rotate each vector so that `axis` points along the positive real axis. -/
noncomputable def halfplaneArg (x axis y : Point) : ℝ :=
  (conj (pointToComplex axis) * pointToComplex (y - x)).arg

theorem halfplaneArg_mem_Ioo {x axis y : Point}
    (hhalf : 0 < inner ℝ axis (y - x)) :
    -Real.pi / 2 < halfplaneArg x axis y ∧
      halfplaneArg x axis y < Real.pi / 2 := by
  let v : ℂ := pointToComplex axis
  let w : ℂ := pointToComplex (y - x)
  have hinner : inner ℝ axis (y - x) = (conj v * w).re := by
    calc
      inner ℝ axis (y - x) = inner ℝ v w :=
        (pointToComplex.toLinearIsometry.inner_map_map axis (y - x)).symm
      _ = (conj v * w).re := by
        rw [Complex.inner, mul_comm]
  have hreal : 0 < (conj v * w).re := by rw [← hinner]; exact hhalf
  have habs : |(conj v * w).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hreal)
  have ⟨hlo, hhi⟩ := abs_lt.mp habs
  constructor
  · change -Real.pi / 2 < (conj v * w).arg
    linarith
  · change (conj v * w).arg < Real.pi / 2
    exact hhi

theorem halfplaneArg_gap
    (x axis y z : Point) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : r ≤ dist y z) (hhalf : 0 < inner ℝ axis (y - x)) :
    Real.pi / 3 ≤ |halfplaneArg x axis y - halfplaneArg x axis z| := by
  let v : ℂ := pointToComplex axis
  let w : ℂ := pointToComplex (y - x)
  let u : ℂ := pointToComplex (z - x)
  have hv : v ≠ 0 := by
    intro hv0
    have haxis : axis = 0 := pointToComplex.injective (by simpa [v] using hv0)
    simp [haxis] at hhalf
  have hconj : conj v ≠ 0 := by
    intro h
    apply hv
    have := congrArg conj h
    simpa using this
  have hw : conj v * w ≠ 0 := by
    intro h
    have hwy : w ≠ 0 := by
      intro h0
      have hpoint : y - x = 0 := pointToComplex.injective (by simpa [w] using h0)
      have : dist x y = 0 := by simp [sub_eq_zero.mp hpoint]
      linarith
    exact hwy ((mul_eq_zero.mp h).resolve_left hconj)
  have hu : conj v * u ≠ 0 := by
    intro h
    have huz : u ≠ 0 := by
      intro h0
      have hpoint : z - x = 0 := pointToComplex.injective (by simpa [u] using h0)
      have : dist x z = 0 := by simp [sub_eq_zero.mp hpoint]
      linarith
    exact huz ((mul_eq_zero.mp h).resolve_left hconj)
  calc
    Real.pi / 3 ≤ InnerProductGeometry.angle (x - y) (x - z) :=
      equal_radius_angle_ge_pi_div_three x y z r hr hxy hxz hyz
    _ = InnerProductGeometry.angle (y - x) (z - x) := by
      simpa only [neg_sub] using
        (InnerProductGeometry.angle_neg_neg (x - y) (x - z)).symm
    _ = InnerProductGeometry.angle w u := by
      exact (pointToComplex.toLinearIsometry.angle_map (y - x) (z - x)).symm
    _ = InnerProductGeometry.angle (conj v * w) (conj v * u) := by
      exact (Complex.angle_mul_left hconj w u).symm
    _ ≤ |halfplaneArg x axis y - halfplaneArg x axis z| := by
      exact complex_angle_le_arg_gap hw hu

/-- A separated same-radius set in a strict half-plane has at most three points. -/
theorem circle_card_le_three_in_halfplane
    (N : Finset Point) (x axis : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hhalf : ∀ y ∈ N, 0 < inner ℝ axis (y - x)) :
    N.card ≤ 3 := by
  classical
  let s : Finset ℝ := N.image (halfplaneArg x axis)
  have hrange : ∀ θ ∈ s, -Real.pi / 2 < θ ∧ θ < Real.pi / 2 := by
    intro θ hθ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    exact halfplaneArg_mem_Ioo (hhalf y hy)
  have hsep_arg : ∀ θ ∈ s, ∀ φ ∈ s, θ ≠ φ →
      Real.pi / 3 ≤ |θ - φ| := by
    intro θ hθ φ hφ hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hφ
    have hyz : y ≠ z := by
      intro heq
      exact hne (congrArg (halfplaneArg x axis) heq)
    exact halfplaneArg_gap x axis y z r hr (hradius y hy) (hradius z hz)
      (hsep y hy z hz hyz) (hhalf y hy)
  have hinj : Set.InjOn (halfplaneArg x axis) (N : Set Point) := by
    intro y hy z hz heq
    by_contra hne
    have hgap := halfplaneArg_gap x axis y z r hr (hradius y hy) (hradius z hz)
      (hsep y hy z hz hne) (hhalf y hy)
    rw [heq, sub_self, abs_zero] at hgap
    linarith [Real.pi_pos]
  have hcard : s.card = N.card := by
    exact Finset.card_image_iff.mpr hinj
  rw [← hcard]
  exact card_le_three_of_angles_in_open_semicircle s hrange hsep_arg

end Erdos957

