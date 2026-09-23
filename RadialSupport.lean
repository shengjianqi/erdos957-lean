import HullSupport
import PlanarOrientation
import HullGeneration
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.FieldSimp

/-! The geometric bridge from an empty radial sector to a supporting chord. -/

namespace Erdos957

/-- A nonzero linear functional bounded above on a set is strictly below
that bound at every interior point. -/
theorem linear_lt_bound_at_interior (f : Point →L[ℝ] ℝ) (hf : f ≠ 0)
    (C : Set Point) (M : ℝ) (hbound : ∀ x ∈ C, f x ≤ M)
    {c : Point} (hc : c ∈ interior C) : f c < M := by
  have hex : ∃ x : Point, f x ≠ 0 := by
    by_contra! h
    apply hf
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hex
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(y / f x) • x, ?_⟩
    simp [hx]
  have hmaps : Set.MapsTo f C (Set.Iic M) := hbound
  have hi := (f.isOpenMap hsurj).mapsTo_interior hmaps hc
  simpa only [interior_Iic, Set.mem_Iio] using hi

/-- Strict support at an extreme vertex also strictly separates every
interior point from that vertex. -/
theorem hull_extreme_support_with_interior {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (u : Fin n) (hu : p u ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p))) :
    ∃ f : Point →L[ℝ] ℝ, f c < f (p u) ∧ ∀ j, f (p j) ≤ f (p u) := by
  obtain ⟨f, hf⟩ := hull_extreme_strict_support p hp u hu
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hj⟩ := exists_ne u
  have hfne : f ≠ 0 := by
    intro h
    have hlt := hf j hj
    simp [h] at hlt
  have hall : ∀ j, f (p j) ≤ f (p u) := by
    intro j
    by_cases hju : j = u
    · simp [hju]
    · exact (hf j hju).le
  have hC : convexHull ℝ (Set.range p) ⊆ {x | f x ≤ f (p u)} := by
    apply convexHull_min
    · rintro x ⟨j, rfl⟩
      exact hall j
    · exact convex_halfSpace_le f.toLinearMap.isLinear _
  exact ⟨f, linear_lt_bound_at_interior f hfne _ _ hC hc, hall⟩

/-- If a configuration point lies beyond the chord between two extreme
vertices, its affine coefficients along both rays from an interior center
are positive. Otherwise one of the extreme vertices could not be supported. -/
theorem extreme_affine_coefficients_pos {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j k : Fin n)
    (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hj : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (a b : ℝ) (hsum : 1 < a + b)
    (hrep : p k = (1 - a - b) • c + a • p i + b • p j) :
    0 < a ∧ 0 < b := by
  have hfirst : 0 < a := by
    by_contra ha
    have ha' : a ≤ 0 := le_of_not_gt ha
    obtain ⟨f, hfc, hf⟩ := hull_extreme_support_with_interior p hn hp j hj c hc
    have hmap := congrArg f hrep
    simp only [map_add, map_smul, smul_eq_mul] at hmap
    have hpos : 0 < (1 - a - b) * (f c - f (p j)) :=
      mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hfc)
    have hnonneg : 0 ≤ a * (f (p i) - f (p j)) :=
      mul_nonneg_of_nonpos_of_nonpos ha' (sub_nonpos.mpr (hf i))
    nlinarith [hf k]
  have hsecond : 0 < b := by
    by_contra hb
    have hb' : b ≤ 0 := le_of_not_gt hb
    obtain ⟨f, hfc, hf⟩ := hull_extreme_support_with_interior p hn hp i hi c hc
    have hmap := congrArg f hrep
    simp only [map_add, map_smul, smul_eq_mul] at hmap
    have hpos : 0 < (1 - a - b) * (f c - f (p i)) :=
      mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hfc)
    have hnonneg : 0 ≤ b * (f (p j) - f (p i)) :=
      mul_nonneg_of_nonpos_of_nonpos hb' (sub_nonpos.mpr (hf j))
    nlinarith [hf k]
  exact ⟨hfirst, hsecond⟩

/-- Affine coordinates of a point with respect to a nondegenerate planar
triangle, written directly using signed areas. -/
theorem affine_coordinates_of_turn (c a b q : Point) (hdet : turn c a b ≠ 0) :
    q = (1 - turn c q b / turn c a b - turn c a q / turn c a b) • c +
      (turn c q b / turn c a b) • a + (turn c a q / turn c a b) • b := by
  ext k
  fin_cases k
  · change q 0 = (1 - turn c q b / turn c a b - turn c a q / turn c a b) * c 0 +
      (turn c q b / turn c a b) * a 0 + (turn c a q / turn c a b) * b 0
    field_simp
    simp only [turn]
    ring
  · change q 1 = (1 - turn c q b / turn c a b - turn c a q / turn c a b) * c 1 +
      (turn c q b / turn c a b) * a 1 + (turn c a q / turn c a b) * b 1
    field_simp
    simp only [turn]
    ring

/-- A point strictly outside the chord between two extreme vertices must
lie strictly inside their radial sector, when that sector spans less than
a half-turn in the positive orientation. -/
theorem outside_chord_in_radial_sector {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j k : Fin n)
    (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hj : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hdet : 0 < turn c (p i) (p j)) (hout : turn (p i) (p j) (p k) < 0) :
    0 < turn c (p i) (p k) ∧ 0 < turn c (p k) (p j) := by
  have hidentity : turn (p i) (p j) (p k) = turn c (p i) (p j) -
      turn c (p k) (p j) - turn c (p i) (p k) := by
    simp only [turn]
    ring
  have hsum : 1 < turn c (p k) (p j) / turn c (p i) (p j) +
      turn c (p i) (p k) / turn c (p i) (p j) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdet).mpr
    nlinarith
  have hpos := extreme_affine_coefficients_pos p hn hp c hc i j k hi hj
    _ _ hsum (affine_coordinates_of_turn c (p i) (p j) (p k) hdet.ne')
  exact ⟨(div_pos_iff_of_pos_right hdet).mp hpos.2,
    (div_pos_iff_of_pos_right hdet).mp hpos.1⟩

/-- If the positive radial sector between two extreme vertices contains no
other extreme vertex, their oriented chord supports the entire point set.
The empty-sector condition will be supplied by consecutive angular order. -/
theorem supporting_chord_of_empty_radial_sector {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j : Fin n)
    (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hj : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ)
    (hdet : 0 < turn c (p i) (p j))
    (hempty : ∀ k ∈ hullVertexIndices p,
      ¬ (0 < turn c (p i) (p k) ∧ 0 < turn c (p k) (p j))) :
    ∀ k : Fin n, 0 ≤ turn (p i) (p j) (p k) := by
  have hvertices : ∀ k ∈ hullVertexIndices p, 0 ≤ turn (p i) (p j) (p k) := by
    intro k hk
    by_contra hout
    exact hempty k hk (outside_chord_in_radial_sector p hn hp c hc i j k hi hj
      hdet (lt_of_not_ge hout))
  have hconvex : Convex ℝ {q : Point | 0 ≤ turn (p i) (p j) q} := by
    intro x hx y hy s t hs ht hst
    change 0 ≤ turn (p i) (p j) (s • x + t • y)
    rw [turn_affine _ _ _ _ _ _ hst]
    exact add_nonneg (mul_nonneg hs hx) (mul_nonneg ht hy)
  have hsub : convexHull ℝ (Set.range p) ⊆
      {q : Point | 0 ≤ turn (p i) (p j) q} := by
    rw [← convexHull_image_hullVertexIndices p]
    apply convexHull_min _ hconvex
    rintro q ⟨k, hk, rfl⟩
    exact hvertices k hk
  intro k
  exact hsub (subset_convexHull ℝ (Set.range p) ⟨k, rfl⟩)

end Erdos957
