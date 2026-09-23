import HullRadialOrder
import HullGeneration
import RadialSupport
import RadialAngles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Radial angular gaps of the actual vertices of a finite planar hull. -/

namespace Erdos957

private noncomputable def turnFunctional (c a : Point) : Point →L[ℝ] ℝ :=
  (a 0 - c 0) • EuclideanSpace.proj 1 -
    (a 1 - c 1) • EuclideanSpace.proj 0

private theorem turnFunctional_apply (c a q : Point) :
    turnFunctional c a q = (a 0 - c 0) * q 1 - (a 1 - c 1) * q 0 := by
  simp [turnFunctional]

private theorem turn_eq_turnFunctional_sub (c a q : Point) :
    turn c a q = turnFunctional c a q - turnFunctional c a c := by
  rw [turnFunctional_apply, turnFunctional_apply]
  simp only [turn]
  ring

private theorem turnFunctional_ne_zero {c a : Point} (h : a ≠ c) :
    turnFunctional c a ≠ 0 := by
  intro hf
  have h0 : a 0 - c 0 = 0 := by
    have heq := congrArg (fun f : Point →L[ℝ] ℝ =>
      f (EuclideanSpace.single 1 (1 : ℝ))) hf
    simp [turnFunctional_apply] at heq
    linarith
  have h1 : a 1 - c 1 = 0 := by
    have heq := congrArg (fun f : Point →L[ℝ] ℝ =>
      f (EuclideanSpace.single 0 (1 : ℝ))) hf
    simp [turnFunctional_apply] at heq
    linarith
  apply h
  ext i
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1

private theorem exists_hull_vertex_positive_turn {n : ℕ} (p : Fin n → Point)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i : Fin n) (hi : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ) :
    ∃ k ∈ hullVertexIndices p, 0 < turn c (p i) (p k) := by
  classical
  by_contra h
  push Not at h
  let f := turnFunctional c (p i)
  have hf : f ≠ 0 := turnFunctional_ne_zero (by
    intro hic
    have hdisj := Set.disjoint_left.mp
      (disjoint_interior_extremePoints (convexHull ℝ (Set.range p)))
    exact hdisj hc (hic ▸ hi))
  have hvertex : ∀ k ∈ hullVertexIndices p, f (p k) ≤ f c := by
    intro k hk
    have hturn := h k hk
    rw [turn_eq_turnFunctional_sub] at hturn
    exact sub_nonpos.mp hturn
  have hpoints : ∀ k, f (p k) ≤ f c :=
    linear_le_of_hullVertexIndices_le p f.toLinearMap (f c) hvertex
  have hC : ∀ q ∈ convexHull ℝ (Set.range p), f q ≤ f c := by
    intro q hq
    have hsub : convexHull ℝ (Set.range p) ⊆ {x : Point | f x ≤ f c} := by
      apply convexHull_min
      · rintro x ⟨k, rfl⟩
        exact hpoints k
      · exact convex_halfSpace_le f.toLinearMap.isLinear _
    exact hsub hq
  have hlt := linear_lt_bound_at_interior f hf _ _ hC hc
  exact (lt_irrefl (f c)) hlt

private theorem sin_nonpos_of_pi_le_of_le_two_pi {x : ℝ}
    (hπ : Real.pi ≤ x) (h2π : x ≤ 2 * Real.pi) :
    Real.sin x ≤ 0 := by
  have h : 0 ≤ Real.sin (x - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub_pi] at h
  linarith

/-- There is less than a half-turn between consecutive vertex arguments
on the principal branch. -/
theorem hull_adjacent_arg_gap_lt_pi {n : ℕ} (p : Fin n → Point)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j : Fin n)
    (hi : i ∈ hullVertexIndices p) (_hj : j ∈ hullVertexIndices p)
    (_harg : (pointToComplex (p i - c)).arg < (pointToComplex (p j - c)).arg)
    (hempty : ∀ k ∈ hullVertexIndices p,
      ¬ ((pointToComplex (p i - c)).arg < (pointToComplex (p k - c)).arg ∧
         (pointToComplex (p k - c)).arg < (pointToComplex (p j - c)).arg)) :
    (pointToComplex (p j - c)).arg - (pointToComplex (p i - c)).arg < Real.pi := by
  classical
  let α := (pointToComplex (p i - c)).arg
  let β := (pointToComplex (p j - c)).arg
  by_contra hgap
  have hgap' : Real.pi ≤ β - α := le_of_not_gt hgap
  have hαlo : -Real.pi < α := (Complex.arg_mem_Ioc _).1
  have hβhi : β ≤ Real.pi := (Complex.arg_mem_Ioc _).2
  have hαnonpos : α ≤ 0 := by linarith
  have hei : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hi).2
  obtain ⟨k, hk, hturn⟩ := exists_hull_vertex_positive_turn p c hc i hei
  let γ := (pointToComplex (p k - c)).arg
  have hγlo : -Real.pi < γ := (Complex.arg_mem_Ioc _).1
  have hγhi : γ ≤ Real.pi := (Complex.arg_mem_Ioc _).2
  have houtside : γ ≤ α ∨ β ≤ γ := by
    by_cases hle : γ ≤ α
    · exact Or.inl hle
    · right
      by_contra hn
      exact hempty k hk ⟨lt_of_not_ge hle, lt_of_not_ge hn⟩
  have hsin : Real.sin (γ - α) ≤ 0 := by
    rcases houtside with hle | hge
    · exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    · exact sin_nonpos_of_pi_le_of_le_two_pi (by linarith) (by linarith)
  have hturn' : turn c (p i) (p k) =
      ‖pointToComplex (p i - c)‖ * ‖pointToComplex (p k - c)‖ *
        Real.sin (γ - α) := by
    rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub]
  have hturnle : turn c (p i) (p k) ≤ 0 := by
    rw [hturn']
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsin
  linarith

/-- The total principal-argument span of all hull vertices exceeds a half-turn.
Thus the gap crossing the branch cut is less than a half-turn. -/
theorem hull_arg_extremal_span_gt_pi {n : ℕ} (p : Fin n → Point)
    (c : Point) (hc : c ∈ interior (convexHull ℝ (Set.range p)))
    (i j : Fin n)
    (_hi : i ∈ hullVertexIndices p) (hj : j ∈ hullVertexIndices p)
    (hmin : ∀ k ∈ hullVertexIndices p,
      (pointToComplex (p i - c)).arg ≤ (pointToComplex (p k - c)).arg)
    (hmax : ∀ k ∈ hullVertexIndices p,
      (pointToComplex (p k - c)).arg ≤ (pointToComplex (p j - c)).arg) :
    Real.pi < (pointToComplex (p j - c)).arg - (pointToComplex (p i - c)).arg := by
  classical
  let α := (pointToComplex (p i - c)).arg
  let β := (pointToComplex (p j - c)).arg
  by_contra hspan
  have hspan' : β - α ≤ Real.pi := le_of_not_gt hspan
  have hej : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hj).2
  obtain ⟨k, hk, hturn⟩ := exists_hull_vertex_positive_turn p c hc j hej
  let γ := (pointToComplex (p k - c)).arg
  have hγbounds : α ≤ γ ∧ γ ≤ β := ⟨hmin k hk, hmax k hk⟩
  have hsin : Real.sin (γ - β) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have hturn' : turn c (p j) (p k) =
      ‖pointToComplex (p j - c)‖ * ‖pointToComplex (p k - c)‖ *
        Real.sin (γ - β) := by
    rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub]
  have hturnle : turn c (p j) (p k) ≤ 0 := by
    rw [hturn']
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsin
  linarith

end Erdos957
