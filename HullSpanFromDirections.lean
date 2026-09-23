import NormalizedHullEdges
import HullSpanInterpolation
import SmallAngleProjection

/-! Short nearly horizontal hull chains supply the actual shallow hull span. -/

namespace Erdos957

noncomputable def normalizedHullSpan_of_nearby_edge_args {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h) (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hsupport : ∀ k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (harg : ∀ j : Fin h,
      (j = i + 1 ∨ j = (i + 1) + 1 ∨ j = i - 1 ∨
        j = (i - 1) - 1 ∨ j = ((i - 1) - 1) - 1) →
      |(hullEdgeDirection p v j / hullEdgeDirection p v i).arg| ≤ Real.pi / 600) :
    NormalizedHullSpan p (v (i + 1)) (v i) := by
  let M := edgeCoordinate (p (v (i + 1))) (p (v i))
  let r (j : Fin h) := hullEdgeDirection p v j / hullEdgeDirection p v i
  have hdir (j : Fin h)
      (hj : j = i + 1 ∨ j = (i + 1) + 1 ∨ j = i - 1 ∨
        j = (i - 1) - 1 ∨ j = ((i - 1) - 1) - 1) :
      (99 / 100 : ℝ) ≤ (r j).re ∧ |(r j).im| ≤ (r j).re / 30 := by
    have ha := harg j hj
    have hnrm := hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase j
    exact ⟨(small_arg_unit_projection (r j) ha hnrm).1,
      (small_arg_projection (r j) ha).2⟩
  obtain ⟨hL₁re, hL₁im⟩ := hdir (i + 1) (Or.inl rfl)
  obtain ⟨hL₂re, hL₂im⟩ := hdir ((i + 1) + 1) (Or.inr (Or.inl rfl))
  obtain ⟨hR₁re, hR₁im⟩ := hdir (i - 1) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hR₂re, hR₂im⟩ := hdir ((i - 1) - 1)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨hR₃re, hR₃im⟩ := hdir (((i - 1) - 1) - 1)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hne : p (v (i + 1)) ≠ p (v i) := hp.ne hbase.ne.symm
  let A := p (v (((i + 1) + 1) + 1))
  let B := p (v (((i - 1) - 1) - 1))
  have hA : M A = -r (i + 1) - r ((i + 1) + 1) :=
    normalized_hull_left_two_sum p v i
  have hB : M B = 1 + r (i - 1) + r ((i - 1) - 1) + r (((i - 1) - 1) - 1) :=
    normalized_hull_right_three_sum p v i hne
  have hAre : (M A).re = -(r (i + 1)).re - (r ((i + 1) + 1)).re := by
    rw [hA, Complex.sub_re, Complex.neg_re]
  have hAim : (M A).im = -(r (i + 1)).im - (r ((i + 1) + 1)).im := by
    rw [hA, Complex.sub_im, Complex.neg_im]
  have hBre : (M B).re = 1 + (r (i - 1)).re +
      (r ((i - 1) - 1)).re + (r (((i - 1) - 1) - 1)).re := by
    rw [hB]
    simp only [Complex.add_re, Complex.one_re]
  have hBim : (M B).im = (r (i - 1)).im +
      (r ((i - 1) - 1)).im + (r (((i - 1) - 1) - 1)).im := by
    rw [hB]
    simp only [Complex.add_im, Complex.one_im, zero_add]
  apply normalizedHullSpan_of_shallow_rays p (v (i + 1)) (v i) A B
    (subset_convexHull ℝ _ (Set.mem_range_self _))
    (subset_convexHull ℝ _ (Set.mem_range_self _))
  · change (M A).re ≤ -1
    linarith
  · change (M A).re / 10 ≤ (M A).im
    have h₁ := (abs_le.mp hL₁im).2
    have h₂ := (abs_le.mp hL₂im).2
    linarith
  · exact edgeCoordinate_im_nonpos_of_support _ _ _ hne (hsupport _)
  · change 3 ≤ (M B).re
    linarith
  · change -(M B).re / 30 ≤ (M B).im
    have h₁ := (abs_le.mp hR₁im).1
    have h₂ := (abs_le.mp hR₂im).1
    have h₃ := (abs_le.mp hR₃im).1
    linarith
  · exact edgeCoordinate_im_nonpos_of_support _ _ _ hne (hsupport _)

end Erdos957
