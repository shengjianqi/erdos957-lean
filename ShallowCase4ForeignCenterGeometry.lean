import ShallowCase4CenterExclusion
import SharedFiveSixExtensionExclusion
import TightFlatChord
import ExtendedFlatDirections
import SmallAngleProjection
import LocalScalarBridgeCompatibility

/-! Geometry for the last same-center Case-4 branch.  Two degree-five
shared-five centers supported by disjoint nearby nearest hull edges cannot
itself be nearest neighbors once the edges are separated by at least one
intervening tight-flat hull edge. -/

namespace Erdos957

/-- If two actual hull edges are both minimum-distance edges, their direction
ratio has unit norm. -/
theorem hullEdgeDirection_div_norm_eq_one_of_nearest
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i j : Fin h)
    (hi : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hj : (nearestGraph p).Adj (v j) (v (j + 1))) :
    ‖hullEdgeDirection p v j / hullEdgeDirection p v i‖ = 1 := by
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  have hnorm (k : Fin h) : ‖hullEdgeDirection p v k‖ =
      dist (p (v k)) (p (v (k + 1))) := by
    rw [hullEdgeDirection, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [norm_div, hnorm, hnorm,
    nearestGraph_adj_dist_eq p hmin hj,
    nearestGraph_adj_dist_eq p hmin hi, div_self hδ.ne']

/-- The positive algebraic height of a unit equilateral triangle is strictly
smaller than one.  Keeping this elementary fact separate makes the projection
estimate below insensitive to square-root normalization details. -/
theorem equilateral_height_lt_one (H : ℝ) (hHpos : 0 < H)
    (hHsq : H ^ 2 = 3 / 4) : H < 1 := by
  nlinarith

/-- A height between zero and one cannot amplify the negative part of a
small transverse edge component. -/
theorem unit_height_mul_small_im_lower (H y : ℝ)
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hy : |y| ≤ 1 / 30) :
    -(1 / 30 : ℝ) ≤ H * y := by
  have hylo : -(1 / 30 : ℝ) ≤ y := (abs_le.mp hy).1
  by_cases hy0 : 0 ≤ y
  · have hprod : 0 ≤ H * y := mul_nonneg hH0 hy0
    linarith
  · have hynonpos : y ≤ 0 := le_of_not_ge hy0
    have hmul : y ≤ H * y := by
      have hh := mul_le_mul_of_nonpos_right hH1 hynonpos
      simpa using hh
    exact hylo.trans hmul

/-- Symmetric upper bound for the same product. -/
theorem unit_height_mul_small_im_upper (H y : ℝ)
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hy : |y| ≤ 1 / 30) :
    H * y ≤ 1 / 30 := by
  have hyhi : y ≤ (1 / 30 : ℝ) := (abs_le.mp hy).2
  by_cases hy0 : y ≤ 0
  · have hprod : H * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hH0 hy0
    linarith
  · have hypos : 0 ≤ y := le_of_not_ge hy0
    have hmul : H * y ≤ y := by
      have hh := mul_le_mul_of_nonneg_right hH1 hypos
      simpa using hh
    exact hmul.trans hyhi

/-- Two supported shared-five centers on the nearest hull edges `i` and
`i+2` cannot be nearest neighbors.  The proof uses only the tight-flat
projection bounds: in the frame of the first edge their real coordinates are
separated by more than one minimum length. -/
theorem sharedFive_centers_forward_two_edges_not_nearest
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v ((((i + 1) + 1) + 1)))
    (hsecondR : second.right = v ((i + 1) + 1)) :
    ¬ (nearestGraph p).Adj q q' := by
  intro hqq
  let H : ℝ := Real.sqrt 3 / 2
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hHsq : H ^ 2 = 3 / 4 := by
    dsimp [H]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hHlt : H < 1 := equilateral_height_lt_one H hHpos hHsq
  have hAB : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let e₁ := hullEdgeDirection p v (i + 1) / hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v ((i + 1) + 1) / hullEdgeDirection p v i
  have hbase₀ : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hfirstL, hfirstR] using first.base.symm
  have hbase₂ : (nearestGraph p).Adj (v ((i + 1) + 1))
      (v (((i + 1) + 1) + 1)) := by
    simpa only [hsecondL, hsecondR] using second.base.symm
  have hqrev := first.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq : M (p q) = (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    dsimp only [M]
    rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) (p q) hAB.symm]
    rw [← hfirstL, ← hfirstR, hqrev]
    ring
  have hCD : p (v ((i + 1) + 1)) ≠ p (v (((i + 1) + 1) + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh ((i + 1) + 1)).1)
  have hq'rev := second.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq'local :
      edgeCoordinate (p (v ((i + 1) + 1)))
        (p (v (((i + 1) + 1) + 1))) (p q') =
        (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    rw [edgeCoordinate_swap_base
      (p (v (((i + 1) + 1) + 1))) (p (v ((i + 1) + 1))) (p q') hCD.symm]
    rw [← hsecondL, ← hsecondR, hq'rev]
    ring
  have hMC : M (p (v ((i + 1) + 1))) = 1 + e₁ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (i + 1))) (p (v ((i + 1) + 1)))
    have hs' : M (p (v ((i + 1) + 1))) - M (p (v (i + 1))) = e₁ := by
      simpa only [M, e₁, hullEdgeDirection, sub_add_cancel] using hs
    have haxis : M (p (v (i + 1))) = 1 := edgeCoordinate_axis _ _ hAB
    calc
      M (p (v ((i + 1) + 1))) =
          (M (p (v ((i + 1) + 1))) - M (p (v (i + 1)))) +
            M (p (v (i + 1))) := by ring
      _ = e₁ + 1 := by rw [hs', haxis]
      _ = 1 + e₁ := by ring
  have hMDsub :
      M (p (v (((i + 1) + 1) + 1))) - M (p (v ((i + 1) + 1))) = e₂ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v ((i + 1) + 1))) (p (v (((i + 1) + 1) + 1)))
    simpa only [M, e₂, hullEdgeDirection, sub_add_cancel] using hs
  have hq' : M (p q') = 1 + e₁ +
      ((1 / 2 : ℂ) + (H : ℂ) * Complex.I) * e₂ := by
    dsimp only [M]
    rw [edgeCoordinate_affine_change
      (p (v i)) (p (v (i + 1)))
      (p (v ((i + 1) + 1))) (p (v (((i + 1) + 1) + 1))) (p q')
      hAB hCD]
    dsimp only [M] at hMC hMDsub
    rw [hMDsub, hMC, hq'local]
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i hgood
  have hargs := tight_hull_nearby_edge_args p hp v hv hh i hpos
    hi hm1 hm2 hp1 hp2
  have he₁arg : |e₁.arg| ≤ Real.pi / 600 := by
    dsimp [e₁]
    exact hargs (i + 1) (Or.inl rfl)
  have he₂arg : |e₂.arg| ≤ Real.pi / 600 := by
    dsimp [e₂]
    exact hargs ((i + 1) + 1) (Or.inr (Or.inl rfl))
  have he₁norm : 1 ≤ ‖e₁‖ := by
    dsimp [e₁]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ (i + 1)
  have he₂norm : ‖e₂‖ = 1 := by
    dsimp [e₂]
    exact hullEdgeDirection_div_norm_eq_one_of_nearest
      p hn hp v hv hh i ((i + 1) + 1) hbase₀ hbase₂
  have he₁re : (99 / 100 : ℝ) ≤ e₁.re :=
    (small_arg_unit_projection e₁ he₁arg he₁norm).1
  have he₂norm_ge : 1 ≤ ‖e₂‖ := by rw [he₂norm]
  have he₂re : (99 / 100 : ℝ) ≤ e₂.re :=
    (small_arg_unit_projection e₂ he₂arg he₂norm_ge).1
  have he₂re_le : e₂.re ≤ 1 := by
    simpa only [he₂norm] using Complex.re_le_norm e₂
  have he₂im : |e₂.im| ≤ 1 / 30 := by
    have him := (small_arg_projection e₂ he₂arg).2
    have hre : e₂.re ≤ 1 := by simpa only [he₂norm] using Complex.re_le_norm e₂
    linarith
  have hreal : 1 < (M (p q') - M (p q)).re := by
    rw [hq', hq]
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_upper H e₂.im hHpos.le hHlt.le he₂im
    nlinarith
  have hcoord : 1 < dist (M (p q)) (M (p q')) := by
    rw [dist_comm, dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  rw [edgeCoordinate_dist _ _ _ _ hAB,
    nearestGraph_adj_dist_eq p hmin hqq,
    nearestGraph_adj_dist_eq p hmin hbase₀,
    div_self hδ.ne'] at hcoord
  linarith

end Erdos957

namespace Erdos957

/-- The same separation with two intervening hull edges.  The radius-three
flatness certificate controls the direction of the `i+3` edge through the
existing eight-edge projection theorem. -/
theorem sharedFive_centers_forward_three_edges_not_nearest
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v (((((i + 1) + 1) + 1) + 1)))
    (hsecondR : second.right = v (((i + 1) + 1) + 1)) :
    ¬ (nearestGraph p).Adj q q' := by
  intro hqq
  let H : ℝ := Real.sqrt 3 / 2
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hHsq : H ^ 2 = 3 / 4 := by
    dsimp [H]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hHlt : H < 1 := equilateral_height_lt_one H hHpos hHsq
  have hAB : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let e₁ := hullEdgeDirection p v (i + 1) / hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v ((i + 1) + 1) / hullEdgeDirection p v i
  let e₃ := hullEdgeDirection p v (((i + 1) + 1) + 1) / hullEdgeDirection p v i
  have hbase₀ : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hfirstL, hfirstR] using first.base.symm
  have hbase₃ : (nearestGraph p).Adj (v (((i + 1) + 1) + 1))
      (v ((((i + 1) + 1) + 1) + 1)) := by
    simpa only [hsecondL, hsecondR] using second.base.symm
  have hqrev := first.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq : M (p q) = (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    dsimp only [M]
    rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) (p q) hAB.symm]
    rw [← hfirstL, ← hfirstR, hqrev]
    ring
  have hCD : p (v (((i + 1) + 1) + 1)) ≠
      p (v ((((i + 1) + 1) + 1) + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh (((i + 1) + 1) + 1)).1)
  have hq'rev := second.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq'local :
      edgeCoordinate (p (v (((i + 1) + 1) + 1)))
        (p (v ((((i + 1) + 1) + 1) + 1))) (p q') =
        (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    rw [edgeCoordinate_swap_base
      (p (v ((((i + 1) + 1) + 1) + 1)))
      (p (v (((i + 1) + 1) + 1))) (p q') hCD.symm]
    rw [← hsecondL, ← hsecondR, hq'rev]
    ring
  have hMB : M (p (v (i + 1))) = 1 := edgeCoordinate_axis _ _ hAB
  have hE1 :
      M (p (v ((i + 1) + 1))) - M (p (v (i + 1))) = e₁ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (i + 1))) (p (v ((i + 1) + 1)))
    simpa only [M, e₁, hullEdgeDirection, sub_add_cancel] using hs
  have hE2 :
      M (p (v (((i + 1) + 1) + 1))) - M (p (v ((i + 1) + 1))) = e₂ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v ((i + 1) + 1))) (p (v (((i + 1) + 1) + 1)))
    simpa only [M, e₂, hullEdgeDirection, sub_add_cancel] using hs
  have hMC : M (p (v (((i + 1) + 1) + 1))) = 1 + e₁ + e₂ := by
    calc
      M (p (v (((i + 1) + 1) + 1))) =
          (M (p (v (((i + 1) + 1) + 1))) - M (p (v ((i + 1) + 1)))) +
          (M (p (v ((i + 1) + 1))) - M (p (v (i + 1)))) +
          M (p (v (i + 1))) := by ring
      _ = e₂ + e₁ + 1 := by rw [hE2, hE1, hMB]
      _ = 1 + e₁ + e₂ := by ring
  have hMDsub :
      M (p (v ((((i + 1) + 1) + 1) + 1))) -
        M (p (v (((i + 1) + 1) + 1))) = e₃ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (((i + 1) + 1) + 1)))
      (p (v ((((i + 1) + 1) + 1) + 1)))
    simpa only [M, e₃, hullEdgeDirection, sub_add_cancel] using hs
  have hq' : M (p q') = 1 + e₁ + e₂ +
      ((1 / 2 : ℂ) + (H : ℂ) * Complex.I) * e₃ := by
    dsimp only [M]
    rw [edgeCoordinate_affine_change
      (p (v i)) (p (v (i + 1)))
      (p (v (((i + 1) + 1) + 1)))
      (p (v ((((i + 1) + 1) + 1) + 1))) (p q')
      hAB hCD]
    dsimp only [M] at hMC hMDsub
    rw [hMDsub, hMC, hq'local]
  have harg (j : Fin h)
      (hj : j = i + 1 ∨ j = (i + 1) + 1 ∨ j = ((i + 1) + 1) + 1) :
      |(hullEdgeDirection p v j / hullEdgeDirection p v i).arg| ≤ Real.pi / 300 := by
    apply tight_hull_eight_edge_args p hp v hv hh i hpos hgood j
    rcases hj with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have he₁arg : |e₁.arg| ≤ Real.pi / 300 := by
    dsimp [e₁]
    exact harg (i + 1) (Or.inl rfl)
  have he₂arg : |e₂.arg| ≤ Real.pi / 300 := by
    dsimp [e₂]
    exact harg ((i + 1) + 1) (Or.inr (Or.inl rfl))
  have he₃arg : |e₃.arg| ≤ Real.pi / 300 := by
    dsimp [e₃]
    exact harg (((i + 1) + 1) + 1) (Or.inr (Or.inr rfl))
  have he₁norm : 1 ≤ ‖e₁‖ := by
    dsimp [e₁]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ (i + 1)
  have he₂norm : 1 ≤ ‖e₂‖ := by
    dsimp [e₂]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ ((i + 1) + 1)
  have he₃norm : ‖e₃‖ = 1 := by
    dsimp [e₃]
    exact hullEdgeDirection_div_norm_eq_one_of_nearest
      p hn hp v hv hh i (((i + 1) + 1) + 1) hbase₀ hbase₃
  have he₁re : (99 / 100 : ℝ) ≤ e₁.re := by
    have hpj := (extended_small_arg_projection e₁ he₁arg).1
    nlinarith
  have he₂re : (99 / 100 : ℝ) ≤ e₂.re := by
    have hpj := (extended_small_arg_projection e₂ he₂arg).1
    nlinarith
  have he₃re : (99 / 100 : ℝ) ≤ e₃.re := by
    have hpj := (extended_small_arg_projection e₃ he₃arg).1
    rw [he₃norm] at hpj
    simpa using hpj
  have he₃re_le : e₃.re ≤ 1 := by
    simpa only [he₃norm] using Complex.re_le_norm e₃
  have he₃im : |e₃.im| ≤ 1 / 30 := by
    have him := (extended_small_arg_projection e₃ he₃arg).2
    linarith
  have hreal : 1 < (M (p q') - M (p q)).re := by
    rw [hq', hq]
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_upper H e₃.im hHpos.le hHlt.le he₃im
    nlinarith
  have hcoord : 1 < dist (M (p q)) (M (p q')) := by
    rw [dist_comm, dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  rw [edgeCoordinate_dist _ _ _ _ hAB,
    nearestGraph_adj_dist_eq p hmin hqq,
    nearestGraph_adj_dist_eq p hmin hbase₀,
    div_self hδ.ne'] at hcoord
  linarith

end Erdos957

namespace Erdos957


/-- Backward two-edge analogue of `sharedFive_centers_forward_two_edges_not_nearest`.
The base edge is supported at the good donor `i`, while the second retained
shared-five edge starts at `i-2`. -/
theorem sharedFive_centers_backward_two_edges_not_nearest
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v (i - 1))
    (hsecondR : second.right = v ((i - 1) - 1)) :
    ¬ (nearestGraph p).Adj q q' := by
  intro hqq
  let H : ℝ := Real.sqrt 3 / 2
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hHsq : H ^ 2 = 3 / 4 := by
    dsimp [H]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hHlt : H < 1 := equilateral_height_lt_one H hHpos hHsq
  have hAB : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let e₁ := hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v ((i - 1) - 1) / hullEdgeDirection p v i
  have hbase₀ : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hfirstL, hfirstR] using first.base.symm
  have hbase₂ : (nearestGraph p).Adj (v ((i - 1) - 1)) (v (i - 1)) := by
    simpa only [hsecondL, hsecondR] using second.base.symm
  have hqrev := first.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq : M (p q) = (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    dsimp only [M]
    rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) (p q) hAB.symm]
    rw [← hfirstL, ← hfirstR, hqrev]
    ring
  have hCD : p (v ((i - 1) - 1)) ≠ p (v (i - 1)) :=
    hp.ne (hv.ne (by simpa only [sub_add_cancel] using
      (cyclic_three_distinct hh ((i - 1) - 1)).1))
  have hq'rev := second.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq'local :
      edgeCoordinate (p (v ((i - 1) - 1))) (p (v (i - 1))) (p q') =
        (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    rw [edgeCoordinate_swap_base
      (p (v (i - 1))) (p (v ((i - 1) - 1))) (p q') hCD.symm]
    rw [← hsecondL, ← hsecondR, hq'rev]
    ring
  have hMprev : M (p (v (i - 1))) = -e₁ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (i - 1))) (p (v i))
    have hs' : M (p (v i)) - M (p (v (i - 1))) = e₁ := by
      simpa only [M, e₁, hullEdgeDirection, sub_add_cancel] using hs
    have hself : M (p (v i)) = 0 := edgeCoordinate_self _ _
    rw [hself] at hs'
    simp only [zero_sub] at hs'
    calc
      M (p (v (i - 1))) = -(-M (p (v (i - 1)))) := by ring
      _ = -e₁ := by rw [hs']
  have hMright : M (p (v ((i - 1) - 1))) = -e₁ - e₂ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v ((i - 1) - 1))) (p (v (i - 1)))
    have hs' : M (p (v (i - 1))) - M (p (v ((i - 1) - 1))) = e₂ := by
      simpa only [M, e₂, hullEdgeDirection, sub_add_cancel] using hs
    rw [hMprev] at hs'
    calc
      M (p (v ((i - 1) - 1))) = -e₁ - (-e₁ - M (p (v ((i - 1) - 1)))) := by ring
      _ = -e₁ - e₂ := by rw [hs']
  have hMsub :
      M (p (v (i - 1))) - M (p (v ((i - 1) - 1))) = e₂ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v ((i - 1) - 1))) (p (v (i - 1)))
    simpa only [M, e₂, hullEdgeDirection, sub_add_cancel] using hs
  have hq' : M (p q') = -e₁ - e₂ +
      ((1 / 2 : ℂ) + (H : ℂ) * Complex.I) * e₂ := by
    dsimp only [M]
    rw [edgeCoordinate_affine_change
      (p (v i)) (p (v (i + 1)))
      (p (v ((i - 1) - 1))) (p (v (i - 1))) (p q') hAB hCD]
    dsimp only [M] at hMright hMsub
    rw [hMsub, hMright, hq'local]
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i hgood
  have hargs := tight_hull_nearby_edge_args p hp v hv hh i hpos
    hi hm1 hm2 hp1 hp2
  have he₁arg : |e₁.arg| ≤ Real.pi / 600 := by
    dsimp [e₁]
    exact hargs (i - 1) (Or.inr (Or.inr (Or.inl rfl)))
  have he₂arg : |e₂.arg| ≤ Real.pi / 600 := by
    dsimp [e₂]
    exact hargs ((i - 1) - 1) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have he₁norm : 1 ≤ ‖e₁‖ := by
    dsimp [e₁]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ (i - 1)
  have he₂norm : ‖e₂‖ = 1 := by
    dsimp [e₂]
    exact hullEdgeDirection_div_norm_eq_one_of_nearest
      p hn hp v hv hh i ((i - 1) - 1) hbase₀
        (by simpa only [sub_add_cancel] using hbase₂)
  have he₂norm_ge : 1 ≤ ‖e₂‖ := by rw [he₂norm]
  have he₁re : (99 / 100 : ℝ) ≤ e₁.re :=
    (small_arg_unit_projection e₁ he₁arg he₁norm).1
  have he₂re : (99 / 100 : ℝ) ≤ e₂.re :=
    (small_arg_unit_projection e₂ he₂arg he₂norm_ge).1
  have he₂im : |e₂.im| ≤ 1 / 30 := by
    have him := (small_arg_projection e₂ he₂arg).2
    have hre : e₂.re ≤ 1 := by simpa only [he₂norm] using Complex.re_le_norm e₂
    linarith
  have hreal : 1 < (M (p q) - M (p q')).re := by
    rw [hq, hq']
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_lower H e₂.im hHpos.le hHlt.le he₂im
    nlinarith
  have hcoord : 1 < dist (M (p q)) (M (p q')) := by
    rw [dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  rw [edgeCoordinate_dist _ _ _ _ hAB,
    nearestGraph_adj_dist_eq p hmin hqq,
    nearestGraph_adj_dist_eq p hmin hbase₀,
    div_self hδ.ne'] at hcoord
  linarith

/-- Backward three-edge analogue of the center-separation estimate. -/
theorem sharedFive_centers_backward_three_edges_not_nearest
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v ((i - 1) - 1))
    (hsecondR : second.right = v (((i - 1) - 1) - 1)) :
    ¬ (nearestGraph p).Adj q q' := by
  intro hqq
  let H : ℝ := Real.sqrt 3 / 2
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hHsq : H ^ 2 = 3 / 4 := by
    dsimp [H]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hHlt : H < 1 := equilateral_height_lt_one H hHpos hHsq
  have hAB : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  let e₁ := hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v ((i - 1) - 1) / hullEdgeDirection p v i
  let e₃ := hullEdgeDirection p v (((i - 1) - 1) - 1) / hullEdgeDirection p v i
  have hbase₀ : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hfirstL, hfirstR] using first.base.symm
  have hbase₃ : (nearestGraph p).Adj (v (((i - 1) - 1) - 1))
      (v ((i - 1) - 1)) := by
    simpa only [hsecondL, hsecondR] using second.base.symm
  have hqrev := first.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq : M (p q) = (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    dsimp only [M]
    rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) (p q) hAB.symm]
    rw [← hfirstL, ← hfirstR, hqrev]
    ring
  have hCD : p (v (((i - 1) - 1) - 1)) ≠ p (v ((i - 1) - 1)) :=
    hp.ne (hv.ne (by simpa only [sub_add_cancel] using
      (cyclic_three_distinct hh (((i - 1) - 1) - 1)).1))
  have hq'rev := second.center_coordinate_with_height p hn hp H hHpos hHsq
  have hq'local : edgeCoordinate (p (v (((i - 1) - 1) - 1)))
      (p (v ((i - 1) - 1))) (p q') =
        (1 / 2 : ℂ) + (H : ℂ) * Complex.I := by
    rw [edgeCoordinate_swap_base
      (p (v ((i - 1) - 1))) (p (v (((i - 1) - 1) - 1))) (p q') hCD.symm]
    rw [← hsecondL, ← hsecondR, hq'rev]
    ring
  have hM1 : M (p (v (i - 1))) = -e₁ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (i - 1))) (p (v i))
    have hs' : M (p (v i)) - M (p (v (i - 1))) = e₁ := by
      simpa only [M, e₁, hullEdgeDirection, sub_add_cancel] using hs
    have hself : M (p (v i)) = 0 := edgeCoordinate_self _ _
    rw [hself] at hs'
    simp only [zero_sub] at hs'
    calc
      M (p (v (i - 1))) = -(-M (p (v (i - 1)))) := by ring
      _ = -e₁ := by rw [hs']
  have hM2 : M (p (v ((i - 1) - 1))) = -e₁ - e₂ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v ((i - 1) - 1))) (p (v (i - 1)))
    have hs' : M (p (v (i - 1))) - M (p (v ((i - 1) - 1))) = e₂ := by
      simpa only [M, e₂, hullEdgeDirection, sub_add_cancel] using hs
    rw [hM1] at hs'
    calc
      M (p (v ((i - 1) - 1))) = -e₁ - (-e₁ - M (p (v ((i - 1) - 1)))) := by ring
      _ = -e₁ - e₂ := by rw [hs']
  have hM3 : M (p (v (((i - 1) - 1) - 1))) = -e₁ - e₂ - e₃ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (((i - 1) - 1) - 1))) (p (v ((i - 1) - 1)))
    have hs' : M (p (v ((i - 1) - 1))) -
        M (p (v (((i - 1) - 1) - 1))) = e₃ := by
      simpa only [M, e₃, hullEdgeDirection, sub_add_cancel] using hs
    rw [hM2] at hs'
    calc
      M (p (v (((i - 1) - 1) - 1))) =
          -e₁ - e₂ - (-e₁ - e₂ - M (p (v (((i - 1) - 1) - 1)))) := by ring
      _ = -e₁ - e₂ - e₃ := by rw [hs']
  have hMsub : M (p (v ((i - 1) - 1))) -
      M (p (v (((i - 1) - 1) - 1))) = e₃ := by
    have hs := edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
      (p (v (((i - 1) - 1) - 1))) (p (v ((i - 1) - 1)))
    simpa only [M, e₃, hullEdgeDirection, sub_add_cancel] using hs
  have hq' : M (p q') = -e₁ - e₂ - e₃ +
      ((1 / 2 : ℂ) + (H : ℂ) * Complex.I) * e₃ := by
    dsimp only [M]
    rw [edgeCoordinate_affine_change
      (p (v i)) (p (v (i + 1)))
      (p (v (((i - 1) - 1) - 1))) (p (v ((i - 1) - 1))) (p q') hAB hCD]
    dsimp only [M] at hM3 hMsub
    rw [hMsub, hM3, hq'local]
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ :=
    tight_hull_five_turns_of_not_bad p v hv i hgood
  have hargs := tight_hull_nearby_edge_args p hp v hv hh i hpos
    hi hm1 hm2 hp1 hp2
  have he₁arg : |e₁.arg| ≤ Real.pi / 600 := by
    dsimp [e₁]
    exact hargs (i - 1) (Or.inr (Or.inr (Or.inl rfl)))
  have he₂arg : |e₂.arg| ≤ Real.pi / 600 := by
    dsimp [e₂]
    exact hargs ((i - 1) - 1) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have he₃arg : |e₃.arg| ≤ Real.pi / 600 := by
    dsimp [e₃]
    exact hargs (((i - 1) - 1) - 1)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have he₁norm : 1 ≤ ‖e₁‖ := by
    dsimp [e₁]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ (i - 1)
  have he₂norm : 1 ≤ ‖e₂‖ := by
    dsimp [e₂]
    exact hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase₀ ((i - 1) - 1)
  have he₃norm : ‖e₃‖ = 1 := by
    dsimp [e₃]
    exact hullEdgeDirection_div_norm_eq_one_of_nearest
      p hn hp v hv hh i (((i - 1) - 1) - 1) hbase₀
        (by simpa only [sub_add_cancel] using hbase₃)
  have he₃norm_ge : 1 ≤ ‖e₃‖ := by rw [he₃norm]
  have he₁re : (99 / 100 : ℝ) ≤ e₁.re :=
    (small_arg_unit_projection e₁ he₁arg he₁norm).1
  have he₂re : (99 / 100 : ℝ) ≤ e₂.re :=
    (small_arg_unit_projection e₂ he₂arg he₂norm).1
  have he₃re : (99 / 100 : ℝ) ≤ e₃.re :=
    (small_arg_unit_projection e₃ he₃arg he₃norm_ge).1
  have he₃im : |e₃.im| ≤ 1 / 30 := by
    have him := (small_arg_projection e₃ he₃arg).2
    have hre : e₃.re ≤ 1 := by simpa only [he₃norm] using Complex.re_le_norm e₃
    linarith
  have hreal : 1 < (M (p q) - M (p q')).re := by
    rw [hq, hq']
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_lower H e₃.im hHpos.le hHlt.le he₃im
    nlinarith
  have hcoord : 1 < dist (M (p q)) (M (p q')) := by
    rw [dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  rw [edgeCoordinate_dist _ _ _ _ hAB,
    nearestGraph_adj_dist_eq p hmin hqq,
    nearestGraph_adj_dist_eq p hmin hbase₀,
    div_self hδ.ne'] at hcoord
  linarith

/-- If two distinct hull sources are exactly the two endpoints of a retained
shared-five edge, one of them is the right endpoint and the other is its
cyclic successor.  This packages the orientation without choosing in advance
which source is on which side. -/
theorem SharedFiveCenterChoice.oriented_edge_of_two_endpoints
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    {q : Fin n} (five : SharedFiveCenterChoice p q)
    (j k : Fin h) (hjk : j ≠ k)
    (hj : v j = five.left ∨ v j = five.right)
    (hk : v k = five.left ∨ v k = five.right) :
    ∃ s : Fin h,
      (s = j ∨ s = k) ∧ (s + 1 = j ∨ s + 1 = k) ∧
      five.right = v s ∧ five.left = v (s + 1) := by
  rcases hj with hjL | hjR <;> rcases hk with hkL | hkR
  · exfalso
    apply hjk
    apply hv
    exact hjL.trans hkL.symm
  · refine ⟨k, Or.inr rfl, Or.inl ?_, hkR.symm, ?_⟩
    · apply hv
      calc
        v (k + 1) = five.left := by
          symm
          exact five.left_eq_cyclic_successor_of_right
            p hp v hv hh hrange hsupport k hkR.symm
        _ = v j := hjL.symm
    · exact five.left_eq_cyclic_successor_of_right
        p hp v hv hh hrange hsupport k hkR.symm
  · refine ⟨j, Or.inl rfl, Or.inr ?_, hjR.symm, ?_⟩
    · apply hv
      calc
        v (j + 1) = five.left := by
          symm
          exact five.left_eq_cyclic_successor_of_right
            p hp v hv hh hrange hsupport j hjR.symm
        _ = v k := hkL.symm
    · exact five.left_eq_cyclic_successor_of_right
        p hp v hv hh hrange hsupport j hjR.symm
  · exfalso
    apply hjk
    apply hv
    exact hjR.trans hkR.symm

/-- A local hull edge disjoint from the forward anchor edge `[i,i+1]` and
whose right endpoint is in the six-source neighborhood starts exactly two or
three edges away on one side. -/
theorem local_edge_start_relative_to_forward_anchor
    {h : ℕ} [NeZero h] (i s : Fin h)
    (hs : s = i + 1 ∨ s = i - 1 ∨
      s = (i + 1) + 1 ∨ s = (i - 1) - 1 ∨
      s = ((i + 1) + 1) + 1 ∨ s = ((i - 1) - 1) - 1)
    (hs_ne_left : s ≠ i + 1) (hleft_ne_right : s + 1 ≠ i) :
    s = (i + 1) + 1 ∨ s = ((i + 1) + 1) + 1 ∨
      i = (s + 1) + 1 ∨ i = ((s + 1) + 1) + 1 := by
  rcases hs with hp1 | hm1 | hp2 | hm2 | hp3 | hm3
  · exact False.elim (hs_ne_left hp1)
  · exact False.elim (hleft_ne_right (by rw [hm1]; abel))
  · exact Or.inl hp2
  · exact Or.inr (Or.inr (Or.inl (by rw [hm2]; abel)))
  · exact Or.inr (Or.inl hp3)
  · exact Or.inr (Or.inr (Or.inr (by rw [hm3]; abel)))

/-- The analogous index classification when the anchor source is the left
endpoint of its shared-five edge, so the anchor edge is `[i-1,i]`.  The extra
locality statement for the foreign left endpoint handles cyclic wrap-around
without any lower bound on the hull-cardinality beyond the existing one. -/
theorem local_edge_start_relative_to_backward_anchor
    {h : ℕ} [NeZero h] (i s : Fin h)
    (hs : s = i + 1 ∨ s = i - 1 ∨
      s = (i + 1) + 1 ∨ s = (i - 1) - 1 ∨
      s = ((i + 1) + 1) + 1 ∨ s = ((i - 1) - 1) - 1)
    (hleft : s + 1 = i + 1 ∨ s + 1 = i - 1 ∨
      s + 1 = (i + 1) + 1 ∨ s + 1 = (i - 1) - 1 ∨
      s + 1 = ((i + 1) + 1) + 1 ∨ s + 1 = ((i - 1) - 1) - 1)
    (hs_ne_right : s ≠ i - 1) (hs_ne_left : s ≠ i)
    (hleft_ne_right : s + 1 ≠ i - 1) :
    s = ((i - 1) + 1) + 1 ∨
      s = (((i - 1) + 1) + 1) + 1 ∨
      i - 1 = (s + 1) + 1 ∨
      i - 1 = ((s + 1) + 1) + 1 := by
  rcases hs with hp1 | hm1 | hp2 | hm2 | hp3 | hm3
  · exact Or.inl (by rw [hp1]; abel)
  · exact False.elim (hs_ne_right hm1)
  · exact Or.inr (Or.inl (by rw [hp2]; abel))
  · exact False.elim (hleft_ne_right (by rw [hm2]; abel))
  · rcases hleft with hlp1 | hlm1 | hlp2 | hlm2 | hlp3 | hlm3
    · exfalso
      apply hs_ne_left
      apply add_right_cancel (b := 1)
      simpa only [hp3] using hlp1
    · exact False.elim (hleft_ne_right hlm1)
    · left
      apply add_right_cancel (b := 1)
      calc
        s + 1 = (i + 1) + 1 := hlp2
        _ = (((i - 1) + 1) + 1) + 1 := by abel
    · exact Or.inr (Or.inr (Or.inl (by
        calc
          i - 1 = ((i - 1) - 1) + 1 := by abel
          _ = (s + 1) + 1 := by rw [hlm2])))
    · right; left
      apply add_right_cancel (b := 1)
      calc
        s + 1 = ((i + 1) + 1) + 1 := hlp3
        _ = ((((i - 1) + 1) + 1) + 1) + 1 := by abel
    · exact Or.inr (Or.inr (Or.inr (by
        calc
          i - 1 = (((((i - 1) - 1) - 1) + 1) + 1) := by abel
          _ = ((s + 1) + 1) + 1 := by rw [hlm3])))
  · exact Or.inr (Or.inr (Or.inl (by rw [hm3]; abel)))

/-- The residual same-center branch of a supporting-family overload produces
two genuinely different shared-five centers which are nearest neighbors, but
whose diameter endpoint pairs are disjoint.  The second pair contains exactly
the two non-anchor active sources.  This is the bookkeeping-to-geometry bridge
needed by the two/three-edge separation lemmas above. -/
theorem supporting_overload_same_center_pair_gives_disjoint_sharedFive_centers
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    {i j k : Fin h} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hcenter : assignedDonorCenter p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) =
      assignedDonorCenter p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k)) :
    ∃ (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
      (hkd : v k ∈ chargeDonors p (tightHullBadVertices p v))
      (availableI : Nonempty (SharedFiveCenterChoice p
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v i) hid).context.q))
      (availableJ : Nonempty (SharedFiveCenterChoice p
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q)),
      let fiveI := selectedSharedFiveCenter p
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v i) hid).context.q availableI
      let fiveJ := selectedSharedFiveCenter p
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q availableJ
      (v i = fiveI.left ∨ v i = fiveI.right) ∧
      (v j = fiveJ.left ∨ v j = fiveJ.right) ∧
      (v k = fiveJ.left ∨ v k = fiveJ.right) ∧
      ¬ (fiveI.left = fiveJ.left ∨ fiveI.left = fiveJ.right ∨
        fiveI.right = fiveJ.left ∨ fiveI.right = fiveJ.right) ∧
      (nearestGraph p).Adj
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v i) hid).context.q
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  let height := hullSupportingHeight p v
  have hiCopy := hi
  obtain ⟨hid, hipos, hinot, availableI, _hisix⟩ := hiCopy
  obtain ⟨hjd, hkd, _hjDirect, _hkDirect, hxcenter, hjCase4, _hkCase4⟩ :=
    supporting_overload_same_center_pair_forces_case4_central_receiver
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam hjk hj hk hcenter
  let aI := assignments (v i) hid
  let aJ := assignments (v j) hjd
  let aK := assignments (v k) hkd
  have hJK : aJ.context.q = aK.context.q := by
    rw [← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v j) hjd,
      ← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v k) hkd]
    exact hcenter
  have hjShared : SharedD p (v j) aJ.context.q := by
    simpa only [aJ, assignments] using hjCase4.2
  obtain ⟨w, hwD, hjw, hqw, hwhere⟩ :=
    tight_flat_sharedD_has_nearest_triangle
      p hp hn v hv hh hsupport hpos j aJ.context hjShared
  have availableJ : Nonempty (SharedFiveCenterChoice p aJ.context.q) := by
    rcases hwhere with hnext | hprev
    · subst w
      exact sharedFiveCenterChoice_nonempty_of_either_tight_flat_endpoint
        p hp hn v hv hh hsupport hpos j aJ.context.q hjw hqw
          aJ.context.central_adj.symm hjCase4.1
          (Or.inl aJ.context.outside_bad) hwD aJ.context.endpoint
    · subst w
      apply sharedFiveCenterChoice_nonempty_of_either_tight_flat_endpoint
        p hp hn v hv hh hsupport hpos (j - 1) aJ.context.q
      · simpa only [sub_add_cancel] using hjw.symm
      · simpa only [sub_add_cancel] using aJ.context.central_adj.symm
      · exact hqw
      · exact hjCase4.1
      · exact Or.inr (by simpa only [sub_add_cancel] using aJ.context.outside_bad)
      · simpa only [sub_add_cancel] using aJ.context.endpoint
      · exact hwD
  let fiveI := selectedSharedFiveCenter p aI.context.q availableI
  let fiveJ := selectedSharedFiveCenter p aJ.context.q availableJ
  have hiEnd : v i = fiveI.left ∨ v i = fiveI.right :=
    fiveI.diameter_neighbor_cases (v i) aI.context.endpoint aI.context.central_adj.symm
  have hjEnd : v j = fiveJ.left ∨ v j = fiveJ.right :=
    fiveJ.diameter_neighbor_cases (v j) aJ.context.endpoint aJ.context.central_adj.symm
  have hkD : v k ∈ diameterEndpoints p := (Finset.mem_filter.mp hkd).1
  have hqk : (nearestGraph p).Adj aJ.context.q (v k) := by
    rw [hJK]
    exact aK.context.central_adj.symm
  have hkEnd : v k = fiveJ.left ∨ v k = fiveJ.right :=
    fiveJ.diameter_neighbor_cases (v k) hkD hqk
  have hforeignRaw :=
    supporting_case4_anchor_center_ne_of_distinct_active
      p hp hn v hv hh hrange hsupport hpos x hij hi hj
  have hforeign : aJ.context.q ≠ aI.context.q := by
    intro heq
    apply hforeignRaw
    rw [assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v j) hjd,
      assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v i) hid]
    exact heq
  have hdisjoint : ¬ (fiveI.left = fiveJ.left ∨ fiveI.left = fiveJ.right ∨
      fiveI.right = fiveJ.left ∨ fiveI.right = fiveJ.right) := by
    intro hov
    have heq : aI.context.q = aJ.context.q :=
      sharedFive_centers_eq_of_endpoint_overlap p hp hn fiveI fiveJ hov
    exact hforeign heq.symm
  have hfiveIdeg : (nearestGraph p).degree aI.context.q = 5 := fiveI.center_degree
  have hIadjx : (nearestGraph p).Adj aI.context.q x :=
    aI.rule.indirect_degree_five_receiver_adj_center hfiveIdeg
      aI.context.endpoint aI.context.central_adj.symm
      (by simpa only [localPacketCharge, dite_eq_left hid, certifiedFamilyPackets,
        CertifiedDonorAssignment.packet, aI, assignments, height] using hipos) hinot
  have hcentersAdj : (nearestGraph p).Adj aI.context.q aJ.context.q := by
    rw [← hxcenter]
    exact hIadjx
  refine ⟨hid, hjd, hkd, ?_, ?_, ?_⟩
  · simpa only [aI, assignments] using availableI
  · simpa only [aJ, assignments] using availableJ
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [fiveI, aI, assignments] using hiEnd
    · simpa only [fiveJ, aJ, assignments] using hjEnd
    · simpa only [fiveJ, aJ, assignments] using hkEnd
    · simpa only [fiveI, fiveJ, aI, aJ, assignments] using hdisjoint
    · simpa only [aI, aJ, assignments] using hcentersAdj

end Erdos957

namespace Erdos957

/-- The residual same-center branch is impossible.  The branch produces two
disjoint supporting nearest hull edges whose shared-five centers would have
to be nearest neighbors.  Locality places the second edge exactly two or
three edges away.  Depending on which endpoint of the anchor edge is the
actual donor, use the good anchor or good foreign donor as the flat reference
and apply the corresponding forward/backward center-separation estimate. -/
theorem supporting_case4_same_center_pair_impossible
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    {i j k : Fin h} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjo : j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1)
    (hko : k = i + 1 ∨ k = i - 1 ∨
      k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
      k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1)
    (hcenter : assignedDonorCenter p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) =
      assignedDonorCenter p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k)) : False := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  obtain ⟨hid, hjd, hkd, availableI, availableJ,
      hiEnd, hjEnd, hkEnd, hdisjoint, hcentersAdj⟩ :=
    supporting_overload_same_center_pair_gives_disjoint_sharedFive_centers
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hcenter
  let aI := assignments (v i) hid
  let aJ := assignments (v j) hjd
  let fiveI := selectedSharedFiveCenter p aI.context.q availableI
  let fiveJ := selectedSharedFiveCenter p aJ.context.q availableJ
  have hiEnd' : v i = fiveI.left ∨ v i = fiveI.right := by
    simpa only [fiveI, aI, assignments] using hiEnd
  have hjEnd' : v j = fiveJ.left ∨ v j = fiveJ.right := by
    simpa only [fiveJ, aJ, assignments] using hjEnd
  have hkEnd' : v k = fiveJ.left ∨ v k = fiveJ.right := by
    simpa only [fiveJ, aJ, assignments] using hkEnd
  have hdisjoint' : ¬ (fiveI.left = fiveJ.left ∨ fiveI.left = fiveJ.right ∨
      fiveI.right = fiveJ.left ∨ fiveI.right = fiveJ.right) := by
    simpa only [fiveI, fiveJ, aI, aJ, assignments] using hdisjoint
  have hcentersAdj' : (nearestGraph p).Adj aI.context.q aJ.context.q := by
    simpa only [aI, aJ, assignments] using hcentersAdj
  obtain ⟨s, hsJK, hs1JK, hJright, hJleft⟩ :=
    fiveJ.oriented_edge_of_two_endpoints p hp v hv hh hrange hsupport
      j k hjk hjEnd' hkEnd'
  have hsLocal : s = i + 1 ∨ s = i - 1 ∨
      s = (i + 1) + 1 ∨ s = (i - 1) - 1 ∨
      s = ((i + 1) + 1) + 1 ∨ s = ((i - 1) - 1) - 1 := by
    rcases hsJK with hs | hs
    · rw [hs]
      exact hjo
    · rw [hs]
      exact hko
  have hs1Local : s + 1 = i + 1 ∨ s + 1 = i - 1 ∨
      s + 1 = (i + 1) + 1 ∨ s + 1 = (i - 1) - 1 ∨
      s + 1 = ((i + 1) + 1) + 1 ∨ s + 1 = ((i - 1) - 1) - 1 := by
    rcases hs1JK with hs | hs
    · rw [hs]
      exact hjo
    · rw [hs]
      exact hko
  have hgoodI : v i ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hid).2.1
  have hgoodS : v s ∉ tightHullBadVertices p v := by
    rcases hsJK with hs | hs
    · subst s
      exact (Finset.mem_filter.mp hjd).2.1
    · subst s
      exact (Finset.mem_filter.mp hkd).2.1
  rcases hiEnd' with hiLeft | hiRight
  · -- The anchor donor is the left endpoint, so the anchor edge starts at `i-1`.
    have hIleft : fiveI.left = v i := hiLeft.symm
    have hIright : fiveI.right = v (i - 1) := by
      have hrightHull : fiveI.right ∈ hullVertexIndices p :=
        diameterEndpoints_subset_hullVertexIndices p hp fiveI.right_diameter
      have hrightNe : fiveI.right ≠ v i := by
        intro heq
        exact fiveI.base.ne (hIleft.trans heq.symm)
      apply supporting_hull_chord_eq_predecessor p hp v hv hh hrange hsupport
        i fiveI.right hrightHull hrightNe
      intro z
      simpa only [hIleft] using fiveI.support z
    have hs_ne_right : s ≠ i - 1 := by
      intro hs
      apply hdisjoint'
      exact Or.inr (Or.inr (Or.inr (by rw [hIright, hJright, hs])))
    have hs_ne_left : s ≠ i := by
      intro hs
      apply hdisjoint'
      exact Or.inr (Or.inl (by rw [hIleft, hJright, hs]))
    have hs1_ne_right : s + 1 ≠ i - 1 := by
      intro hs
      apply hdisjoint'
      exact Or.inr (Or.inr (Or.inl (by rw [hIright, hJleft, hs])))
    have hwhere := local_edge_start_relative_to_backward_anchor
      i s hsLocal hs1Local hs_ne_right hs_ne_left hs1_ne_right
    rcases hwhere with hforward2 | hforward3 | hback2 | hback3
    · -- `s = (i-1)+2`: foreign good edge, anchor is two edges behind.
      have hsecondL : fiveI.left = v (s - 1) := by
        rw [hIleft, hforward2]
        congr 1
        abel
      have hsecondR : fiveI.right = v ((s - 1) - 1) := by
        rw [hIright, hforward2]
        congr 1
        abel
      exact (sharedFive_centers_backward_two_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm
    · -- `s = (i-1)+3`: foreign good edge, anchor is three edges behind.
      have hsecondL : fiveI.left = v ((s - 1) - 1) := by
        rw [hIleft, hforward3]
        congr 1
        abel
      have hsecondR : fiveI.right = v (((s - 1) - 1) - 1) := by
        rw [hIright, hforward3]
        congr 1
        abel
      exact (sharedFive_centers_backward_three_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm
    · -- `i-1 = s+2`: the good foreign edge is two edges before the anchor.
      have hsecondL : fiveI.left = v (((s + 1) + 1) + 1) := by
        rw [hIleft, ← hback2, sub_add_cancel]
      have hsecondR : fiveI.right = v ((s + 1) + 1) := by
        rw [hIright, hback2]
      exact (sharedFive_centers_forward_two_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm
    · -- `i-1 = s+3`: the good foreign edge is three edges before the anchor.
      have hsecondL : fiveI.left = v ((((s + 1) + 1) + 1) + 1) := by
        rw [hIleft, ← hback3, sub_add_cancel]
      have hsecondR : fiveI.right = v (((s + 1) + 1) + 1) := by
        rw [hIright, hback3]
      exact (sharedFive_centers_forward_three_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm
  · -- The anchor donor is the right endpoint, hence its edge starts at the good source `i`.
    have hIright : fiveI.right = v i := hiRight.symm
    have hIleft : fiveI.left = v (i + 1) :=
      fiveI.left_eq_cyclic_successor_of_right
        p hp v hv hh hrange hsupport i hIright
    have hs_ne_left : s ≠ i + 1 := by
      intro hs
      apply hdisjoint'
      exact Or.inr (Or.inl (by rw [hIleft, hJright, hs]))
    have hs1_ne_right : s + 1 ≠ i := by
      intro hs
      apply hdisjoint'
      exact Or.inr (Or.inr (Or.inl (by rw [hIright, hJleft, hs])))
    have hwhere := local_edge_start_relative_to_forward_anchor
      i s hsLocal hs_ne_left hs1_ne_right
    rcases hwhere with hforward2 | hforward3 | hback2 | hback3
    · have hsecondR : fiveJ.right = v ((i + 1) + 1) := by rw [hJright, hforward2]
      have hsecondL : fiveJ.left = v (((i + 1) + 1) + 1) := by
        rw [hJleft, hforward2]
      exact (sharedFive_centers_forward_two_edges_not_nearest
        p (by omega) hp v hv hh hpos i hgoodI fiveI fiveJ
        hIleft hIright hsecondL hsecondR) hcentersAdj'
    · have hsecondR : fiveJ.right = v (((i + 1) + 1) + 1) := by rw [hJright, hforward3]
      have hsecondL : fiveJ.left = v ((((i + 1) + 1) + 1) + 1) := by
        rw [hJleft, hforward3]
      exact (sharedFive_centers_forward_three_edges_not_nearest
        p (by omega) hp v hv hh hpos i hgoodI fiveI fiveJ
        hIleft hIright hsecondL hsecondR) hcentersAdj'
    · have hsecondR : fiveI.right = v ((s + 1) + 1) := by rw [hIright, hback2]
      have hsecondL : fiveI.left = v (((s + 1) + 1) + 1) := by
        rw [hIleft, ← hback2]
      exact (sharedFive_centers_forward_two_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm
    · have hsecondR : fiveI.right = v (((s + 1) + 1) + 1) := by rw [hIright, hback3]
      have hsecondL : fiveI.left = v ((((s + 1) + 1) + 1) + 1) := by
        rw [hIleft, ← hback3]
      exact (sharedFive_centers_forward_three_edges_not_nearest
        p (by omega) hp v hv hh hpos s hgoodS fiveJ fiveI
        hJleft hJright hsecondL hsecondR) hcentersAdj'.symm

end Erdos957

namespace Erdos957

/-- Consequently, every actual lossless Case-4 overload triple uses three
pairwise different retained centers.  The anchor-center inequalities were
already known; the new geometry above eliminates the last possible equality
between the two non-anchor centers. -/
theorem supporting_case4_actual_triple_centers_pairwise_distinct
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    {i j k : Fin h} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjo : j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1)
    (hko : k = i + 1 ∨ k = i - 1 ∨
      k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
      k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) :
    let center := fun t : Fin h =>
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v t)
    center i ≠ center j ∧ center i ≠ center k ∧ center j ≠ center k := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact (supporting_case4_anchor_center_ne_of_distinct_active
      p hp hn v hv hh hrange hsupport hpos x hij hi hj).symm
  · exact (supporting_case4_anchor_center_ne_of_distinct_active
      p hp hn v hv hh hrange hsupport hpos x hik hi hk).symm
  · intro hcenter
    exact supporting_case4_same_center_pair_impossible
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hjo hko hcenter

end Erdos957
