import ShallowCase4ForeignCenterGeometry

/-! Stronger three-edge separation for the final shallow side-capacity proof.
Two degree-five shared-five centers supported on hull edges three steps apart
cannot have a common nearest-neighbor receiver: their center separation is
strictly larger than two minimum distances. -/

namespace Erdos957

theorem sharedFive_centers_forward_three_edges_no_common_receiver
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' x : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v (((((i + 1) + 1) + 1) + 1)))
    (hsecondR : second.right = v (((i + 1) + 1) + 1))
    (hqx : (nearestGraph p).Adj q x)
    (hq'x : (nearestGraph p).Adj q' x) : False := by
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
  have hreal : 2 < (M (p q') - M (p q)).re := by
    rw [hq', hq]
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_upper H e₃.im hHpos.le hHlt.le he₃im
    nlinarith
  have hcoord : 2 < dist (M (p q)) (M (p q')) := by
    rw [dist_comm, dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  have hfar : 2 * pairDist p ab < dist (p q) (p q') := by
    rw [edgeCoordinate_dist _ _ _ _ hAB,
      nearestGraph_adj_dist_eq p hmin hbase₀] at hcoord
    exact (lt_div_iff₀ hδ).mp hcoord
  have ht := dist_triangle (p q) (p x) (p q')
  rw [nearestGraph_adj_dist_eq p hmin hqx,
    nearestGraph_adj_dist_eq p hmin hq'x.symm] at ht
  linarith


theorem sharedFive_centers_backward_three_edges_no_common_receiver
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' x : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v ((i - 1) - 1))
    (hsecondR : second.right = v (((i - 1) - 1) - 1))
    (hqx : (nearestGraph p).Adj q x)
    (hq'x : (nearestGraph p).Adj q' x) : False := by
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
  have hreal : 2 < (M (p q) - M (p q')).re := by
    rw [hq, hq']
    norm_num [Complex.mul_re, Complex.mul_im]
    have hprod := unit_height_mul_small_im_lower H e₃.im hHpos.le hHlt.le he₃im
    nlinarith
  have hcoord : 2 < dist (M (p q)) (M (p q')) := by
    rw [dist_eq_norm]
    exact lt_of_lt_of_le hreal (Complex.re_le_norm _)
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  have hfar : 2 * pairDist p ab < dist (p q) (p q') := by
    rw [edgeCoordinate_dist _ _ _ _ hAB,
      nearestGraph_adj_dist_eq p hmin hbase₀] at hcoord
    exact (lt_div_iff₀ hδ).mp hcoord
  have ht := dist_triangle (p q) (p x) (p q')
  rw [nearestGraph_adj_dist_eq p hmin hqx,
    nearestGraph_adj_dist_eq p hmin hq'x.symm] at ht
  linarith


/-- Three-step shared-five centers cannot both be active at the same receiver,
even allowing one of the two packets to charge its own center directly.  The
only degenerate possibility `x = q = q'` is excluded explicitly by `hne`. -/
theorem sharedFive_centers_forward_three_edges_no_common_active_receiver
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' x : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v (((((i + 1) + 1) + 1) + 1)))
    (hsecondR : second.right = v (((i + 1) + 1) + 1))
    (hne : q ≠ q')
    (hqx : x = q ∨ (nearestGraph p).Adj q x)
    (hq'x : x = q' ∨ (nearestGraph p).Adj q' x) : False := by
  rcases hqx with hxc | hqx <;> rcases hq'x with hxc' | hq'x
  · exact hne (hxc.symm.trans hxc')
  · subst x
    exact (sharedFive_centers_forward_three_edges_not_nearest
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR) hq'x.symm
  · subst x
    exact (sharedFive_centers_forward_three_edges_not_nearest
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR) hqx
  · exact sharedFive_centers_forward_three_edges_no_common_receiver
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR hqx hq'x

/-- Backward analogue of the active-receiver three-step exclusion. -/
theorem sharedFive_centers_backward_three_edges_no_common_active_receiver
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    {q q' x : Fin n}
    (first : SharedFiveCenterChoice p q)
    (second : SharedFiveCenterChoice p q')
    (hfirstL : first.left = v (i + 1))
    (hfirstR : first.right = v i)
    (hsecondL : second.left = v ((i - 1) - 1))
    (hsecondR : second.right = v (((i - 1) - 1) - 1))
    (hne : q ≠ q')
    (hqx : x = q ∨ (nearestGraph p).Adj q x)
    (hq'x : x = q' ∨ (nearestGraph p).Adj q' x) : False := by
  rcases hqx with hxc | hqx <;> rcases hq'x with hxc' | hq'x
  · exact hne (hxc.symm.trans hxc')
  · subst x
    exact (sharedFive_centers_backward_three_edges_not_nearest
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR) hq'x.symm
  · subst x
    exact (sharedFive_centers_backward_three_edges_not_nearest
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR) hqx
  · exact sharedFive_centers_backward_three_edges_no_common_receiver
      p hn hp v hv hh hpos i hgood first second
      hfirstL hfirstR hsecondL hsecondR hqx hq'x

end Erdos957
