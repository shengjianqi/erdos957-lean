import SharedFiveSixExtensionExclusion

/-! Preserve the public scalar bridge interfaces developed locally before
integrating the Case-4 candidate snapshot. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Every retained shared-five center is the lower equilateral vertex in its
selected diameter-edge frame. The height can be any positive root of 3/4,
so it can later be identified with the shared-six packet height. -/
theorem SharedFiveCenterChoice.center_coordinate_at_height {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q : Fin n} (five : SharedFiveCenterChoice p q)
    (h : ℝ) (hh : 0 < h) (hsq : h ^ 2 = 3 / 4) :
    edgeCoordinate (p five.left) (p five.right) (p q) =
      (1 / 2 : ℂ) - (h : ℂ) * Complex.I := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hne : p five.left ≠ p five.right := hp.ne five.base.ne
  have hbase : dist (p five.left) (p five.right) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin five.base
  have hleft : ‖edgeCoordinate (p five.left) (p five.right) (p q)‖ = 1 := by
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p hmin five.center_left.symm, hbase,
      div_self hδ.ne']
  have hright : ‖edgeCoordinate (p five.left) (p five.right) (p q) - 1‖ = 1 := by
    rw [edgeCoordinate_sub_one_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p hmin five.center_right.symm, hbase,
      div_self hδ.ne']
  have hbelow : (edgeCoordinate (p five.left) (p five.right) (p q)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne (five.support q)
  obtain ⟨h', hh', hsq', hcoord⟩ :=
    unit_triangle_below_real_axis _ hleft hright hbelow
  have heq : h' = h := by nlinarith
  simpa only [heq] using hcoord

/-- Coordinate change between two nondegenerate oriented edges. -/
theorem edgeCoordinate_affine_change (u w a b x : Point)
    (huw : u ≠ w) (hab : a ≠ b) :
    edgeCoordinate u w x = edgeCoordinate u w a +
      edgeCoordinate a b x * (edgeCoordinate u w b - edgeCoordinate u w a) := by
  have hden₁ : pointToComplex (w - u) ≠ 0 := by
    intro hz
    exact huw (sub_eq_zero.mp
      (pointToComplex.injective (by simpa using hz))).symm
  have hden₂ : pointToComplex (b - a) ≠ 0 := by
    intro hz
    exact hab (sub_eq_zero.mp
      (pointToComplex.injective (by simpa using hz))).symm
  have hxa : pointToComplex (x - a) =
      pointToComplex (x - u) - pointToComplex (a - u) := by
    rw [← map_sub]
    congr 1
    abel
  have hba : pointToComplex (b - a) =
      pointToComplex (b - u) - pointToComplex (a - u) := by
    rw [← map_sub]
    congr 1
    abel
  simp only [edgeCoordinate, hxa, hba]
  have hne : pointToComplex (b - u) - pointToComplex (a - u) ≠ 0 := by
    simpa only [← hba] using hden₂
  field_simp [hden₁, hne]
  ring

/-- Express the actual shared-five center in any shared-six base frame. -/
theorem SharedFiveCenterChoice.center_in_sharedSix_frame {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (five : SharedFiveCenterChoice p qfive) :
    edgeCoordinate (p u) (p w) (p qfive) =
      edgeCoordinate (p u) (p w) (p five.left) +
        ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) *
          (edgeCoordinate (p u) (p w) (p five.right) -
            edgeCoordinate (p u) (p w) (p five.left)) := by
  rw [edgeCoordinate_affine_change _ _ _ _ _
    (hp.ne choice.base.ne) (hp.ne five.base.ne)]
  rw [five.center_coordinate_at_height p hn hp choice.height
    choice.height_pos choice.height_sq]

/-- The actual supporting edge supplies the scalar support inequality for
the other shared-six source, expressed in the shared-six normalized frame. -/
theorem SharedFiveCenterChoice.support_inequality_in_sharedSix_frame {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (five : SharedFiveCenterChoice p qfive) :
    (conj (edgeCoordinate (p u) (p w) (p five.right) -
        edgeCoordinate (p u) (p w) (p five.left)) *
      (1 - edgeCoordinate (p u) (p w) (p five.left))).im ≤ 0 := by
  have hne : p u ≠ p w := hp.ne choice.base.ne
  have hturn : turn (p five.left) (p five.right) (p w) ≤ 0 := by
    rw [turn_reverse]
    linarith [five.support w]
  have heq := edgeCoordinate_complexTurn_mul_dist_sq
    (p u) (p w) (p five.left) (p five.right) (p w) hne
  rw [edgeCoordinate_axis _ _ hne] at heq
  change (conj (edgeCoordinate (p u) (p w) (p five.right) -
      edgeCoordinate (p u) (p w) (p five.left)) *
    (1 - edgeCoordinate (p u) (p w) (p five.left))).im *
    dist (p u) (p w) ^ 2 = turn (p five.left) (p five.right) (p w) at heq
  have hpositive : 0 < dist (p u) (p w) ^ 2 :=
    sq_pos_of_pos (dist_pos.mpr hne)
  nlinarith only [heq, hturn, hpositive]


/-- Four scalar premises for the actual forward mixed configuration: the
shared-five base vector is unit and supported, the center meets t₂, and it
avoids the shared-six outer site. -/
theorem SharedSixPacketChoice.second_extension_sharedFive_scalar_distances {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hbottom : five.selection.bottom = choice.packet.right) :
    let a := edgeCoordinate (p u) (p w) (p five.left)
    let b := edgeCoordinate (p u) (p w) (p five.right) - a
    ‖b‖ = 1 ∧
      (conj b * (1 - a)).im ≤ 0 ∧
      ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
        ((2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)‖ = 1 ∧
      1 ≤ ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
        ((3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ := by
  dsimp
  have hne : p u ≠ p w := hp.ne choice.base.ne
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hbase : dist (p u) (p w) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin choice.base
  have hfive : dist (p five.left) (p five.right) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin five.base
  have hnorm : ‖edgeCoordinate (p u) (p w) (p five.right) -
      edgeCoordinate (p u) (p w) (p five.left)‖ = 1 := by
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hne,
      dist_comm (p five.right) (p five.left), hfive, hbase,
      div_self hδ.ne']
  have hcenter := five.center_in_sharedSix_frame p hn hp choice
  have hsupport := five.support_inequality_in_sharedSix_frame p hp choice
  obtain ⟨hqa, hqb⟩ := choice.second_extension_sharedFive_center_distances
    p hn hp hw hqw hdegree hnot_lower five hbottom
  rw [hcenter] at hqa hqb
  exact ⟨hnorm, hsupport, hqa, hqb⟩



end Erdos957

