import SharedFiveReceiver

/-! A receiver rectangle obtained directly from a supported nearest-distance
triangle. It does not require a diameter, a scale estimate, or a hull span. -/

namespace Erdos957

/-- The shared equilateral vertex and all its other nearest neighbors lie
in one normalized rectangle. The two supporting endpoints are excluded
from the neighbor alternative, but the center itself is included. -/
theorem shared_triangle_neighbor_receiver_rectangle {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q a : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (ha : a = q ∨ ((nearestGraph p).Adj q a ∧ a ≠ u ∧ a ≠ w)) :
    -(1 / 2 : ℝ) ≤ (edgeCoordinate (p u) (p w) (p a)).re ∧
      (edgeCoordinate (p u) (p w) (p a)).re ≤ 3 / 2 ∧
      -2 ≤ (edgeCoordinate (p u) (p w) (p a)).im ∧
      (edgeCoordinate (p u) (p w) (p a)).im ≤ 0 := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have hne : p u ≠ p w := hp.ne huw.ne
  have huwdist := nearestGraph_adj_dist_eq p hmin huw
  have huqdist := nearestGraph_adj_dist_eq p hmin hqu.symm
  have hwqdist := nearestGraph_adj_dist_eq p hmin hqw.symm
  let M := edgeCoordinate (p u) (p w)
  have hq0 : ‖M (p q)‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_norm _ _ _ hne, huqdist, huwdist, div_self hr.ne']
  have hq1 : ‖M (p q) - 1‖ = 1 := by
    dsimp [M]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, hwqdist, huwdist, div_self hr.ne']
  have hbelow (k : Fin n) : (M (p k)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne (hsupport k)
  obtain ⟨h, hh, hhsq, hMq⟩ :=
    unit_triangle_below_real_axis (M (p q)) hq0 hq1 (hbelow q)
  change -(1 / 2 : ℝ) ≤ (M (p a)).re ∧ (M (p a)).re ≤ 3 / 2 ∧
    -2 ≤ (M (p a)).im ∧ (M (p a)).im ≤ 0
  rcases ha with rfl | ⟨hqa, hau, haw⟩
  · rw [hMq]
    norm_num
    constructor <;> nlinarith only [hh, hhsq]
  · have haqdist := nearestGraph_adj_dist_eq p hmin hqa.symm
    have haunit : ‖M (p a) - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1 := by
      rw [← hMq, ← dist_eq_norm]
      dsimp [M]
      rw [edgeCoordinate_dist _ _ _ _ hne, haqdist, huwdist, div_self hr.ne']
    have ha0 : 1 ≤ ‖M (p a)‖ := by
      dsimp [M]
      rw [edgeCoordinate_norm _ _ _ hne, huwdist]
      exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin hau.symm)
    have ha1 : 1 ≤ ‖M (p a) - 1‖ := by
      dsimp [M]
      rw [edgeCoordinate_sub_one_norm _ _ _ hne, huwdist]
      exact (one_le_div₀ hr).mpr (isMinPair_le_dist p hmin haw.symm)
    obtain ⟨hxlo, hxhi, hylo, _⟩ :=
      equilateral_other_neighbor_rectangle (M (p a)) h hh hhsq haunit ha0 ha1 (hbelow a)
    exact ⟨hxlo, hxhi, hylo, hbelow a⟩

end Erdos957
