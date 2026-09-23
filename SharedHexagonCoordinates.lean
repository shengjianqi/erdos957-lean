import NormalizedEdgeGeometry
import NearestBound
import Mathlib.Tactic.Abel

/-! Reusable exact coordinates along a hexagonal extension of a shared edge. -/

namespace Erdos957

/-- Normalize the nearest edge `u-w` to `0-1`, with the shared neighbor `v`
below its actual supporting line. The first two rhombus identities then fix
the exact coordinates of `b` and `t`. -/
theorem shared_hexagon_base_coordinates {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v b t : Fin n}
    (hvu : (nearestGraph p).Adj v u)
    (hvw : (nearestGraph p).Adj v w)
    (huw : (nearestGraph p).Adj u w)
    (hsupport : ∀ k : Fin n, 0 ≤ turn (p w) (p u) (p k))
    (hbsum : p u + p b = p v + p w)
    (htsum : p w + p t = p v + p b) :
    ∃ h : ℝ, 0 < h ∧ h ^ 2 = 3 / 4 ∧
      edgeCoordinate (p u) (p w) (p v) =
        (1 / 2 : ℂ) - (h : ℂ) * Complex.I ∧
      edgeCoordinate (p u) (p w) (p b) =
        (3 / 2 : ℂ) - (h : ℂ) * Complex.I ∧
      edgeCoordinate (p u) (p w) (p t) =
        (1 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I := by
  have huwne : p u ≠ p w := hp.ne huw.ne
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have huwdist : dist (p u) (p w) = r := nearestGraph_adj_dist_eq p hmin huw
  have huvdist : dist (p u) (p v) = r := nearestGraph_adj_dist_eq p hmin hvu.symm
  have hwvdist : dist (p w) (p v) = r := nearestGraph_adj_dist_eq p hmin hvw.symm
  let M := edgeCoordinate (p u) (p w)
  have hMu : M (p u) = 0 := edgeCoordinate_self (p u) (p w)
  have hMw : M (p w) = 1 := edgeCoordinate_axis (p u) (p w) huwne
  have hMvunit : ‖M (p v)‖ = 1 := by
    rw [edgeCoordinate_norm (p u) (p w) (p v) huwne, huvdist, huwdist]
    exact div_self hr.ne'
  have hMvunit₁ : ‖M (p v) - 1‖ = 1 := by
    rw [edgeCoordinate_sub_one_norm (p u) (p w) (p v) huwne, hwvdist, huwdist]
    exact div_self hr.ne'
  have hMvbelow : (M (p v)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support (p u) (p w) (p v) huwne (hsupport v)
  obtain ⟨h, hh, hhsq, hMv⟩ := unit_triangle_below_real_axis (M (p v))
    hMvunit hMvunit₁ hMvbelow
  have hMb : M (p b) = (3 / 2 : ℂ) - (h : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p u) (p b) (p v) (p w) hbsum
    change M (p u) + M (p b) = M (p v) + M (p w) at hs
    rw [hMu, hMw, hMv] at hs
    simpa only [zero_add] using hs.trans (by ring)
  have hMt : M (p t) = (1 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p w) (p t) (p v) (p b) htsum
    change M (p w) + M (p t) = M (p v) + M (p b) at hs
    calc
      M (p t) = (M (p w) + M (p t)) - M (p w) := by ring
      _ = (M (p v) + M (p b)) - M (p w) := by rw [hs]
      _ = _ := by rw [hMv, hMb, hMw]; push_cast; ring
  exact ⟨h, hh, hhsq, hMv, hMb, hMt⟩

/-- One more rhombus identity fixes the next extension point at `2-2hi`. -/
theorem shared_hexagon_t2_coordinate {n : ℕ} (p : Fin n → Point)
    {u w v b t t2 : Fin n} (h : ℝ)
    (hMv : edgeCoordinate (p u) (p w) (p v) =
      (1 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (hMb : edgeCoordinate (p u) (p w) (p b) =
      (3 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (hMt : edgeCoordinate (p u) (p w) (p t) =
      (1 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I)
    (ht2sum : p v + p t2 = p t + p b) :
    edgeCoordinate (p u) (p w) (p t2) =
      (2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I := by
  let M := edgeCoordinate (p u) (p w)
  change M (p v) = _ at hMv
  change M (p b) = _ at hMb
  change M (p t) = _ at hMt
  have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
    (p v) (p t2) (p t) (p b) ht2sum
  change M (p v) + M (p t2) = M (p t) + M (p b) at hs
  calc
    M (p t2) = (M (p v) + M (p t2)) - M (p v) := by ring
    _ = (M (p t) + M (p b)) - M (p v) := by rw [hs]
    _ = _ := by rw [hMt, hMb, hMv]; push_cast; ring

/-- The final affine identity fixes the shared receiver at `5/2-hi`. -/
theorem shared_hexagon_d_coordinate {n : ℕ} (p : Fin n → Point)
    {u w v b d : Fin n} (h : ℝ)
    (hMv : edgeCoordinate (p u) (p w) (p v) =
      (1 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (hMb : edgeCoordinate (p u) (p w) (p b) =
      (3 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (hdeq : p d = 2 • p b - p v) :
    edgeCoordinate (p u) (p w) (p d) =
      (5 / 2 : ℂ) - (h : ℂ) * Complex.I := by
  let M := edgeCoordinate (p u) (p w)
  change M (p v) = _ at hMv
  change M (p b) = _ at hMb
  have hdadd : p v + p d = p b + p b := by
    rw [hdeq, two_smul]
    abel
  have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
    (p v) (p d) (p b) (p b) hdadd
  change M (p v) + M (p d) = M (p b) + M (p b) at hs
  calc
    M (p d) = (M (p v) + M (p d)) - M (p v) := by ring
    _ = (M (p b) + M (p b)) - M (p v) := by rw [hs]
    _ = _ := by rw [hMb, hMv]; ring

end Erdos957
