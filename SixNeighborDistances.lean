import SixNeighborStructure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The three possible chords among distinct neighbors of a degree-six vertex. -/

namespace Erdos957

open scoped ComplexConjugate

private theorem cos_of_two_step_gap {t : ℝ}
    (ht : |t| = 2 * Real.pi / 3 ∨ |t| = 4 * Real.pi / 3) :
    Real.cos t = -(1 / 2 : ℝ) := by
  rw [← Real.cos_abs]
  rcases ht with ht | ht
  · have heq : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [ht, heq, Real.cos_pi_sub, Real.cos_pi_div_three]
  · have heq : 4 * Real.pi / 3 = 2 * Real.pi - (2 * Real.pi / 3) := by ring
    have htwo : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [ht, heq, Real.cos_two_pi_sub, htwo]

private theorem complex_re_mul_conj_eq_cos_gap (z w : ℂ) :
    (z * conj w).re = ‖z‖ * ‖w‖ * Real.cos (z.arg - w.arg) := by
  have hzre := Complex.norm_mul_cos_arg z
  have hwre := Complex.norm_mul_cos_arg w
  have hzim := Complex.norm_mul_sin_arg z
  have hwim := Complex.norm_mul_sin_arg w
  calc
    (z * conj w).re = z.re * w.re + z.im * w.im := by simp [Complex.mul_re]
    _ = ‖z‖ * ‖w‖ *
        (Real.cos z.arg * Real.cos w.arg + Real.sin z.arg * Real.sin w.arg) := by
      rw [← hzre, ← hwre, ← hzim, ← hwim]
      ring
    _ = ‖z‖ * ‖w‖ * Real.cos (z.arg - w.arg) := by rw [Real.cos_sub]

/-- A two-step chord in an equal-radius hexagon has squared length `3r²`.
The alternative gap covers the principal-argument wrap. -/
theorem dist_sq_eq_three_radius_sq_of_directionArg_two_step
    (x y z : Point) (r : ℝ)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hgap : |directionArg x y - directionArg x z| = 2 * Real.pi / 3 ∨
      |directionArg x y - directionArg x z| = 4 * Real.pi / 3) :
    dist y z ^ 2 = 3 * r ^ 2 := by
  let a : ℂ := pointToComplex (x - y)
  let b : ℂ := pointToComplex (x - z)
  have ha : ‖a‖ = r := by
    simpa only [a, pointToComplex.norm_map, dist_eq_norm, norm_sub_rev] using hxy
  have hb : ‖b‖ = r := by
    simpa only [b, pointToComplex.norm_map, dist_eq_norm, norm_sub_rev] using hxz
  have hcos : Real.cos (a.arg - b.arg) = -(1 / 2 : ℝ) :=
    cos_of_two_step_gap hgap
  have hmul := complex_re_mul_conj_eq_cos_gap a b
  have hnorm : ‖a - b‖ ^ 2 = 3 * r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hmul, ha, hb, hcos]
    ring
  have hvec : (x - y) - (x - z) = z - y := by abel
  calc
    dist y z ^ 2 = ‖z - y‖ ^ 2 := by simp [dist_eq_norm, norm_sub_rev]
    _ = ‖(x - y) - (x - z)‖ ^ 2 := by rw [hvec]
    _ = ‖a - b‖ ^ 2 := by
      change ‖(x - y) - (x - z)‖ ^ 2 =
        ‖pointToComplex (x - y) - pointToComplex (x - z)‖ ^ 2
      rw [← map_sub, pointToComplex.norm_map]
    _ = 3 * r ^ 2 := hnorm

/-- The two-step chord of the canonical six-neighbor ordering. -/
theorem degree_six_two_step_dist_sq {n : ℕ} (p : Fin n → Point)
    (q : Fin n)
    (v : Fin 6 → Fin n)
    (hradius : ∀ k, (nearestGraph p).Adj q (v k))
    (hargs : ∀ k, directionArg (p q) (p (v k)) =
      directionArg (p q) (p (v 0)) + (k : ℝ) * (Real.pi / 3))
    (k : Fin 6) (ij : Fin n × Fin n) (hmin : isMinPair p ij) :
    dist (p (v k)) (p (v (k + 2))) ^ 2 = 3 * pairDist p ij ^ 2 := by
  have hgap :
      |directionArg (p q) (p (v k)) -
        directionArg (p q) (p (v (k + 2)))| = 2 * Real.pi / 3 ∨
      |directionArg (p q) (p (v k)) -
        directionArg (p q) (p (v (k + 2)))| = 4 * Real.pi / 3 := by
    rw [hargs k, hargs (k + 2)]
    fin_cases k <;> norm_num
    · left
      rw [abs_of_pos (by positivity : 0 < Real.pi / 3)]
      ring
    · left
      rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
      ring
    · left
      rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
      ring
    · left
      rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
      ring
    · right
      rw [abs_of_pos (by positivity : 0 < Real.pi / 3)]
      ring
    · right
      rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]
      ring
  exact dist_sq_eq_three_radius_sq_of_directionArg_two_step
    (p q) (p (v k)) (p (v (k + 2))) (pairDist p ij)
    (nearestGraph_adj_dist_eq p hmin (hradius k))
    (nearestGraph_adj_dist_eq p hmin (hradius (k + 2))) hgap

/-- Opposite positions in a canonical six-neighbor ordering are antipodal. -/
theorem degree_six_three_step_antipodal {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (q : Fin n)
    (v : Fin 6 → Fin n)
    (hradius : ∀ k, (nearestGraph p).Adj q (v k))
    (hargs : ∀ k, directionArg (p q) (p (v k)) =
      directionArg (p q) (p (v 0)) + (k : ℝ) * (Real.pi / 3))
    (k : Fin 6) (ij : Fin n × Fin n) (hmin : isMinPair p ij) :
    p (v k) + p (v (k + 3)) = 2 • p q := by
  apply equal_radius_arg_gap_pi_antipodal
    (p q) (p (v k)) (p (v (k + 3)))
    (pairDist p ij) (pairDist_pos p hp hmin.1)
    (nearestGraph_adj_dist_eq p hmin (hradius k))
    (nearestGraph_adj_dist_eq p hmin (hradius (k + 3)))
  rw [hargs k, hargs (k + 3)]
  fin_cases k <;> norm_num
  all_goals
    first
    | rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]; ring
    | rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]; ring

/-- Every pair of distinct neighbors of a degree-six point is a one-step,
two-step, or antipodal chord of its forced regular hexagon. -/
theorem degree_six_neighbor_distance_classification {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q u w : Fin n} (hdegree : (nearestGraph p).degree q = 6)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w) (huw : u ≠ w)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij) :
    dist (p u) (p w) = pairDist p ij ∨
      dist (p u) (p w) ^ 2 = 3 * pairDist p ij ^ 2 ∨
      p u + p w = 2 • p q := by
  obtain ⟨v, _hvinj, hcover, hcycle, hargs⟩ :=
    nearestGraph_degree_six_regular p hn hp q hdegree
  obtain ⟨a, rfl⟩ := (hcover u).mp hqu
  obtain ⟨b, rfl⟩ := (hcover w).mp hqw
  have hradius (k : Fin 6) : (nearestGraph p).Adj q (v k) :=
    (hcover _).mpr ⟨k, rfl⟩
  have hab : a ≠ b := by
    intro heq
    exact huw (congrArg v heq)
  have hclass : b = a + 1 ∨ b = a + 5 ∨ b = a + 2 ∨
      b = a + 4 ∨ b = a + 3 := by
    fin_cases a <;> fin_cases b <;>
      first | exact False.elim (hab (by decide)) | decide
  rcases hclass with h1 | h5 | h2 | h4 | h3
  · subst b
    exact Or.inl (nearestGraph_adj_dist_eq p hmin (hcycle a))
  · have hwrap : (b + 1 : Fin 6) = a := by
      rw [h5]
      fin_cases a <;> decide
    have hdist := nearestGraph_adj_dist_eq p hmin (hcycle b)
    rw [hwrap] at hdist
    exact Or.inl (by simpa only [dist_comm] using hdist)
  · subst b
    exact Or.inr (Or.inl
      (degree_six_two_step_dist_sq p q v hradius hargs a ij hmin))
  · have hwrap : (b + 2 : Fin 6) = a := by
      rw [h4]
      fin_cases a <;> decide
    have hdist := degree_six_two_step_dist_sq p q v hradius hargs b ij hmin
    rw [hwrap] at hdist
    exact Or.inr (Or.inl (by simpa only [dist_comm] using hdist))
  · subst b
    exact Or.inr (Or.inr
      (degree_six_three_step_antipodal p hp q v hradius hargs a ij hmin))

/-- A non-antipodal chord of the six-neighbor hexagon is shorter than
`1.9` times the minimum distance. -/
theorem degree_six_nonantipodal_neighbor_dist_le {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q u w : Fin n} (hdegree : (nearestGraph p).degree q = 6)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w) (huw : u ≠ w)
    (hnot : p u + p w ≠ 2 • p q)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij) :
    dist (p u) (p w) ≤ (19 / 10 : ℝ) * pairDist p ij := by
  have hr : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  rcases degree_six_neighbor_distance_classification p hn hp hdegree
      hqu hqw huw ij hmin with hone | htwo | hopp
  · rw [hone]
    nlinarith
  · have hd : 0 ≤ dist (p u) (p w) := dist_nonneg
    nlinarith [sq_pos_of_pos hr]
  · exact False.elim (hnot hopp)

end Erdos957
