import NormalizedTriangle
import DiameterGraph
import NearestGraph
import HullChordAdjacency
import DiameterAxisSeparation
import ShortDiameterChordAlgebra

namespace Erdos957

open scoped ComplexConjugate

set_option maxHeartbeats 1000000

private theorem complex_norm_sq_coordinates (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z

private theorem complex_dist_sq_coordinates (z t : ℂ) :
    (z.re - t.re) ^ 2 + (z.im - t.im) ^ 2 = dist z t ^ 2 := by
  simpa only [dist_eq_norm, Complex.sub_re, Complex.sub_im] using
    complex_norm_sq_coordinates (z - t)

/-- A normalized closest chord with sufficiently distant diameter partners
has all other separated points on the same side as either partner. -/
theorem normalized_short_diameter_chord_strict_same_side
    (J K z : ℂ) (D : ℝ)
    (hJ : ‖J‖ = D) (hK : ‖K - 1‖ = D)
    (hJK : dist J K ≤ D) (hJ1 : ‖J - 1‖ ≤ D) (hK0 : ‖K‖ ≤ D)
    (hD : 3 < D) (hz0 : 1 ≤ ‖z‖) (hz1 : 1 ≤ ‖z - 1‖)
    (hJz : dist J z ≤ D) (hKz : dist K z ≤ D) :
    0 < J.im * z.im := by
  have hJsq := complex_norm_sq_coordinates J
  have hKsq := complex_norm_sq_coordinates K
  have hJ1sq := complex_norm_sq_coordinates (J - 1)
  have hK1sq := complex_norm_sq_coordinates (K - 1)
  have hzsq := complex_norm_sq_coordinates z
  have hz1sq := complex_norm_sq_coordinates (z - 1)
  have hJzsq := complex_dist_sq_coordinates J z
  have hKzsq := complex_dist_sq_coordinates K z
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at hJ1sq hK1sq hz1sq
  rw [hJ] at hJsq
  rw [hK] at hK1sq
  have hJ1bound : ‖J - 1‖ ^ 2 ≤ D ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hJ1
  have hK0bound : ‖K‖ ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hK0
  have hJzbound : dist J z ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by linarith)).mpr hJz
  have hKzbound : dist K z ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by linarith)).mpr hKz
  have hz0sq : 1 ≤ ‖z‖ ^ 2 := by nlinarith only [hz0]
  have hz1sq' : 1 ≤ ‖z - 1‖ ^ 2 := by nlinarith only [hz1]
  have hA : 0 < J.re := by nlinarith only [hJsq, hJ1sq, hJ1bound]
  have hC : 0 < 1 - K.re := by nlinarith only [hKsq, hK1sq, hK0bound]
  have haxis := diameter_axes_inner_pos_of_three_mul_dist_lt
    (0 : ℂ) 1 J K D (by simpa using hJ) (by
      simpa only [dist_eq_norm, norm_sub_rev] using hK)
    hJK (by simpa using hD)
  simp only [sub_zero, Complex.inner, Complex.mul_re, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im, Complex.conj_re,
    Complex.conj_im] at haxis
  apply short_chord_point_strict_same_side 1 J.re J.im (1 - K.re) K.im z.re z.im
    (by norm_num) hA hC
  · nlinarith only [haxis]
  · nlinarith only [hzsq, hz0sq]
  · nlinarith only [hz1sq, hz1sq']
  · nlinarith only [hJsq, hzsq, hJzsq, hJzbound, hz0sq]
  · nlinarith only [hK1sq, hz1sq, hKzsq, hKzbound, hz1sq']

/-- A nearest-distance chord joining two diameter endpoints supports the
entire configuration once the diameter is greater than three chord lengths.
The orientation is chosen once and works for all configuration points. -/
theorem short_diameter_chord_support {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hmax : isMaxPair p ij)
    {u w : Fin n} (hu : u ∈ diameterEndpoints p)
    (hw : w ∈ diameterEndpoints p) (huw : (nearestGraph p).Adj u w)
    (hlong : 3 * dist (p u) (p w) < pairDist p ij) :
    (∀ l, 0 ≤ turn (p u) (p w) (p l)) ∨
      (∀ l, 0 ≤ turn (p w) (p u) (p l)) := by
  obtain ⟨j, huj⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  obtain ⟨k, hwk⟩ := (mem_diameterEndpoints_iff_exists_adj p w).mp hw
  have huwne : u ≠ w := (nearestGraph p).ne_of_adj huw
  have hne : p u ≠ p w := hp.ne huwne
  have hr : 0 < dist (p u) (p w) := dist_pos.mpr hne
  have hminall (a b : Fin n) (hab : a ≠ b) :
      dist (p u) (p w) ≤ dist (p a) (p b) := by
    rcases (nearestGraph_adj_iff p u w).mp huw with hmin | hmin
    · exact isMinPair_le_dist p hmin hab
    · simpa only [pairDist, dist_comm (p w) (p u)] using isMinPair_le_dist p hmin hab
  have hujD : dist (p u) (p j) = pairDist p ij :=
    (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp huj
  have hwkD : dist (p w) (p k) = pairDist p ij :=
    (diameterGraph_adj_iff_dist_eq p hp hmax w k).mp hwk
  let M : Fin n → ℂ := fun l => edgeCoordinate (p u) (p w) (p l)
  let D := pairDist p ij / dist (p u) (p w)
  have hD : 3 < D := (lt_div_iff₀ hr).mpr hlong
  have hJ : ‖M j‖ = D := by
    dsimp [M, D]
    rw [edgeCoordinate_norm _ _ _ hne, hujD]
  have hK : ‖M k - 1‖ = D := by
    dsimp [M, D]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne, hwkD]
  have hmetric (a b : Fin n) : dist (M a) (M b) ≤ D := by
    dsimp [M, D]
    rw [edgeCoordinate_dist _ _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMaxPair_dist_le p hmax a b) hr.le
  have hJ1 : ‖M j - 1‖ ≤ D := by
    dsimp [M, D]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMaxPair_dist_le p hmax w j) hr.le
  have hK0 : ‖M k‖ ≤ D := by
    dsimp [M, D]
    rw [edgeCoordinate_norm _ _ _ hne]
    exact div_le_div_of_nonneg_right (isMaxPair_dist_le p hmax u k) hr.le
  have hpositive (l : Fin n) (hlu : l ≠ u) (hlw : l ≠ w) :
      0 < (M j).im * (M l).im := by
    apply normalized_short_diameter_chord_strict_same_side
      (M j) (M k) (M l) D hJ hK (hmetric j k) hJ1 hK0 hD
    · dsimp [M]
      rw [edgeCoordinate_norm _ _ _ hne]
      exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hminall u l hlu.symm)
    · dsimp [M]
      rw [edgeCoordinate_sub_one_norm _ _ _ hne]
      exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hminall w l hlw.symm)
    · exact hmetric j l
    · exact hmetric k l
  have hju : j ≠ u := ((diameterGraph p).ne_of_adj huj).symm
  have hjw : j ≠ w := by
    intro heq
    rw [heq] at hujD
    nlinarith only [hlong, hujD, hr]
  have hJne : (M j).im ≠ 0 := by
    have hpos := hpositive j hju hjw
    intro heq
    simp only [heq, zero_mul, lt_self_iff_false] at hpos
  have hproduct (l : Fin n) : 0 ≤ (M j).im * (M l).im := by
    by_cases hlu : l = u
    · subst l
      simp [M, edgeCoordinate_self]
    by_cases hlw : l = w
    · subst l
      simp [M, edgeCoordinate_axis _ _ hne]
    exact (hpositive l hlu hlw).le
  rcases lt_or_gt_of_ne hJne with hnegative | hpositiveJ
  · right
    intro l
    have hlim : (M l).im ≤ 0 := by
      by_contra h
      have ht := mul_neg_of_neg_of_pos hnegative (lt_of_not_ge h)
      exact (not_lt_of_ge (hproduct l)) ht
    have hturn : turn (p u) (p w) (p l) ≤ 0 := by
      rw [← edgeCoordinate_im_mul_dist_sq _ _ _ hne]
      exact mul_nonpos_of_nonpos_of_nonneg hlim (sq_nonneg _)
    rw [turn_reverse]
    linarith
  · left
    intro l
    have hlim : 0 ≤ (M l).im := nonneg_of_mul_nonneg_right (hproduct l) hpositiveJ
    rw [← edgeCoordinate_im_mul_dist_sq _ _ _ hne]
    exact mul_nonneg hlim (sq_nonneg _)

end Erdos957
