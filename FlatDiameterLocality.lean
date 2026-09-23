import CircleTriangle
import Mathlib.Tactic.Linarith

/-! Algebraic tools for uniform locality of diameter endpoints near a flat
hull chain. Applying them to the actual cyclic hull is a separate obligation. -/

namespace Erdos957

private theorem complex_square_coordinates (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z

/-- A nearby diameter axis points above the support direction if the first
axis is in a narrow inward cone. The metric gap is strictly less than 6D/5. -/
theorem close_diameter_axis_im_pos (A B : ℂ) (D : ℝ)
    (hD : 0 < D) (hA : ‖A‖ = D) (hB : ‖B‖ = D)
    (hgap : ‖A - B‖ < 6 * D / 5)
    (hAx : 0 ≤ A.re) (hcone : 30 * A.re ≤ A.im) :
    0 < B.im := by
  have hAy : A.im ≤ D := by simpa only [hA] using Complex.im_le_norm A
  have hBx : B.re ≤ D := by simpa only [hB] using Complex.re_le_norm B
  have hAypos : 0 ≤ A.im := by linarith
  have hAxbound : A.re ≤ D / 30 := by linarith
  have hAsq := complex_square_coordinates A
  have hBsq := complex_square_coordinates B
  have hABsq := complex_square_coordinates (A - B)
  simp only [Complex.sub_re, Complex.sub_im, hA, hB] at *
  have hgapSq : ‖A - B‖ ^ 2 < (6 * D / 5) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hgap
  have hdot : 7 * D ^ 2 / 25 < A.re * B.re + A.im * B.im := by
    nlinarith only [hAsq, hBsq, hABsq, hgapSq]
  by_contra hnot
  have hBy : B.im ≤ 0 := le_of_not_gt hnot
  have hyprod := mul_nonpos_of_nonneg_of_nonpos hAypos hBy
  have hxprod := mul_nonneg hAx (sub_nonneg.mpr hBx)
  have hxD := mul_nonneg hD.le (sub_nonneg.mpr hAxbound)
  nlinarith only [hdot, hyprod, hxprod, hxD, sq_pos_of_pos hD]

/-- A point above a supported increasing edge and horizontally bracketed by
its endpoints cannot have a strictly inward upward diameter functional unless
it is an endpoint. This also covers equality at either horizontal endpoint. -/
theorem supported_point_eq_edge_endpoint (a b w B : ℂ)
    (hab : a.re < b.re) (haw : a.re ≤ w.re) (hwb : w.re ≤ b.re)
    (hside : 0 ≤ complexTurn a b w) (hBy : 0 < B.im)
    (ha : a ≠ w → 0 < B.re * (a.re - w.re) + B.im * (a.im - w.im))
    (hb : b ≠ w → 0 < B.re * (b.re - w.re) + B.im * (b.im - w.im)) :
    w = a ∨ w = b := by
  by_contra hnot
  have hwa : w ≠ a := fun h => hnot (Or.inl h)
  have hwbne : w ≠ b := fun h => hnot (Or.inr h)
  have hapos := ha hwa.symm
  have hbpos := hb hwbne.symm
  have hleft : 0 ≤ b.re - w.re := sub_nonneg.mpr hwb
  have hright : 0 ≤ w.re - a.re := sub_nonneg.mpr haw
  have hsum : 0 <
      (b.re - w.re) * (B.re * (a.re - w.re) + B.im * (a.im - w.im)) +
      (w.re - a.re) * (B.re * (b.re - w.re) + B.im * (b.im - w.im)) := by
    rcases lt_or_eq_of_le hwb with hlt | heq
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hapos)
        (mul_nonneg hright hbpos.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hleft hapos.le)
        (mul_pos (by linarith) hbpos)
  have hid :
      (b.re - w.re) * (B.re * (a.re - w.re) + B.im * (a.im - w.im)) +
      (w.re - a.re) * (B.re * (b.re - w.re) + B.im * (b.im - w.im)) =
      -B.im * complexTurn a b w := by
    simp only [complexTurn, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [hid] at hsum
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hBy.le) hside
  exact (not_lt_of_ge hnonpos) hsum

/-- An arbitrary finite increasing chain brackets each horizontal coordinate
between its first and last vertices in one of its edges. -/
theorem increasing_chain_brackets (x : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hstep : ∀ i, i < m → x i < x (i + 1))
    (r : ℝ) (hlo : x 0 ≤ r) (hhi : r ≤ x m) :
    ∃ i, i < m ∧ x i ≤ r ∧ r ≤ x (i + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hmzero : m = 0
    · subst m
      exact ⟨0, by omega, hlo, hhi⟩
    by_cases hmid : r ≤ x m
    · obtain ⟨i, hi, hil, hir⟩ := ih (by omega)
        (fun j hj => hstep j (by omega)) hmid
      exact ⟨i, by omega, hil, hir⟩
    · exact ⟨m, by omega, (le_of_not_ge hmid), hhi⟩

/-- A single inward functional excludes every point outside the finite local
chain, without considering its index in a larger polygon. -/
theorem supported_point_mem_increasing_chain (c : ℕ → ℂ) (m : ℕ)
    (hm : 0 < m) (w B : ℂ)
    (hstep : ∀ i, i < m → (c i).re < (c (i + 1)).re)
    (hlo : (c 0).re ≤ w.re) (hhi : w.re ≤ (c m).re)
    (hside : ∀ i, i < m → 0 ≤ complexTurn (c i) (c (i + 1)) w)
    (hBy : 0 < B.im)
    (hstrict : ∀ i, i ≤ m → c i ≠ w →
      0 < B.re * ((c i).re - w.re) + B.im * ((c i).im - w.im)) :
    ∃ i, i ≤ m ∧ w = c i := by
  obtain ⟨i, hi, hil, hir⟩ := increasing_chain_brackets
    (fun j => (c j).re) m hm hstep w.re hlo hhi
  rcases supported_point_eq_edge_endpoint (c i) (c (i + 1)) w B
      (hstep i hi) hil hir (hside i hi) hBy
      (hstrict i (by omega)) (hstrict (i + 1) (by omega)) with heq | heq
  · exact ⟨i, by omega, heq⟩
  · exact ⟨i + 1, by omega, heq⟩

end Erdos957
