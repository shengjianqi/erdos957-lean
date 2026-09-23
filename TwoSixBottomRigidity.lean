import ShallowMixedDirectOffsets

/-! Structural rigidity of two six-degree triangles at a receiver of degree
at most five. No hull-source offsets or paper-case enumeration occur here. -/

namespace Erdos957

/-- Common neighbors of a nearest edge are separated by at most sqrt(3)
minimum lengths, expressed without square roots. -/
theorem nearest_common_neighbors_dist_sq_le_three
    {n : ℕ} (p : Fin n → Point) (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {u v a b : Fin n}
    (huv : (nearestGraph p).Adj u v)
    (hua : (nearestGraph p).Adj u a) (hva : (nearestGraph p).Adj v a)
    (hub : (nearestGraph p).Adj u b) (hvb : (nearestGraph p).Adj v b) :
    dist (p a) (p b) ^ 2 ≤ 3 * pairDist p ij ^ 2 := by
  by_cases hab : a = b
  · rw [hab, dist_self]
    nlinarith [sq_nonneg (pairDist p ij)]
  · have hr := pairDist_pos p hp hmin.1
    have hsum := equilateral_rhombus (p u) (p v) (p a) (p b) (pairDist p ij) hr
      (nearestGraph_adj_dist_eq p hmin huv)
      (nearestGraph_adj_dist_eq p hmin hua) (nearestGraph_adj_dist_eq p hmin hva)
      (nearestGraph_adj_dist_eq p hmin hub) (nearestGraph_adj_dist_eq p hmin hvb)
      (hp.ne hab)
    have hplus : (p a - p u) + (p b - p u) = p v - p u := by
      calc
        _ = (p a + p b) - p u - p u := by abel
        _ = _ := by rw [hsum]; abel
    have hminus : (p a - p u) - (p b - p u) = p a - p b := by abel
    have hpar := parallelogram_law_with_norm ℝ (p a - p u) (p b - p u)
    rw [hplus, hminus] at hpar
    simp only [← dist_eq_norm, dist_comm (p a) (p u), dist_comm (p b) (p u),
      dist_comm (p v) (p u), nearestGraph_adj_dist_eq p hmin hua,
      nearestGraph_adj_dist_eq p hmin hub, nearestGraph_adj_dist_eq p hmin huv] at hpar
    nlinarith

/-- Two six-degree bottoms adjacent to a receiver of degree at most five
force sufficiently separated five-degree centers to be antipodal there.
The argument counts forced neighbors and identifies overlaps by circle
intersection rigidity; it makes no classification by donor position. -/
theorem two_six_bottoms_force_antipodal_centers
    {n : ℕ} (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {x q₁ q₂ b₁ b₂ : Fin n}
    (hxdeg : (nearestGraph p).degree x ≤ 5)
    (hq₁deg : (nearestGraph p).degree q₁ = 5)
    (hq₂deg : (nearestGraph p).degree q₂ = 5)
    (hb₁deg : (nearestGraph p).degree b₁ = 6)
    (hb₂deg : (nearestGraph p).degree b₂ = 6)
    (hq₁x : (nearestGraph p).Adj q₁ x)
    (hq₂x : (nearestGraph p).Adj q₂ x)
    (hb₁x : (nearestGraph p).Adj b₁ x)
    (hb₂x : (nearestGraph p).Adj b₂ x)
    (hq₁b₁ : (nearestGraph p).Adj q₁ b₁)
    (hq₂b₂ : (nearestGraph p).Adj q₂ b₂)
    (hfar : 3 * pairDist p ij ^ 2 < dist (p q₁) (p q₂) ^ 2) :
    p q₁ + p q₂ = 2 • p x := by
  classical
  obtain ⟨t₁, ht₁q₁, hb₁t₁, hxt₁, hsum₁⟩ :=
    degree_six_triangle_completion p hn hp hb₁deg hb₁x hq₁b₁.symm hq₁x.symm
  obtain ⟨t₂, ht₂q₂, hb₂t₂, hxt₂, hsum₂⟩ :=
    degree_six_triangle_completion p hn hp hb₂deg hb₂x hq₂b₂.symm hq₂x.symm
  have hqne : q₁ ≠ q₂ := by
    intro heq
    rw [heq, dist_self] at hfar
    nlinarith [sq_nonneg (pairDist p ij)]
  have hq₁b₂ne : q₁ ≠ b₂ := by intro heq; rw [heq] at hq₁deg; omega
  have hq₂b₁ne : q₂ ≠ b₁ := by intro heq; rw [heq] at hq₂deg; omega
  have hbne : b₁ ≠ b₂ := by
    intro heq
    have hclose := nearest_common_neighbors_dist_sq_le_three p hp hmin hb₁x
      hq₁b₁.symm hq₁x.symm (by simpa only [heq] using hq₂b₂.symm) hq₂x.symm
    linarith
  have ht₁q₂ne : t₁ ≠ q₂ := by
    intro heq
    have hclose := nearest_common_neighbors_dist_sq_le_three p hp hmin hb₁x
      hq₁b₁.symm hq₁x.symm (by simpa only [heq] using hb₁t₁)
      (by simpa only [heq] using hxt₁)
    linarith
  have ht₂q₁ne : t₂ ≠ q₁ := by
    intro heq
    have hclose := nearest_common_neighbors_dist_sq_le_three p hp hmin hb₂x
      (by simpa only [heq] using hb₂t₂) (by simpa only [heq] using hxt₂)
      hq₂b₂.symm hq₂x.symm
    linarith
  have htne : t₁ ≠ t₂ := by
    intro heq
    have hclose := nearest_common_neighbors_dist_sq_le_three p hp hmin hxt₁
      hb₁x.symm hb₁t₁.symm hb₂x.symm (by simpa only [heq] using hb₂t₂.symm)
    have hdiff : p q₁ - p q₂ = p b₁ - p b₂ := by
      have heq₁ := eq_sub_of_add_eq hsum₁
      have heq₂ := eq_sub_of_add_eq hsum₂
      rw [heq₁, heq₂, heq]
      abel
    have hdist : dist (p q₁) (p q₂) = dist (p b₁) (p b₂) := by
      rw [dist_eq_norm, hdiff, ← dist_eq_norm]
    rw [hdist] at hfar
    linarith
  have hoverlap : t₁ = b₂ ∨ t₂ = b₁ := by
    by_contra hnone
    have hnone' : t₁ ≠ b₂ ∧ t₂ ≠ b₁ := not_or.mp hnone
    have hsub : ({q₁, b₁, t₁, q₂, b₂, t₂} : Finset (Fin n)) ⊆
        (nearestGraph p).neighborFinset x := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      apply ((nearestGraph p).mem_neighborFinset x a).mpr
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hq₁x.symm
      · exact hb₁x.symm
      · exact hxt₁
      · exact hq₂x.symm
      · exact hb₂x.symm
      · exact hxt₂
    have hcard : ({q₁, b₁, t₁, q₂, b₂, t₂} : Finset (Fin n)).card = 6 := by
      simp [hq₁b₁.ne, ht₁q₁.symm, hqne, hq₁b₂ne, ht₂q₁ne.symm,
        hb₁t₁.ne, hq₂b₁ne.symm, hbne, hnone'.2.symm, ht₁q₂ne,
        hnone'.1, htne, hq₂b₂.ne, ht₂q₂.symm, hb₂t₂.ne]
    have hle := Finset.card_le_card hsub
    rw [hcard, (nearestGraph p).card_neighborFinset_eq_degree] at hle
    omega
  have hr := pairDist_pos p hp hmin.1
  rcases hoverlap with ht₁ | ht₂
  · have hsum := equilateral_rhombus (p b₂) (p x) (p q₂) (p b₁)
      (pairDist p ij) hr (nearestGraph_adj_dist_eq p hmin hb₂x)
      (nearestGraph_adj_dist_eq p hmin hq₂b₂.symm)
      (nearestGraph_adj_dist_eq p hmin hq₂x.symm)
      (nearestGraph_adj_dist_eq p hmin (by simpa only [ht₁] using hb₁t₁.symm))
      (nearestGraph_adj_dist_eq p hmin hb₁x.symm) (hp.ne hq₂b₁ne)
    rw [ht₁] at hsum₁
    calc
      p q₁ + p q₂ = (p q₁ + p b₂) + (p q₂ + p b₁) - p b₁ - p b₂ := by abel
      _ = (p b₁ + p x) + (p b₂ + p x) - p b₁ - p b₂ := by rw [hsum₁, hsum]
      _ = 2 • p x := by rw [two_smul]; abel
  · have hsum := equilateral_rhombus (p b₁) (p x) (p q₁) (p b₂)
      (pairDist p ij) hr (nearestGraph_adj_dist_eq p hmin hb₁x)
      (nearestGraph_adj_dist_eq p hmin hq₁b₁.symm)
      (nearestGraph_adj_dist_eq p hmin hq₁x.symm)
      (nearestGraph_adj_dist_eq p hmin (by simpa only [ht₂] using hb₂t₂.symm))
      (nearestGraph_adj_dist_eq p hmin hb₂x.symm) (hp.ne hq₁b₂ne)
    rw [ht₂] at hsum₂
    calc
      p q₁ + p q₂ = (p q₁ + p b₂) + (p q₂ + p b₁) - p b₁ - p b₂ := by abel
      _ = (p b₁ + p x) + (p b₂ + p x) - p b₁ - p b₂ := by rw [hsum, hsum₂]
      _ = 2 • p x := by rw [two_smul]; abel

/-- A uniform separation estimate for two disjoint nearest endpoint pairs
in one thin boundary strip. The first pair is normalized to 0 and 1. The
second center lies within 1/8 horizontally of its endpoint midpoint, as an
equilateral center does when both endpoints have heights in [0,1/8]. -/
theorem thin_strip_pair_centers_separated
    (C D Q Z : ℂ)
    (hCstrip : 0 ≤ C.im ∧ C.im ≤ 1 / 8)
    (hDstrip : 0 ≤ D.im ∧ D.im ≤ 1 / 8)
    (hC0 : 1 ≤ ‖C‖) (hC1 : 1 ≤ ‖C - 1‖)
    (hD0 : 1 ≤ ‖D‖) (hD1 : 1 ≤ ‖D - 1‖)
    (hCD : dist C D = 1)
    (hQlo : (C.re + D.re) / 2 - 1 / 8 ≤ Q.re)
    (hQhi : Q.re ≤ (C.re + D.re) / 2 + 1 / 8)
    (hZ : Z.re = 1 / 2) : 3 < dist Q Z ^ 2 := by
  have hnorm (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z
  have hside (z : ℂ) (hstrip : 0 ≤ z.im ∧ z.im ≤ 1 / 8)
      (h0 : 1 ≤ ‖z‖) (h1 : 1 ≤ ‖z - 1‖) :
      z.re ≤ -(99 / 100 : ℝ) ∨ 199 / 100 ≤ z.re := by
    have hy : z.im ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by nlinarith [hstrip.1, hstrip.2]
    have hn0 := hnorm z
    have hn1 := hnorm (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero] at hn1
    rcases le_or_gt z.re (1 / 2) with hleft | hright
    · left
      by_contra hbad
      have hprod := mul_pos (show 0 < 99 / 100 - z.re by linarith)
        (show 0 < 99 / 100 + z.re by linarith)
      nlinarith [sq_nonneg (‖z‖ - 1)]
    · right
      by_contra hbad
      have hprod := mul_pos (show 0 < 99 / 100 - (z.re - 1) by linarith)
        (show 0 < 99 / 100 + (z.re - 1) by linarith)
      nlinarith [sq_nonneg (‖z - 1‖ - 1)]
  have hdist : (C.re - D.re) ^ 2 + (C.im - D.im) ^ 2 = 1 := by
    have ht := hnorm (C - D)
    simpa only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm, hCD, one_pow] using ht
  have hy : |C.im - D.im| ≤ 1 / 8 := by
    exact abs_le.mpr ⟨by linarith [hCstrip.1, hDstrip.2],
      by linarith [hCstrip.2, hDstrip.1]⟩
  have hySq : (C.im - D.im) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    have hh := (abs_le.mp hy)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 8 - (C.im - D.im))
      (by linarith : 0 ≤ 1 / 8 + (C.im - D.im))]
  have hgap : 99 / 100 ≤ |C.re - D.re| := by
    by_contra hbad
    have hab := abs_nonneg (C.re - D.re)
    have hs := sq_abs (C.re - D.re)
    nlinarith
  have hspan : |C.re - D.re| ≤ 1 := by
    nlinarith [sq_abs (C.re - D.re), abs_nonneg (C.re - D.re),
      sq_nonneg (C.im - D.im)]
  have hQdist : (Q.re - 1 / 2) ^ 2 ≤ dist Q Z ^ 2 := by
    have heq := hnorm (Q - Z)
    simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm, hZ] at heq
    nlinarith [sq_nonneg (Q.im - Z.im)]
  rcases hside C hCstrip hC0 hC1 with hCL | hCR <;>
    rcases hside D hDstrip hD0 hD1 with hDL | hDR
  · have hsum : C.re + D.re ≤ -(297 / 100 : ℝ) := by
      rcases le_or_gt C.re D.re with horder | horder
      · rw [abs_of_nonpos (by linarith)] at hgap
        linarith
      · rw [abs_of_nonneg (by linarith)] at hgap
        linarith
    have hQ : Q.re - 1 / 2 ≤ -(186 / 100 : ℝ) := by linarith
    nlinarith
  · have hs := (abs_le.mp hspan).1
    linarith
  · have hs := (abs_le.mp hspan).2
    linarith
  · have hsum : 497 / 100 ≤ C.re + D.re := by
      rcases le_or_gt C.re D.re with horder | horder
      · rw [abs_of_nonpos (by linarith)] at hgap
        linarith
      · rw [abs_of_nonneg (by linarith)] at hgap
        linarith
    have hQ : 186 / 100 ≤ Q.re - 1 / 2 := by linarith
    nlinarith

/-- The rigidity dichotomy applies to any two actual indirect sources in
the supplied family, without a source-offset premise or a case label input.
The short-distance alternative is explicit until hull geometry excludes it. -/
theorem SixBottomIndirectSource.two_centers_close_or_antipodal
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {x u w : Fin n} (hxdeg : (nearestGraph p).degree x ≤ 5)
    (hu : SixBottomIndirectSource p v height assignments x u)
    (hw : SixBottomIndirectSource p v height assignments x w) :
    ∃ (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
      (hwd : w ∈ chargeDonors p (tightHullBadVertices p v)),
      dist (p (assignments u hud).context.q) (p (assignments w hwd).context.q) ^ 2 ≤
        3 * pairDist p ij ^ 2 ∨
      p (assignments u hud).context.q + p (assignments w hwd).context.q = 2 • p x := by
  obtain ⟨hud, _hux, _hunot, avU, hbU⟩ := hu
  obtain ⟨hwd, _hwx, _hwnot, avW, hbW⟩ := hw
  let first := selectedSharedFiveCenter p (assignments u hud).context.q avU
  let second := selectedSharedFiveCenter p (assignments w hwd).context.q avW
  obtain ⟨hud', avU', hbxU, hqxU⟩ :=
    (show SixBottomIndirectSource p v height assignments x u from
      ⟨hud, _hux, _hunot, avU, hbU⟩).receiver_adj_center_and_bottom p v height assignments
  obtain ⟨hwd', avW', hbxW, hqxW⟩ :=
    (show SixBottomIndirectSource p v height assignments x w from
      ⟨hwd, _hwx, _hwnot, avW, hbW⟩).receiver_adj_center_and_bottom p v height assignments
  have hpu : hud' = hud := Subsingleton.elim _ _
  have hpw : hwd' = hwd := Subsingleton.elim _ _
  subst hud'
  subst hwd'
  have havu : avU' = avU := Subsingleton.elim _ _
  have havw : avW' = avW := Subsingleton.elim _ _
  subst avU'
  subst avW'
  refine ⟨hud, hwd, ?_⟩
  by_cases hclose : dist (p (assignments u hud).context.q)
      (p (assignments w hwd).context.q) ^ 2 ≤ 3 * pairDist p ij ^ 2
  · exact Or.inl hclose
  · exact Or.inr (two_six_bottoms_force_antipodal_centers p hn hp hmin hxdeg
      first.center_degree second.center_degree hbU hbW hqxU hqxW hbxU hbxW
      first.selection.bottom_adj second.selection.bottom_adj (lt_of_not_ge hclose))

end Erdos957
