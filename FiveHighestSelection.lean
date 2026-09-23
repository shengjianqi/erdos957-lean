import CertifiedCentralPackets
import FlatCentralProjection
import TwoCircleSeparation

/-! Selection by actual supporting-frame height. Noncommon neighbors of the
center lie at least as deep as the center, while common neighbors lie no
deeper. Consequently maximizing supporting height among the common neighbors
also maximizes it among every center-neighbor except the donor. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Height toward the exterior in an oriented supporting-edge frame. -/
noncomputable def supportingHeight {n : ℕ} (p : Fin n → Point)
    (u s x : Fin n) : ℝ := -(edgeCoordinate (p u) (p s) (p x)).im

/-- Avoiding the two outer unit disks traps a shifted unit-circle neighbor
between the two outer directions at the first center. -/
theorem shifted_unit_neighbor_arg_between (a c z : ℂ)
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) (hz : ‖z‖ = 1)
    (haarg : -Real.pi < a.arg ∧ a.arg < 0)
    (hcarg : 0 < c.arg ∧ c.arg < Real.pi)
    (horigin : 1 ≤ ‖1 + z‖)
    (hSa : 1 ≤ dist a (1 + z)) (hSc : 1 ≤ dist c (1 + z)) :
    a.arg ≤ z.arg ∧ z.arg ≤ c.arg := by
  have hzarg := unit_arg_lt_pi_of_one_le_norm_add_one z hz horigin
  constructor
  · by_contra hnot
    have hza : z.arg < a.arg := lt_of_not_ge hnot
    have haπ : a.arg ≠ Real.pi := by linarith [Real.pi_pos]
    have hzπ : z.arg ≠ Real.pi := ne_of_lt hzarg
    have haconj : (conj a).arg = -a.arg := by simp [Complex.arg_conj, haπ]
    have hzconj : (conj z).arg = -z.arg := by simp [Complex.arg_conj, hzπ]
    have hsmall := unit_circle_shift_dist_lt_one (conj a) (conj z)
      (by simpa using ha) (by simpa using hz)
      (by rw [haconj]; linarith) (by rw [haconj, hzconj]; linarith)
      (by rw [hzconj]; linarith [Complex.neg_pi_lt_arg z])
    have heq : dist (conj a) (1 + conj z) = dist a (1 + z) := by
      rw [dist_eq_norm, show conj a - (1 + conj z) = conj (a - (1 + z)) by simp,
        Complex.norm_conj, ← dist_eq_norm]
    rw [heq] at hsmall
    linarith
  · by_contra hnot
    have hsmall := unit_circle_shift_dist_lt_one c z hc hz hcarg.1
      (lt_of_not_ge hnot) hzarg
    linarith

/-- A direction in a cone of width less than pi preserves each nonnegative
linear height that is nonnegative on the two boundary directions. -/
theorem short_arg_cone_mul_im_nonneg (a c z Q : ℂ)
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1)
    (hac : a.arg < c.arg) (hspan : c.arg - a.arg < Real.pi)
    (haz : a.arg ≤ z.arg) (hzc : z.arg ≤ c.arg)
    (hQa : 0 ≤ (Q * a).im) (hQc : 0 ≤ (Q * c).im) :
    0 ≤ (Q * z).im := by
  have hcross : 0 < (conj a * c).im := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub, ha, hc]
    simpa only [one_mul] using
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hac) hspan
  have hazcross : 0 ≤ (conj a * z).im := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr haz) (by linarith))
  have hzccross : 0 ≤ (conj z * c).im := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hzc) (by linarith))
  have hid : (conj a * c).im * (Q * z).im =
      (conj z * c).im * (Q * a).im + (conj a * z).im * (Q * c).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hprod : 0 ≤ (conj a * c).im * (Q * z).im := by
    rw [hid]
    exact add_nonneg (mul_nonneg hzccross hQa) (mul_nonneg hazcross hQc)
  exact nonneg_of_mul_nonneg_right hprod hcross

private theorem edgeCoordinate_mul_change (u q s x : Point) (huq : u ≠ q) :
    edgeCoordinate u s x = edgeCoordinate u s q * edgeCoordinate u q x := by
  have hden : pointToComplex (q - u) ≠ 0 := by
    intro hzero
    exact huq (sub_eq_zero.mp (pointToComplex.injective (by simpa using hzero))).symm
  simp only [edgeCoordinate]
  field_simp

/-- Every noncommon neighbor of the actual center is at least as deep as
the center in any actual supporting-edge frame at the donor. -/
theorem central_noncommon_neighbor_im_ge {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    {b : Fin n} (hqb : (nearestGraph p).Adj ctx.q b) (hbu : b ≠ u)
    (hnot : ¬ (nearestGraph p).Adj u b) :
    (edgeCoordinate (p u) (p s) (p ctx.q)).im ≤
      (edgeCoordinate (p u) (p s) (p b)).im := by
  obtain ⟨v, _hvinj, _hvrange, hvadj, hvmono, _hgap01, _hgap12, hvlo, hvhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp ctx.diameter_adj ctx.degree_three
  have hmiddle : v 1 = ctx.q := ctx.central_unique (v 1) (hvadj 1) hvlo hvhi
  let E := edgeCoordinate (p u) (p ctx.q)
  let M := edgeCoordinate (p u) (p s)
  let A := E (p (v 0))
  let C := E (p (v 2))
  let z := E (p b) - 1
  have hne := hp.ne ctx.central_adj.ne
  have hL := dist_pos.mpr (hp.ne hus)
  have hr := pairDist_pos p hp ctx.minPair_spec.1
  have hnorm (a : Fin n) (hua : (nearestGraph p).Adj u a) : ‖E (p a)‖ = 1 := by
    dsimp [E]
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hua,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj, div_self hr.ne']
  have ha : ‖A‖ = 1 := hnorm _ (hvadj 0)
  have hc : ‖C‖ = 1 := hnorm _ (hvadj 2)
  have haxis (t : Fin 3) :
      0 < inner ℝ (p ctx.j - p u) (p (v t) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp ctx.diameter_adj (hvadj t).ne
  have hqaxis : 0 < inner ℝ (p ctx.j - p u) (p ctx.q - p u) := by
    simpa only [hmiddle] using haxis 1
  have hAa : A.arg = halfplaneArg (p u) (p ctx.j - p u) (p (v 0)) -
      halfplaneArg (p u) (p ctx.j - p u) (p ctx.q) :=
    edgeCoordinate_arg _ _ _ _ hqaxis (haxis 0)
  have hCa : C.arg = halfplaneArg (p u) (p ctx.j - p u) (p (v 2)) -
      halfplaneArg (p u) (p ctx.j - p u) (p ctx.q) :=
    edgeCoordinate_arg _ _ _ _ hqaxis (haxis 2)
  have h01 := hvmono 0 1 (by decide)
  have h12 := hvmono 1 2 (by decide)
  rw [hmiddle] at h01 h12
  have hfull : halfplaneArg (p u) (p ctx.j - p u) (p (v 2)) -
      halfplaneArg (p u) (p ctx.j - p u) (p (v 0)) < Real.pi := by
    have hlo := (halfplaneArg_mem_Ioo (haxis 0)).1
    have hhi := (halfplaneArg_mem_Ioo (haxis 2)).2
    linarith
  have hAarg : -Real.pi < A.arg ∧ A.arg < 0 := by rw [hAa]; constructor <;> linarith
  have hCarg : 0 < C.arg ∧ C.arg < Real.pi := by rw [hCa]; constructor <;> linarith
  have hspan : C.arg - A.arg < Real.pi := by rw [hAa, hCa]; linarith
  have hz : ‖z‖ = 1 := by
    dsimp [z, E]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hqb,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj, div_self hr.ne']
  have hE (a c : Fin n) (hac : a ≠ c) : 1 ≤ dist (E (p a)) (E (p c)) := by
    dsimp [E]
    rw [edgeCoordinate_dist _ _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj]
    exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using
      (isMinPair_le_dist p ctx.minPair_spec hac))
  have hEz : 1 + z = E (p b) := by dsimp [z]; ring
  have horigin : 1 ≤ ‖1 + z‖ := by
    rw [hEz]
    have h := hE u b hbu.symm
    simpa only [E, edgeCoordinate_self, dist_zero_left] using h
  have hSa : 1 ≤ dist A (1 + z) := by
    rw [hEz]
    exact hE _ _ (fun heq => hnot (heq ▸ hvadj 0))
  have hSc : 1 ≤ dist C (1 + z) := by
    rw [hEz]
    exact hE _ _ (fun heq => hnot (heq ▸ hvadj 2))
  have hbetween := shifted_unit_neighbor_arg_between A C z ha hc hz hAarg hCarg
    horigin hSa hSc
  have hM (a : Fin n) : 0 ≤ (M (p a)).im := by
    have heq := edgeCoordinate_im_mul_dist_sq (p u) (p s) (p a) (hp.ne hus)
    have hs := hsupport a
    change (M (p a)).im * dist (p u) (p s) ^ 2 = _ at heq
    nlinarith [sq_pos_of_pos hL]
  have hchange (a : Fin n) : M (p a) = M (p ctx.q) * E (p a) :=
    edgeCoordinate_mul_change _ _ _ _ hne
  have hcone := short_arg_cone_mul_im_nonneg A C z (M (p ctx.q)) ha hc
    (by linarith [hAarg.2, hCarg.1]) hspan hbetween.1 hbetween.2
    (by change 0 ≤ (M (p ctx.q) * E (p (v 0))).im
        rw [← hchange (v 0)]; exact hM (v 0))
    (by change 0 ≤ (M (p ctx.q) * E (p (v 2))).im
        rw [← hchange (v 2)]; exact hM (v 2))
  have hid : M (p ctx.q) * z = M (p b) - M (p ctx.q) := by
    rw [hchange b]
    dsimp [z]
    ring
  rw [hid, Complex.sub_im] at hcone
  exact sub_nonneg.mp hcone

/-- When the central radius makes at most thirty degrees with the inward
normal, either equilateral common point is no deeper than the center. -/
theorem equilateral_mul_im_le (Q a : ℂ) (r : ℝ)
    (hQ : ‖Q‖ = r) (hQre : |Q.re| ≤ r / 2) (hQim : 0 ≤ Q.im)
    (ha : ‖a‖ = 1) (ha1 : ‖a - 1‖ = 1) : (Q * a).im ≤ Q.im := by
  have hsq := Complex.normSq_eq_norm_sq a
  have hsq1 := Complex.normSq_eq_norm_sq (a - 1)
  rw [Complex.normSq_apply, ha] at hsq
  rw [Complex.normSq_apply, ha1] at hsq1
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_zero] at hsq1
  have hare : a.re = 1 / 2 := by nlinarith
  have hai : a.im ^ 2 = 3 / 4 := by nlinarith
  have hQsq : Q.re ^ 2 + Q.im ^ 2 = r ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two, hQ] using Complex.normSq_eq_norm_sq Q
  have hprod : 0 ≤ (r / 2 - Q.re) * (r / 2 + Q.re) :=
    mul_nonneg (by linarith [(abs_le.mp hQre).2])
      (by linarith [(abs_le.mp hQre).1])
  have hQR : Q.re ^ 2 ≤ r ^ 2 / 4 := by nlinarith
  have hpsq : (Q.re * a.im) ^ 2 = 3 / 4 * Q.re ^ 2 := by rw [mul_pow, hai]; ring
  have hple : (Q.re * a.im) ^ 2 ≤ (Q.im / 2) ^ 2 := by nlinarith
  have hpabs : |Q.re * a.im| ≤ Q.im / 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by linarith)).mp (by simpa only [sq_abs] using hple)
  have hp := (le_abs_self (Q.re * a.im)).trans hpabs
  rw [Complex.mul_im, hare]
  linarith

/-- Every actual common nearest neighbor lies no deeper than the central
neighbor in the same supporting frame used to choose the receiver. -/
theorem central_common_neighbor_im_le {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    {a : Fin n} (hua : (nearestGraph p).Adj u a)
    (hqa : (nearestGraph p).Adj ctx.q a) :
    (edgeCoordinate (p u) (p s) (p a)).im ≤
      (edgeCoordinate (p u) (p s) (p ctx.q)).im := by
  let M := edgeCoordinate (p u) (p s)
  let E := edgeCoordinate (p u) (p ctx.q)
  let r := pairDist p ctx.minPair / dist (p u) (p s)
  have husp := hp.ne hus
  have huq := hp.ne ctx.central_adj.ne
  have hr := pairDist_pos p hp ctx.minPair_spec.1
  have hL := dist_pos.mpr husp
  have hQ : ‖M (p ctx.q)‖ = r := by
    dsimp [M, r]
    rw [edgeCoordinate_norm _ _ _ husp,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj]
  have hQre : |(M (p ctx.q)).re| ≤ r / 2 :=
    central_neighbor_re_bound_of_support p hn hp ctx hus hsupport
  have hQim : 0 ≤ (M (p ctx.q)).im := by
    have heq := edgeCoordinate_im_mul_dist_sq (p u) (p s) (p ctx.q) husp
    have hs := hsupport ctx.q
    change (M (p ctx.q)).im * dist (p u) (p s) ^ 2 = _ at heq
    nlinarith [sq_pos_of_pos hL]
  have ha : ‖E (p a)‖ = 1 := by
    dsimp [E]
    rw [edgeCoordinate_norm _ _ _ huq,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hua,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj, div_self hr.ne']
  have ha1 : ‖E (p a) - 1‖ = 1 := by
    dsimp [E]
    rw [edgeCoordinate_sub_one_norm _ _ _ huq,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hqa,
      nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj, div_self hr.ne']
  change (M (p a)).im ≤ (M (p ctx.q)).im
  rw [show M (p a) = M (p ctx.q) * E (p a) from edgeCoordinate_mul_change _ _ _ _ huq]
  exact equilateral_mul_im_le _ _ r hQ hQre hQim ha ha1

/-- In an actual supporting frame, each common neighbor is at least as high
as each noncommon neighbor of the center other than the donor. -/
theorem common_neighbor_supporting_height_ge_noncommon {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    {a b : Fin n} (hua : (nearestGraph p).Adj u a)
    (hqa : (nearestGraph p).Adj ctx.q a) (hqb : (nearestGraph p).Adj ctx.q b)
    (hbu : b ≠ u) (hnot : ¬ (nearestGraph p).Adj u b) :
    supportingHeight p u s b ≤ supportingHeight p u s a := by
  have ha := central_common_neighbor_im_le p hn hp ctx hus hsupport hua hqa
  have hb := central_noncommon_neighbor_im_ge p hn hp ctx hus hsupport hqb hbu hnot
  dsimp [supportingHeight]
  linarith

/-- An actual five-degree center has a common neighbor maximizing the real
supporting height over all its neighbors except the donor. -/
theorem degree_five_central_has_supporting_highest_common {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    (hfive : (nearestGraph p).degree ctx.q = 5) :
    ∃ a, (nearestGraph p).Adj u a ∧ (nearestGraph p).Adj ctx.q a ∧
      ∀ b, (nearestGraph p).Adj ctx.q b → b ≠ u →
        supportingHeight p u s b ≤ supportingHeight p u s a := by
  classical
  let S := (nearestGraph p).neighborFinset u ∩ (nearestGraph p).neighborFinset ctx.q
  have hSne : S.Nonempty := by
    obtain ⟨a, hua, hqa⟩ := degree_five_central_neighbor_has_common_neighbor
      p hn hp ctx.diameter_adj ctx.degree_three ctx.central_adj
      ctx.central_lo ctx.central_hi hfive
    exact ⟨a, Finset.mem_inter.mpr
      ⟨((nearestGraph p).mem_neighborFinset u a).mpr hua,
        ((nearestGraph p).mem_neighborFinset ctx.q a).mpr hqa⟩⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (supportingHeight p u s) hSne
  have hua := ((nearestGraph p).mem_neighborFinset u a).mp (Finset.mem_inter.mp ha).1
  have hqa := ((nearestGraph p).mem_neighborFinset ctx.q a).mp (Finset.mem_inter.mp ha).2
  refine ⟨a, hua, hqa, ?_⟩
  intro b hqb hbu
  by_cases hub : (nearestGraph p).Adj u b
  · exact hmax b (Finset.mem_inter.mpr
      ⟨((nearestGraph p).mem_neighborFinset u b).mpr hub,
        ((nearestGraph p).mem_neighborFinset ctx.q b).mpr hqb⟩)
  · exact common_neighbor_supporting_height_ge_noncommon p hn hp ctx hus hsupport
      hua hqa hqb hbu hub

/-- The existing five-degree certificate, scored in the actual supporting
frame, already chooses a global height maximum among all non-donor neighbors. -/
theorem CertifiedCentralPacket.five_supporting_global_maximum {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    (choice : CertifiedCentralPacket p u ctx.q (supportingHeight p u s))
    (hfive : (nearestGraph p).degree ctx.q = 5) :
    (nearestGraph p).Adj u choice.packet.right ∧
      (nearestGraph p).Adj ctx.q choice.packet.right ∧
      ∀ b, (nearestGraph p).Adj ctx.q b → b ≠ u →
        supportingHeight p u s b ≤ supportingHeight p u s choice.packet.right := by
  classical
  rcases choice.rule with hlow | hfiveRule | hsix
  · omega
  · obtain ⟨_, _, hur, hqr, hmax⟩ := hfiveRule
    refine ⟨hur, hqr, ?_⟩
    intro b hqb hbu
    by_cases hub : (nearestGraph p).Adj u b
    · exact hmax b hub hqb
    · exact common_neighbor_supporting_height_ge_noncommon p hn hp ctx hus hsupport
        hur hqr hqb hbu hub
  · omega

end Erdos957
