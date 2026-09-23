import SupportedCentralNeighbor
import Mathlib.Tactic.FinCases

/-! A supported nearest triangle at a degree-three donor uses the donor's
retained central neighbor as its third vertex. -/

namespace Erdos957

private theorem unit_triangle_arg_not_large (z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : ‖z - 1‖ = 1)
    (hlo : 2 * Real.pi / 3 ≤ z.arg) : False := by
  have hs := Complex.normSq_eq_norm_sq z
  have hs1 := Complex.normSq_eq_norm_sq (z - 1)
  rw [Complex.normSq_apply, hz] at hs
  rw [Complex.normSq_apply, hz1] at hs1
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_zero] at hs1
  have hre : z.re = 1 / 2 := by nlinarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * Real.pi / 3 by positivity) (Complex.arg_le_pi z) hlo
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three] at hcos
  have heq := Complex.norm_mul_cos_arg z
  rw [hz, one_mul, hre] at heq
  linarith

private theorem donor_neighbor_order_geometry {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u : Fin n} (ctx : DonorContext p bad u) :
    ∃ v : Fin 3 → Fin n,
      Set.range v = ((nearestGraph p).neighborFinset u : Set (Fin n)) ∧
      v 1 = ctx.q ∧ ¬ (nearestGraph p).Adj (v 0) (v 2) ∧
      turn (p u) (p ctx.q) (p (v 0)) < 0 ∧
      0 < turn (p u) (p ctx.q) (p (v 2)) := by
  obtain ⟨v, _hvinj, hvrange, hvadj, hvmono, hgap01, hgap12, hvlo, hvhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp ctx.diameter_adj ctx.degree_three
  have hmiddle : v 1 = ctx.q := ctx.central_unique (v 1) (hvadj 1) hvlo hvhi
  have hhalf (t : Fin 3) :
      0 < inner ℝ (p ctx.j - p u) (p (v t) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp ctx.diameter_adj (hvadj t).ne
  have hqhalf : 0 < inner ℝ (p ctx.j - p u) (p ctx.q - p u) := by
    simpa only [hmiddle] using hhalf 1
  have hr := pairDist_pos p hp ctx.minPair_spec.1
  have hne := hp.ne ctx.central_adj.ne
  have hdistq := nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj
  let E := edgeCoordinate (p u) (p ctx.q)
  have hnorm (t : Fin 3) : ‖E (p (v t))‖ = 1 := by
    dsimp [E]
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj t), hdistq, div_self hr.ne']
  have harg (t : Fin 3) : (E (p (v t))).arg =
      halfplaneArg (p u) (p ctx.j - p u) (p (v t)) -
        halfplaneArg (p u) (p ctx.j - p u) (p ctx.q) :=
    edgeCoordinate_arg _ _ _ _ hqhalf (hhalf t)
  have hspan : halfplaneArg (p u) (p ctx.j - p u) (p (v 2)) -
      halfplaneArg (p u) (p ctx.j - p u) (p (v 0)) < Real.pi := by
    have hlo := (halfplaneArg_mem_Ioo (hhalf 0)).1
    have hhi := (halfplaneArg_mem_Ioo (hhalf 2)).2
    linarith
  have h01 := hvmono 0 1 (by decide)
  have h12 := hvmono 1 2 (by decide)
  rw [hmiddle] at h01 h12
  have hAarg : -Real.pi < (E (p (v 0))).arg ∧ (E (p (v 0))).arg < 0 := by
    rw [harg]
    constructor <;> linarith
  have hCarg : 0 < (E (p (v 2))).arg ∧ (E (p (v 2))).arg < Real.pi := by
    rw [harg]
    constructor <;> linarith
  have hAneg : (E (p (v 0))).im < 0 := by
    have heq := Complex.norm_mul_sin_arg (E (p (v 0)))
    rw [hnorm, one_mul] at heq
    rw [← heq]
    exact Real.sin_neg_of_neg_of_neg_pi_lt hAarg.2 hAarg.1
  have hCpos : 0 < (E (p (v 2))).im := by
    have heq := Complex.norm_mul_sin_arg (E (p (v 2)))
    rw [hnorm, one_mul] at heq
    rw [← heq]
    exact Real.sin_pos_of_pos_of_lt_pi hCarg.1 hCarg.2
  have hscale : 0 < dist (p u) (p ctx.q) ^ 2 := sq_pos_of_pos (dist_pos.mpr hne)
  have hturn0 : turn (p u) (p ctx.q) (p (v 0)) < 0 := by
    rw [← edgeCoordinate_im_mul_dist_sq _ _ _ hne]
    exact mul_neg_of_neg_of_pos hAneg hscale
  have hturn2 : 0 < turn (p u) (p ctx.q) (p (v 2)) := by
    rw [← edgeCoordinate_im_mul_dist_sq _ _ _ hne]
    exact mul_pos hCpos hscale
  refine ⟨v, hvrange, hmiddle, ?_, hturn0, hturn2⟩
  intro h02
  let Z := edgeCoordinate (p u) (p (v 0)) (p (v 2))
  have hne0 := hp.ne (hvadj 0).ne
  have hdist0 := nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj 0)
  have hZ : ‖Z‖ = 1 := by
    dsimp [Z]
    rw [edgeCoordinate_norm _ _ _ hne0,
      nearestGraph_adj_dist_eq p ctx.minPair_spec (hvadj 2), hdist0, div_self hr.ne']
  have hZ1 : ‖Z - 1‖ = 1 := by
    dsimp [Z]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne0,
      nearestGraph_adj_dist_eq p ctx.minPair_spec h02, hdist0, div_self hr.ne']
  have hZa : Z.arg = halfplaneArg (p u) (p ctx.j - p u) (p (v 2)) -
      halfplaneArg (p u) (p ctx.j - p u) (p (v 0)) :=
    edgeCoordinate_arg _ _ _ _ (hhalf 0) (hhalf 2)
  apply unit_triangle_arg_not_large Z hZ hZ1
  rw [hZa]
  linarith

/-- Any nearest triangle incident to a degree-three donor contains the
central neighbor among its two other vertices. -/
theorem donor_nearest_triangle_contains_central {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u w q : Fin n} (ctx : DonorContext p bad u)
    (huw : (nearestGraph p).Adj u w) (huq : (nearestGraph p).Adj u q)
    (hwq : (nearestGraph p).Adj w q) : w = ctx.q ∨ q = ctx.q := by
  obtain ⟨v, hvrange, hmiddle, houter, _, _⟩ := donor_neighbor_order_geometry p hn hp ctx
  have hin (a : Fin n) (hua : (nearestGraph p).Adj u a) : ∃ t, v t = a := by
    have hm : a ∈ ((nearestGraph p).neighborFinset u : Set (Fin n)) :=
      ((nearestGraph p).mem_neighborFinset u a).mpr hua
    rwa [← hvrange] at hm
  obtain ⟨iw, hiw⟩ := hin w huw
  obtain ⟨iq, hiq⟩ := hin q huq
  by_cases hw : iw = 1
  · exact Or.inl (hiw.symm.trans (hw ▸ hmiddle))
  by_cases hq : iq = 1
  · exact Or.inr (hiq.symm.trans (hq ▸ hmiddle))
  have hwcases : iw = 0 ∨ iw = 2 := by fin_cases iw <;> simp_all
  have hqcases : iq = 0 ∨ iq = 2 := by fin_cases iq <;> simp_all
  rcases hwcases with rfl | rfl <;> rcases hqcases with rfl | rfl
  · exact False.elim (hwq.ne (hiw.symm.trans hiq))
  · exact False.elim (houter (by simpa only [hiw, hiq] using hwq))
  · exact False.elim (houter (by simpa only [hiw, hiq] using hwq.symm))
  · exact False.elim (hwq.ne (hiw.symm.trans hiq))

/-- A line through the donor and its retained central neighbor cannot
support the configuration: the two outer neighbors lie on opposite sides. -/
theorem donor_central_edge_not_supporting {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u : Fin n} (ctx : DonorContext p bad u) :
    ¬ ((∀ k, 0 ≤ turn (p u) (p ctx.q) (p k)) ∨
      (∀ k, 0 ≤ turn (p ctx.q) (p u) (p k))) := by
  obtain ⟨v, _, _, _, hneg, hpos⟩ := donor_neighbor_order_geometry p hn hp ctx
  rintro (hs | hs)
  · exact (not_le_of_gt hneg) (hs (v 0))
  · have h := hs (v 2)
    rw [turn_reverse] at h
    linarith

/-- The third vertex of a supported nearest equilateral triangle at an
actual donor equals its retained central neighbor, in either orientation. -/
theorem supported_nearest_triangle_center_eq {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u w q : Fin n} (ctx : DonorContext p bad u)
    (huw : (nearestGraph p).Adj u w) (huq : (nearestGraph p).Adj u q)
    (hwq : (nearestGraph p).Adj w q)
    (hsupport : (∀ k, 0 ≤ turn (p u) (p w) (p k)) ∨
      (∀ k, 0 ≤ turn (p w) (p u) (p k))) : q = ctx.q := by
  rcases donor_nearest_triangle_contains_central p hn hp ctx huw huq hwq with hw | hq
  · exact False.elim (donor_central_edge_not_supporting p hn hp ctx (hw ▸ hsupport))
  · exact hq

/-- Two supported nearest triangles with high-degree centers cannot meet at
one diameter endpoint while having different centers. The common endpoint
may be exceptional: degree three follows from the two centers and a diameter
partner, and an auxiliary donor context uses the empty exceptional set. -/
theorem high_degree_supported_triangle_centers_eq_of_diameterEndpoint {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {u w₁ w₂ q₁ q₂ : Fin n}
    (hu : u ∈ diameterEndpoints p)
    (hw₁ : w₁ ∈ diameterEndpoints p) (_hw₂ : w₂ ∈ diameterEndpoints p)
    (huw₁ : (nearestGraph p).Adj u w₁) (huw₂ : (nearestGraph p).Adj u w₂)
    (huq₁ : (nearestGraph p).Adj u q₁) (huq₂ : (nearestGraph p).Adj u q₂)
    (hwq₁ : (nearestGraph p).Adj w₁ q₁) (hwq₂ : (nearestGraph p).Adj w₂ q₂)
    (hdeg₁ : 4 ≤ (nearestGraph p).degree q₁)
    (hdeg₂ : 4 ≤ (nearestGraph p).degree q₂)
    (hsupport₁ : (∀ k, 0 ≤ turn (p u) (p w₁) (p k)) ∨
      (∀ k, 0 ≤ turn (p w₁) (p u) (p k)))
    (hsupport₂ : (∀ k, 0 ≤ turn (p u) (p w₂) (p k)) ∨
      (∀ k, 0 ≤ turn (p w₂) (p u) (p k))) : q₁ = q₂ := by
  classical
  by_contra hqne
  have hn2 : 2 ≤ n := by omega
  have huwdeg := nearestGraph_degree_le_three_of_diameterEndpoint p hn2 hp w₁ hw₁
  have hwq₁ne : w₁ ≠ q₁ := by intro heq; rw [heq] at huwdeg; omega
  have hwq₂ne : w₁ ≠ q₂ := by intro heq; rw [heq] at huwdeg; omega
  have hsub : ({w₁, q₁, q₂} : Finset (Fin n)) ⊆ (nearestGraph p).neighborFinset u := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    apply ((nearestGraph p).mem_neighborFinset u a).mpr
    rcases ha with rfl | rfl | rfl
    · exact huw₁
    · exact huq₁
    · exact huq₂
  have hcard : ({w₁, q₁, q₂} : Finset (Fin n)).card = 3 := by
    simp [hwq₁ne, hwq₂ne, hqne]
  have hge : 3 ≤ (nearestGraph p).degree u := by
    have h := Finset.card_le_card hsub
    rwa [hcard, (nearestGraph p).card_neighborFinset_eq_degree u] at h
  have hle := nearestGraph_degree_le_three_of_diameterEndpoint p hn2 hp u hu
  have hdegree : (nearestGraph p).degree u = 3 := by omega
  have hdonor : u ∈ chargeDonors p ∅ := by
    simp [chargeDonors, hu, hdegree]
  let ctx := donorContext_of_large_card p hp hn ∅ u hdonor
  have h₁ := supported_nearest_triangle_center_eq p hn2 hp ctx huw₁ huq₁ hwq₁ hsupport₁
  have h₂ := supported_nearest_triangle_center_eq p hn2 hp ctx huw₂ huq₂ hwq₂ hsupport₂
  exact hqne (h₁.trans h₂.symm)

end Erdos957
