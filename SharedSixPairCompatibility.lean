import IndirectChargeUnitBound
import FlatUnitCircleSources
import CenterChargeGroups
import SharedCenterUniqueness

/-! Distinct diameter sources of one shared-six center cannot send their
indirect units to the same receiver. Reversing the common endpoint pair
reverses the horizontal direction of every possible secondary site. -/

namespace Erdos957

theorem SharedSixPacketChoice.center_adj_partner {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedSixPacketChoice p u w q) (hn : 2 ≤ n)
    (hp : Function.Injective p) : (nearestGraph p).Adj q u := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hne := hp.ne choice.base.ne
  have hn2 := Complex.normSq_eq_norm_sq (edgeCoordinate (p u) (p w) (p q))
  rw [choice.center_coordinate, Complex.normSq_apply] at hn2
  have hs := choice.height_sq
  have hnorm : ‖edgeCoordinate (p u) (p w) (p q)‖ = 1 := by
    have hnonneg := norm_nonneg (edgeCoordinate (p u) (p w) (p q))
    rw [choice.center_coordinate] at hnonneg ⊢
    simp at hn2
    nlinarith
  rw [edgeCoordinate_norm _ _ _ hne] at hnorm
  have hdist : dist (p u) (p q) = dist (p u) (p w) := by
    exact (div_eq_one_iff_eq (dist_ne_zero.mpr hne)).mp hnorm
  apply (nearestGraph_adj_iff_dist_eq p hp hmin q u).mpr
  rw [dist_comm, hdist, nearestGraph_adj_dist_eq p hmin choice.base]

theorem SharedSixPacketChoice.right_re_ge_one {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedSixPacketChoice p u w q) :
    1 ≤ (edgeCoordinate (p u) (p w) (p choice.packet.right)).re := by
  rcases choice.right_coordinate_cases with hc | hc | hc <;> rw [hc] <;> norm_num

theorem ReflectedSharedSixPacketChoice.center_adj_partner {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w q) (hn : 2 ≤ n)
    (hp : Function.Injective p) : (nearestGraph p).Adj q u := by
  have hG := nearestGraph_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))
  simpa only [hG] using choice.reflected.center_adj_partner hn
    (planeReflection.injective.comp hp)

theorem ReflectedSharedSixPacketChoice.right_re_ge_one {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w q) :
    1 ≤ (edgeCoordinate (p u) (p w) (p choice.packet.right)).re := by
  simpa only [choice.packet_sites.2, edgeCoordinate_planeReflection,
    Complex.conj_re] using choice.reflected.right_re_ge_one

/-- Every indirect positive transfer from a degree-six center retains a
second diameter neighbor behind the source in the receiver's direction. -/
theorem CertifiedDonorRule.six_indirect_partner {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) (hn : 2 ≤ n)
    (hp : Function.Injective p) (hq : (nearestGraph p).degree q = 6)
    (x : Fin n) (hx : 0 < rule.packet.weight x)
    (hnot : ¬ (nearestGraph p).Adj u x) :
    ∃ w, w ∈ diameterEndpoints p ∧ (nearestGraph p).Adj q w ∧
      (nearestGraph p).Adj w u ∧ 1 ≤ (edgeCoordinate (p w) (p u) (p x)).re := by
  have hxright : x = rule.packet.right := by
    have hxleft : x ≠ rule.packet.left := fun heq => hnot (heq ▸ rule.left_adj)
    by_contra hxright
    simp [LocalChargePacket.weight, hxleft, hxright] at hx
  cases rule with
  | low choice => have hl := choice.central_degree; omega
  | unique choice high => exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available endpoint central =>
      have hf := (selectedSharedFiveCenter p q available).center_degree
      omega
  | @sharedSix w choice =>
      refine ⟨w, choice.partner_diameter, choice.center_adj_partner hn hp,
        choice.base, ?_⟩
      simpa only [CertifiedDonorRule.packet, hxright] using choice.right_re_ge_one
  | @reflectedSharedSix w choice =>
      have hG := nearestGraph_eq_of_dist_eq p (fun i => planeReflection (p i))
        (fun i j => planeReflection.dist_map (p i) (p j))
      have hD := diameterEndpoints_eq_of_dist_eq p (fun i => planeReflection (p i))
        (fun i j => planeReflection.dist_map (p i) (p j))
      refine ⟨w, ?_, choice.center_adj_partner hn hp, ?_, ?_⟩
      · simpa only [hD] using choice.reflected.partner_diameter
      · simpa only [hG] using choice.reflected.base
      · simpa only [CertifiedDonorRule.packet, hxright] using choice.right_re_ge_one

/-- The two possible diameter neighbors of a shared-six center cannot
both send an indirect positive unit to one receiver, with either orientation. -/
theorem certified_six_indirect_sources_eq_of_card_le_two {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q x : Fin n} {heightU heightW : Fin n → ℝ}
    (ruleU : CertifiedDonorRule p u q heightU)
    (ruleW : CertifiedDonorRule p w q heightW)
    (hq : (nearestGraph p).degree q = 6)
    (hcard : ((diameterEndpoints p).filter (fun a => (nearestGraph p).Adj q a)).card ≤ 2)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (hxU : 0 < ruleU.packet.weight x) (hxW : 0 < ruleW.packet.weight x)
    (hnotU : ¬ (nearestGraph p).Adj u x) (hnotW : ¬ (nearestGraph p).Adj w x) :
    u = w := by
  classical
  by_contra hne
  obtain ⟨a, haD, hqa, hau, hax⟩ := ruleU.six_indirect_partner hn hp hq x hxU hnotU
  obtain ⟨b, hbD, hqb, hbw, hbx⟩ := ruleW.six_indirect_partner hn hp hq x hxW hnotW
  have hcases (c : Fin n) (hcD : c ∈ diameterEndpoints p)
      (hqc : (nearestGraph p).Adj q c) : c = u ∨ c = w := by
    by_contra hc
    have hcu : c ≠ u := fun h => hc (Or.inl h)
    have hcw : c ≠ w := fun h => hc (Or.inr h)
    have hsub : ({u, w, c} : Finset (Fin n)) ⊆
        (diameterEndpoints p).filter (fun a => (nearestGraph p).Adj q a) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> exact Finset.mem_filter.mpr ⟨‹_›, ‹_›⟩
    have hthree : ({u, w, c} : Finset (Fin n)).card = 3 := by
      simp [hne, hcu.symm, hcw.symm]
    have hbound := Finset.card_le_card hsub
    omega
  have ha : a = w := (hcases a haD hqa).resolve_left hau.ne
  have hb : b = u := (hcases b hbD hqb).resolve_right hbw.ne
  rw [ha] at hax
  rw [hb] at hbx
  rw [edgeCoordinate_swap_base _ _ _ (hp.ne hne)] at hax
  simp only [Complex.sub_re, Complex.one_re] at hax
  linarith

/-- Actual tight-flat geometry supplies the at-most-two-neighbor premise. -/
theorem tight_flat_certified_six_indirect_sources_eq {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    {w x : Fin n} {heightU heightW : Fin n → ℝ}
    (ruleU : CertifiedDonorRule p (v i) ctx.q heightU)
    (ruleW : CertifiedDonorRule p w ctx.q heightW)
    (hq : (nearestGraph p).degree ctx.q = 6)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj ctx.q w)
    (hxU : 0 < ruleU.packet.weight x) (hxW : 0 < ruleW.packet.weight x)
    (hnotU : ¬ (nearestGraph p).Adj (v i) x) (hnotW : ¬ (nearestGraph p).Adj w x) :
    v i = w := by
  apply certified_six_indirect_sources_eq_of_card_le_two p (by omega) hp
    ruleU ruleW hq
    (tight_flat_diameter_neighbors_card_le_two p hp hn v hv hh hsupport hpos i
      ctx.outside_bad ctx.endpoint ctx.q ctx.central_adj)
    ctx.endpoint hw ctx.central_adj.symm hqw hxU hxW hnotU hnotW

/-- An eligible partner of an actual shared central edge has the same
retained center, even if its context was chosen independently. -/
theorem tight_flat_shared_partner_context_center_eq {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    {w : Fin n} {badW : Finset (Fin n)} (ctxW : DonorContext p badW w)
    (hqw : (nearestGraph p).Adj ctx.q w) (hne : w ≠ v i) :
    ctxW.q = ctx.q := by
  obtain ⟨huw, hwhere⟩ := tight_flat_shared_central_neighbor_nearest
    p hp hn v hv hh hsupport hpos i ctx w ctxW.endpoint hqw hne
  apply (supported_nearest_triangle_center_eq p (by omega) hp ctxW
    huw.symm hqw.symm ctx.central_adj ?_).symm
  rcases hwhere with hnext | hprev
  · right
    rw [hnext]
    exact hsupport i
  · left
    rw [hprev]
    simpa only [sub_add_cancel] using hsupport (i - 1)

end Erdos957
