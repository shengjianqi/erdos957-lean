import SharedSixLowerExclusion
import SharedSixPairCompatibility

/-! Reflection transports the complete retained shared-five certificate and
the actual supporting hull. Consequently the selected first lower site of a
reflected shared-six rule cannot equal any shared-five bottom. -/

namespace Erdos957

private noncomputable def reflected_selection_preserving_bottom {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedFivePairSelection p u w q) (hne : p u ≠ p w) :
    {other : SharedFivePairSelection (fun k => planeReflection (p k)) w u q //
      other.bottom = choice.bottom} := by
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hexists : ∃ original : SharedFivePairSelection
      (fun k => planeReflection (pR k)) u w q, original.bottom = choice.bottom := by
    have hdouble : (fun k => planeReflection (pR k)) = p := by
      funext k
      simp [pR, planeReflection_planeReflection]
    rw [hdouble]
    exact ⟨choice, rfl⟩
  let original := Classical.choose hexists
  have hbottom := Classical.choose_spec hexists
  have hneR : pR w ≠ pR u := (planeReflection.injective.ne hne).symm
  exact ⟨original.of_reflection_swap pR hneR, hbottom⟩

/-- Reflect a complete shared-five center certificate, exchanging the two
endpoint roles and preserving the retained bottom index. -/
noncomputable def SharedFiveCenterChoice.reflection_swap {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (five : SharedFiveCenterChoice p q)
    (hp : Function.Injective p) :
    SharedFiveCenterChoice (fun k => planeReflection (p k)) q := by
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdegree := nearestGraph_degree_eq_of_dist_eq p pR hdist q
  refine {
    left := five.right
    right := five.left
    left_diameter := by rw [hD]; exact five.right_diameter
    right_diameter := by rw [hD]; exact five.left_diameter
    center_left := by rw [hG]; exact five.center_right
    center_right := by rw [hG]; exact five.center_left
    base := by rw [hG]; exact five.base.symm
    center_degree := hdegree.trans five.center_degree
    support := ?_
    selection := (reflected_selection_preserving_bottom five.selection (hp.ne five.base.ne)).val
  }
  intro k
  rw [turn_planeReflection, turn_reverse, neg_neg]
  exact five.support k

@[simp] theorem SharedFiveCenterChoice.reflection_swap_bottom {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (five : SharedFiveCenterChoice p q)
    (hp : Function.Injective p) :
    (five.reflection_swap hp).selection.bottom = five.selection.bottom := by
  exact (reflected_selection_preserving_bottom five.selection (hp.ne five.base.ne)).property

/-- The actual reflected rule has the same mixed lower-site exclusion as
the forward rule. Its frame alignment follows from the reflected hull. -/
theorem tight_flat_reflectedSharedSix_selected_lower_ne_sharedFive_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n)
    (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hselected : choice.packet.right = choice.reflected.lower)
    (five : SharedFiveCenterChoice p qfive) :
    five.selection.bottom ≠ choice.reflected.lower := by
  classical
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdegree := nearestGraph_degree_eq_of_dist_eq p pR hdist (v i)
  have hvR := reversedHullCycle_injective v hv
  have hrangeR : Set.range (reversedHullCycle v) =
      (hullVertexIndices pR : Set (Fin n)) := reflectedHull_range p v hrange
  have hsupportR : ∀ a k, 0 ≤ turn (pR (reversedHullCycle v a))
      (pR (reversedHullCycle v (a + 1))) (pR k) := reflectedHull_support p v hsupport
  have hposR : ∀ a, 0 < hullExteriorAngle pR (reversedHullCycle v) a := by
    intro a
    simpa only [pR, hullExteriorAngle_planeReflection_reversed] using hpos (-a)
  have hgoodR : v i ∉ tightHullBadVertices pR (reversedHullCycle v) := by
    have ht := tightHull_not_bad_planeReflection_reversed p v hv (-i)
      (by simpa only [neg_neg] using ctx.outside_bad)
    simpa only [reversedHullCycle_neg] using ht
  have hdonorR : v i ∈ chargeDonors pR (tightHullBadVertices pR (reversedHullCycle v)) := by
    simp only [chargeDonors, Finset.mem_filter]
    exact ⟨by simpa only [hD] using ctx.endpoint,
      hgoodR, hdegree.trans ctx.degree_three⟩
  let ctxR := donorContext_of_large_card pR hpR hn
    (tightHullBadVertices pR (reversedHullCycle v)) (v i) hdonorR
  have hpartnerD : partner ∈ diameterEndpoints p := by
    simpa only [pR, hD] using choice.reflected.partner_diameter
  have hqpartner := choice.center_adj_partner (by omega : 2 ≤ n) hp
  have hbase : (nearestGraph p).Adj partner (v i) := by
    simpa only [pR, hG] using choice.reflected.base
  have hwhere := (tight_flat_shared_central_neighbor_nearest p hp hn v hv hh
    hsupport hpos i ctx partner hpartnerD hqpartner hbase.ne).2
  have hctxq : ctxR.q = ctx.q := by
    apply (supported_nearest_triangle_center_eq pR (by omega) hpR ctxR
      (by simpa only [hG] using hbase.symm)
      (by simpa only [hG] using ctx.central_adj)
      (by simpa only [hG] using hqpartner.symm) ?_).symm
    rcases hwhere with hnext | hprev
    · right
      intro k
      dsimp [pR]
      rw [turn_planeReflection, turn_reverse, neg_neg, hnext]
      exact hsupport i k
    · left
      intro k
      dsimp [pR]
      rw [turn_planeReflection, turn_reverse, neg_neg, hprev]
      simpa only [sub_add_cancel] using hsupport (i - 1) k
  have hexclude := tight_flat_sharedSix_selected_lower_ne_sharedFive_bottom pR hpR hn
    (reversedHullCycle v) hvR hh hrangeR hsupportR hposR (-i)
  rw [show reversedHullCycle v (-i) = v i by
    exact reversedHullCycle_neg v i] at hexclude
  specialize hexclude ctxR
  rw [hctxq] at hexclude
  have h := hexclude partner qfive choice.reflected hselected (five.reflection_swap hp)
  simpa only [SharedFiveCenterChoice.reflection_swap_bottom] using h

end Erdos957
