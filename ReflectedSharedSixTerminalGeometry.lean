import SharedSixTerminalGeometry

namespace Erdos957

theorem ReflectedSharedSixPacketChoice.deep_strip_no_diameter_neighbor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (a : Fin n) (c : ℝ) (hc : -1 ≤ c ∧ c ≤ 3)
    (hcoord : edgeCoordinate (p partner) (p (v i)) (p a) =
      (c : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I) :
    ∀ z, (nearestGraph p).Adj a z → z ∉ diameterEndpoints p := by
  classical
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdegreeMap := nearestGraph_degree_eq_of_dist_eq p pR hdist
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
  have hdonorR : v i ∈ chargeDonors pR
      (tightHullBadVertices pR (reversedHullCycle v)) := by
    simp only [chargeDonors, Finset.mem_filter]
    exact ⟨by simpa only [hD] using ctx.endpoint,
      hgoodR, (hdegreeMap (v i)).trans ctx.degree_three⟩
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

  have hcoordR : edgeCoordinate (pR partner) (pR (v i)) (pR a) =
      (c : ℂ) - ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I := by
    dsimp [pR]
    rw [edgeCoordinate_planeReflection, hcoord]
    simp [map_ofNat, sub_eq_add_neg]
  have hno := SharedSixPacketChoice.deep_strip_no_diameter_neighbor
    pR hpR hn (reversedHullCycle v) hvR hh hsupportR hposR (-i)
  rw [show reversedHullCycle v (-i) = v i by exact reversedHullCycle_neg v i] at hno
  specialize hno ctxR partner
  rw [hctxq] at hno
  have ht := hno choice.reflected hrangeR a c hc hcoordR
  intro z hz
  have hzR : (nearestGraph pR).Adj a z := by simpa only [hG] using hz
  simpa only [hD] using ht z hzR

theorem ReflectedSharedSixPacketChoice.terminal_blocked_neighbors
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : ReflectedSharedSixPacketChoice p partner (v i) ctx.q)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (t₂ : Fin n) (hdeg : (nearestGraph p).degree t₂ = 6)
    (houter : (nearestGraph p).Adj choice.reflected.outer t₂)
    (hadj : (nearestGraph p).Adj t₂ choice.packet.right)
    (hcoord₂ : edgeCoordinate (p partner) (p (v i)) (p t₂) =
      (2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I)
    (hcoordx : edgeCoordinate (p partner) (p (v i)) (p choice.packet.right) =
      (5 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I) :
    ∃ z, t₂ ≠ z ∧ (nearestGraph p).Adj choice.packet.right t₂ ∧
      (nearestGraph p).Adj choice.packet.right z ∧
      t₂ ∉ diameterEndpoints p ∧ z ∉ diameterEndpoints p ∧
      ∀ a, (nearestGraph p).Adj z a → a ∉ diameterEndpoints p := by
  have hbx : (nearestGraph p).Adj choice.reflected.outer choice.packet.right := by
    simpa only [choice.packet_sites.1] using choice.original_neighbors.2.2.2.2.2.1
  obtain ⟨z, _, ht₂z, hxz, hsum⟩ := degree_six_triangle_completion
    p (by omega) hp hdeg hadj houter.symm hbx.symm
  have hcoordz : edgeCoordinate (p partner) (p (v i)) (p z) =
      (3 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p partner) (p (v i))
      (p choice.reflected.outer) (p z) (p t₂) (p choice.packet.right) hsum
    rw [choice.original_coordinates.2.1, hcoord₂, hcoordx] at hs
    linear_combination hs
  have hno₂ := choice.deep_strip_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    i ctx partner hrange t₂ 2 (by norm_num) (by simpa using hcoord₂)
  have hnoz := choice.deep_strip_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    i ctx partner hrange z 3 (by norm_num) (by simpa using hcoordz)
  have ht₂D : t₂ ∉ diameterEndpoints p := by
    intro hd
    have ht := nearestGraph_degree_le_three_of_diameterEndpoint p (by omega) hp t₂ hd
    omega
  exact ⟨z, ht₂z.ne, hadj.symm, hxz, ht₂D, hno₂ z ht₂z, hnoz⟩


end Erdos957

