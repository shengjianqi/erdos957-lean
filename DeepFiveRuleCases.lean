import SharedSixPairCompatibility

/-! Every indirect transfer to a degree-five receiver either lies at exact
distance two or carries an actual nearby diameter partner. This is a uniform
classification of the existing rule constructors, with no sampled geometry. -/

namespace Erdos957

theorem CertifiedDonorRule.indirect_receiver_eq_right {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) (x : Fin n)
    (hx : 0 < rule.packet.weight x) (hnot : ¬ (nearestGraph p).Adj u x) :
    x = rule.packet.right := by
  have hl : x ≠ rule.packet.left := fun h => hnot (h ▸ rule.left_adj)
  by_contra hr
  simp [LocalChargePacket.weight, hl, hr] at hx

/-- Every indirect positive transfer comes from a shared high-degree center. -/
theorem CertifiedDonorRule.center_degree_five_or_six_of_indirect {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) (x : Fin n)
    (hx : 0 < rule.packet.weight x) (hnot : ¬ (nearestGraph p).Adj u x) :
    (nearestGraph p).degree q = 5 ∨ (nearestGraph p).degree q = 6 := by
  cases rule with
  | low choice => exact False.elim (hnot (choice.positive_geometry hx).1)
  | unique choice high => exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available endpoint central =>
      exact Or.inl (selectedSharedFiveCenter p q available).center_degree
  | sharedSix choice => exact Or.inr choice.center_degree
  | reflectedSharedSix choice => exact Or.inr choice.original_neighbors.1

private theorem extension_norm_eq_two (a : ℝ) (ha : a ^ 2 = 3 / 4) :
    ‖(2 : ℂ) - ((2 * a : ℝ) : ℂ) * Complex.I - 1‖ = 2 := by
  let z : ℂ := (2 : ℂ) - ((2 * a : ℝ) : ℂ) * Complex.I - 1
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z
  have hzre : z.re = 1 := by norm_num [z]
  have hzim : z.im = -(2 * a) := by simp [z]
  rw [hzre, hzim] at hsq
  change ‖z‖ = 2
  nlinarith [norm_nonneg z]

/-- A degree-five secondary site is either the first lower site or the
second extension, which is at exactly twice the minimum distance from source. -/
theorem SharedSixPacketChoice.degree_five_right_lower_or_exact_two {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedSixPacketChoice p u w q) (hp : Function.Injective p)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5) :
    choice.packet.right = choice.lower ∨
      dist (p w) (p choice.packet.right) = 2 * pairDist p ij := by
  rcases choice.branch with ⟨_, hl⟩ | ⟨_, t₂, _, _, _, ht₂, hbranch⟩
  · exact Or.inl hl
  rcases hbranch with ⟨_, hx⟩ | ⟨_, _, _, _, hfour⟩
  · right
    have heq := edgeCoordinate_sub_one_norm (p u) (p w) (p choice.packet.right)
      (hp.ne choice.base.ne)
    rw [hx, ht₂, extension_norm_eq_two choice.height choice.height_sq,
      nearestGraph_adj_dist_eq p hmin choice.base] at heq
    have hdelta := pairDist_pos p hp hmin.1
    simpa only [hx] using (div_eq_iff hdelta.ne').mp heq.symm
  · omega

theorem ReflectedSharedSixPacketChoice.degree_five_right_lower_or_exact_two {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w q) (hp : Function.Injective p)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5) :
    choice.packet.right = choice.reflected.lower ∨
      dist (p w) (p choice.packet.right) = 2 * pairDist p ij := by
  let pR := fun k => planeReflection (p k)
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hminR : isMinPair pR ij := by
    simpa only [isMinPair, pairDist, hdist] using hmin
  have hdeg := nearestGraph_degree_eq_of_dist_eq p pR hdist choice.packet.right
  have hdegreeR : (nearestGraph pR).degree choice.reflected.packet.right = 5 := by
    change (nearestGraph pR).degree choice.packet.right = 5
    omega
  have hc := choice.reflected.degree_five_right_lower_or_exact_two
    (planeReflection.injective.comp hp) ij hminR hdegreeR
  simpa only [choice.packet_sites.2, pR, planeReflection.dist_map, pairDist] using hc

/-- The geometric short-distance alternative retains a real second diameter
endpoint and all three edges of the shared triangle. -/
theorem CertifiedDonorRule.indirect_degree_five_exact_or_nearby_partner {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) (hp : Function.Injective p)
    (hn : 2 ≤ n) (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (x : Fin n) (hx : 0 < rule.packet.weight x)
    (hnot : ¬ (nearestGraph p).Adj u x) (hdegree : (nearestGraph p).degree x = 5) :
    dist (p u) (p x) = 2 * pairDist p ij ∨
      ∃ w, w ∈ diameterEndpoints p ∧ w ≠ u ∧ (nearestGraph p).Adj u w ∧
        (nearestGraph p).Adj q w ∧ dist (p w) (p x) ≤ 2 * pairDist p ij := by
  classical
  have hright := rule.indirect_receiver_eq_right x hx hnot
  have path (a b c : Fin n) (hab : (nearestGraph p).Adj a b)
      (hbc : (nearestGraph p).Adj b c) : dist (p a) (p c) ≤ 2 * pairDist p ij := by
    have ht := dist_triangle (p a) (p b) (p c)
    rw [nearestGraph_adj_dist_eq p hmin hab, nearestGraph_adj_dist_eq p hmin hbc] at ht
    linarith
  cases rule with
  | low choice =>
      exact False.elim (hnot (choice.positive_geometry hx).1)
  | unique choice high =>
      exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available endpoint central =>
      right
      let choice := selectedSharedFiveCenter p q available
      change x = (choice.packetFor u endpoint central).right at hright
      rcases choice.diameter_neighbor_cases u endpoint central with hl | hr
      · subst u
        have hxright : x = choice.selection.first.right := by
          simpa [SharedFiveCenterChoice.packetFor] using hright
        refine ⟨choice.right, choice.right_diameter, choice.base.ne.symm, choice.base,
          choice.center_right, ?_⟩
        exact path _ q x choice.center_right.symm (hxright ▸ choice.selection.first_secondary.1)
      · subst u
        have hxright : x = choice.selection.second.right := by
          simpa [SharedFiveCenterChoice.packetFor, choice.base.ne.symm] using hright
        refine ⟨choice.left, choice.left_diameter, choice.base.ne, choice.base.symm,
          choice.center_left, ?_⟩
        exact path _ q x choice.center_left.symm (hxright ▸ choice.selection.second_secondary.1)
  | sharedSix choice =>
      change x = choice.packet.right at hright
      have hd : (nearestGraph p).degree choice.packet.right = 5 := hright ▸ hdegree
      rcases choice.degree_five_right_lower_or_exact_two hp ij hmin hd with hl | he
      · right
        refine ⟨_, choice.partner_diameter, choice.base.ne, choice.base.symm,
          choice.center_adj_partner hn hp, ?_⟩
        exact path _ q x (choice.center_adj_partner hn hp).symm
          ((hright.trans hl) ▸ choice.lower_adj_center)
      · exact Or.inl (hright ▸ he)
  | @reflectedSharedSix w choice =>
      change x = choice.packet.right at hright
      have hd : (nearestGraph p).degree choice.packet.right = 5 := hright ▸ hdegree
      rcases choice.degree_five_right_lower_or_exact_two hp ij hmin hd with hl | he
      · right
        have hG := nearestGraph_eq_of_dist_eq p (fun k => planeReflection (p k))
          (fun a b => planeReflection.dist_map (p a) (p b))
        have hD := diameterEndpoints_eq_of_dist_eq p (fun k => planeReflection (p k))
          (fun a b => planeReflection.dist_map (p a) (p b))
        have hbase : (nearestGraph p).Adj w u := by
          simpa only [hG] using choice.reflected.base
        refine ⟨_, by simpa only [hD] using choice.reflected.partner_diameter,
          hbase.ne, hbase.symm, choice.center_adj_partner hn hp, ?_⟩
        exact path _ q x (choice.center_adj_partner hn hp).symm
          ((hright.trans hl) ▸ choice.original_neighbors.2.2.2.1)
      · exact Or.inl (hright ▸ he)

end Erdos957
