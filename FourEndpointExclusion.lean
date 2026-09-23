import FourEndpointPacking

/-! Structural exclusion by saturation of the whole nearby endpoint set. -/

namespace Erdos957

/-- A distinct active source cannot be either endpoint of the selected pair
of a six-bottom source. This includes every rule of the actual family. -/
theorem SixBottomIndirectSource.active_not_selected_endpoint
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u z : Fin n} (hu : SixBottomIndirectSource p v height assignments x u)
    (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (av : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q))
    (hzd : z ∈ chargeDonors p (tightHullBadVertices p v))
    (hzpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) z x)
    (hzu : z ≠ u) :
    z ≠ (selectedSharedFiveCenter p (assignments u hud).context.q av).left ∧
    z ≠ (selectedSharedFiveCenter p (assignments u hud).context.q av).right := by
  let choice := selectedSharedFiveCenter p (assignments u hud).context.q av
  have hforeign : (assignments z hzd).context.q ≠ (assignments u hud).context.q := by
    intro heq
    exact hzu (hu.active_same_center_eq p v height assignments hud hzd hzpos heq)
  constructor
  · intro hzl
    change z = choice.left at hzl
    have heq := supported_nearest_triangle_center_eq p hn hp (assignments z hzd).context
      (by simpa only [← hzl] using choice.base)
      (by simpa only [← hzl] using choice.center_left.symm)
      choice.center_right.symm
      (Or.inr (by simpa only [← hzl] using choice.support))
    exact hforeign heq.symm
  · intro hzr
    change z = choice.right at hzr
    have heq := supported_nearest_triangle_center_eq p hn hp (assignments z hzd).context
      (by simpa only [← hzr] using choice.base.symm)
      (by simpa only [← hzr] using choice.center_right.symm)
      choice.center_left.symm
      (Or.inl (by simpa only [← hzr] using choice.support))
    exact hforeign heq.symm

/-- Two distinct actual six-bottom sources exhaust the four possible nearby
diameter endpoints. A third distinct active source would be a fifth endpoint.
There are no source-position or orientation premises. -/
theorem two_six_bottom_sources_no_third_active
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x w z : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hw : SixBottomIndirectSource p v height assignments x w)
    (hwi : w ≠ v i) (hzi : z ≠ v i) (hzw : z ≠ w)
    (hzd : z ∈ chargeDonors p (tightHullBadVertices p v))
    (hzpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) z x) : False := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  have hcap := hi.nearby_diameter_card_le_four p hp hn v hv hh hrange hsupport hpos
    height assignments ij hmin
  have hiCopy := hi
  have hwCopy := hw
  obtain ⟨hid, _hipos, _hinot, avI, _hbI⟩ := hiCopy
  obtain ⟨hwd, hwpos, _hwnot, avW, _hbW⟩ := hwCopy
  let first := selectedSharedFiveCenter p (assignments (v i) hid).context.q avI
  let second := selectedSharedFiveCenter p (assignments w hwd).context.q avW
  have hqne : (assignments (v i) hid).context.q ≠ (assignments w hwd).context.q := by
    intro heq
    exact hwi (hi.active_same_center_eq p v height assignments hid hwd hwpos heq.symm)
  have hdisjoint : first.left ≠ second.left ∧ first.left ≠ second.right ∧
      first.right ≠ second.left ∧ first.right ≠ second.right := by
    have ht : ¬ (first.left = second.left ∨ first.left = second.right ∨
        first.right = second.left ∨ first.right = second.right) := by
      intro hov
      exact hqne (sharedFive_centers_eq_of_endpoint_overlap p hp hn first second hov)
    tauto
  obtain ⟨hzIL, hzIR⟩ := hi.active_not_selected_endpoint p (by omega) hp v
    height assignments hid avI hzd hzpos hzi
  obtain ⟨hzWL, hzWR⟩ := hw.active_not_selected_endpoint p (by omega) hp v
    height assignments hwd avW hzd hzpos hzw
  obtain ⟨hid', _avI, _hbxI, hqxI⟩ := hi.receiver_adj_center_and_bottom p v height assignments
  have hproofI : hid' = hid := Subsingleton.elim _ _
  subst hid'
  obtain ⟨hwd', _avW, _hbxW, hqxW⟩ := hw.receiver_adj_center_and_bottom p v height assignments
  have hproofW : hwd' = hwd := Subsingleton.elim _ _
  subst hwd'
  let S := (diameterEndpoints p).filter fun a => dist (p a) (p x) ≤ 2 * pairDist p ij
  have hmem {q : Fin n} (ch : SharedFiveCenterChoice p q)
      (hqx : (nearestGraph p).Adj q x) : ch.left ∈ S ∧ ch.right ∈ S := by
    have hnear {a : Fin n} (hadj : (nearestGraph p).Adj q a) :
        dist (p a) (p x) ≤ 2 * pairDist p ij := by
      have ht := dist_triangle (p a) (p q) (p x)
      rw [nearestGraph_adj_dist_eq p hmin hadj.symm,
        nearestGraph_adj_dist_eq p hmin hqx] at ht
      linarith
    exact ⟨Finset.mem_filter.mpr ⟨ch.left_diameter, hnear ch.center_left⟩,
      Finset.mem_filter.mpr ⟨ch.right_diameter, hnear ch.center_right⟩⟩
  have hI := hmem first hqxI
  have hW := hmem second hqxW
  have hzmem : z ∈ S := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzd).1,
    localPacketCharge_pos_dist_le_two_min p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) hmin hzpos⟩
  have hsub : ({first.left, first.right, second.left, second.right, z} : Finset (Fin n)) ⊆ S := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hI.1
    · exact hI.2
    · exact hW.1
    · exact hW.2
    · exact hzmem
  have hcard : ({first.left, first.right, second.left, second.right, z} : Finset (Fin n)).card = 5 := by
    simp [first.base.ne, second.base.ne, hdisjoint.1, hdisjoint.2.1,
      hdisjoint.2.2.1, hdisjoint.2.2.2, hzIL.symm, hzIR.symm, hzWL.symm, hzWR.symm,
      first, second]
  have hle := Finset.card_le_card hsub
  change S.card ≤ 4 at hcap
  rw [hcard] at hle
  omega

/-- The previously open three-source obstruction is impossible. The final
exclusion counts all nearby endpoints, independent of the source offsets. -/
theorem supporting_case4_triple_exclusion : SupportingCase4TripleExclusion := by
  intro n h _ p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
    _i _j _k _hij _hik _hjk _hi _horient _hj _hk _hjo _hko
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    supporting_family_overload_has_two_indirect_sources
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
  obtain ⟨hkd, hkpos, _hkcase⟩ := hk
  exact two_six_bottom_sources_no_third_active p hp hn v hv hh hrange hsupport hpos
    (hullSupportingHeight p v)
    (supportingCertifiedDonorRules_of_tight_flat_hull p hp hn v hv hh hrange hsupport hpos)
    hi hj (hv.ne hij.symm) (hv.ne hik.symm) (hv.ne hjk.symm) hkd hkpos

/-- Unconditional total capacity for every degree-five receiver adjacent to
a diameter endpoint in the actual supporting family. All donor rules enter
the sum, with no unproved local-exclusion parameter. -/
theorem supporting_family_degree_five_mixed_capacity
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v)
          (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos)) w x ≤
      2 * (6 - (nearestGraph p).degree x) :=
  supporting_family_degree_five_mixed_capacity_of_triple_exclusion
    supporting_case4_triple_exclusion p hp hn v hv hh hrange hsupport hpos x hxdeg hdiam

end Erdos957
