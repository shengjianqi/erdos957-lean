import ShallowCase4ReceiverSide

/-! Strongest current normal form for the last shallow obstruction.  It
combines the actual supporting-family overload triple, the pairwise-distinct
retained centers, and the exact Case-4 secondary receiver side. -/

namespace Erdos957

/-- Any actual mixed degree-five overload in the supporting family contains
three distinct local active sources with pairwise distinct retained centers.
The distinguished Case-4 source additionally identifies the current receiver
as its donor-side secondary site and retains the horizontal ordering of the
other secondary site. -/
theorem supporting_family_overload_has_side_resolved_distinct_case4_triple
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ i j k : Fin h,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      SixBottomIndirectSource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x (v i) ∧
      ActiveSupportingPaperFourWaySource
        p hp hn v hv hh hrange hsupport hpos x j ∧
      ActiveSupportingPaperFourWaySource
        p hp hn v hv hh hrange hsupport hpos x k ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) ∧
      (let center := fun t : Fin h =>
        assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v t)
       center i ≠ center j ∧ center i ≠ center k ∧ center j ≠ center k) ∧
      (∃ (hud : v i ∈ chargeDonors p (tightHullBadVertices p v))
        (available : Nonempty
          (SharedFiveCenterChoice p
            ((supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos) (v i) hud).context.q)),
        let selected := selectedSharedFiveCenter p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) hud).context.q available
        (((selected.right = v i ∧ selected.left = v (i + 1)) ∧
            x = selected.selection.second.right ∧
            selected.selection.first.right ≠ x ∧
            (edgeCoordinate (p selected.left) (p selected.right)
              (p selected.selection.first.right)).re ≤
            (edgeCoordinate (p selected.left) (p selected.right) (p x)).re) ∨
         ((selected.left = v i ∧ selected.right = v (i - 1)) ∧
            x = selected.selection.first.right ∧
            selected.selection.second.right ≠ x ∧
            (edgeCoordinate (p selected.left) (p selected.right) (p x)).re ≤
            (edgeCoordinate (p selected.left) (p selected.right)
              (p selected.selection.second.right)).re))) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, _hiorient, hj, hk, hjo, hko⟩ :=
    supporting_family_degree_five_overload_has_lossless_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
  have hcenters := supporting_case4_actual_triple_centers_pairwise_distinct
    p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hjo hko
  have hside := hi.oriented_receiver_order p hp v hv hh hrange hsupport
    (hullSupportingHeight p v)
    (supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos) x i
  exact ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko, hcenters, hside⟩

end Erdos957

namespace Erdos957

/-- In an actual overload triple the other endpoint of the anchor's selected
Case-4 hull edge cannot itself be one of the two additional active sources.
If it were, supported-triangle uniqueness would give the same retained center,
contradicting the already established pairwise center distinction. -/
theorem supporting_case4_anchor_partner_not_additional_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    {i j k : Fin h} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjo : j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1)
    (hko : k = i + 1 ∨ k = i - 1 ∨
      k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
      k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) :
    let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos
    ∃ hud available,
      let selected := selectedSharedFiveCenter p
        (assignments (v i) hud).context.q available
      (((selected.right = v i ∧ selected.left = v (i + 1)) ∧
          j ≠ i + 1 ∧ k ≠ i + 1) ∨
       ((selected.left = v i ∧ selected.right = v (i - 1)) ∧
          j ≠ i - 1 ∧ k ≠ i - 1)) := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  have hcenters := supporting_case4_actual_triple_centers_pairwise_distinct
    p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hjo hko
  dsimp only at hcenters
  obtain ⟨hid, available, _hsix, horient⟩ :=
    hi.oriented_selected_pair p hp v hv hh hrange hsupport
      (hullSupportingHeight p v) assignments x i
  refine ⟨hid, available, ?_⟩
  rcases hj with ⟨hjd, _hjpos, _hjcase⟩
  rcases hk with ⟨hkd, _hkpos, _hkcase⟩
  rcases horient with hforward | hbackward
  · left
    refine ⟨hforward, ?_, ?_⟩
    · intro hji
      have hc := hi.partner_assigned_center_eq p hp hn v hv hh hrange hsupport
        (hullSupportingHeight p v) assignments x i j hjd (Or.inl hji)
        (Or.inl ⟨hji, hid, available, hforward⟩)
      exact hcenters.1 (hc.symm)
    · intro hki
      have hc := hi.partner_assigned_center_eq p hp hn v hv hh hrange hsupport
        (hullSupportingHeight p v) assignments x i k hkd (Or.inl hki)
        (Or.inl ⟨hki, hid, available, hforward⟩)
      exact hcenters.2.1 (hc.symm)
  · right
    refine ⟨hbackward, ?_, ?_⟩
    · intro hji
      have hc := hi.partner_assigned_center_eq p hp hn v hv hh hrange hsupport
        (hullSupportingHeight p v) assignments x i j hjd (Or.inr hji)
        (Or.inr ⟨hji, hid, available, hbackward⟩)
      exact hcenters.1 (hc.symm)
    · intro hki
      have hc := hi.partner_assigned_center_eq p hp hn v hv hh hrange hsupport
        (hullSupportingHeight p v) assignments x i k hkd (Or.inr hki)
        (Or.inr ⟨hki, hid, available, hbackward⟩)
      exact hcenters.2.1 (hc.symm)

end Erdos957
