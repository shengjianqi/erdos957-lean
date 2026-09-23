import ShallowCase4SideNormalForm

/-! Remove the already impossible endpoint-partner offset from the final
Case-4 shallow overload normal form.  This is the finite index form needed
before the last one-source-per-side argument: a forward anchor edge `[i,i+1]`
forbids `i+1` as either extra source, while a backward anchor edge `[i-1,i]`
forbids `i-1`. -/

namespace Erdos957

/-- Local offsets around a forward-oriented Case-4 anchor after removing the
other endpoint of the anchor edge itself. -/
def ForwardCase4ResidualOffset {h : ℕ} [NeZero h] (i t : Fin h) : Prop :=
  t = i - 1 ∨
  t = (i + 1) + 1 ∨ t = (i - 1) - 1 ∨
  t = ((i + 1) + 1) + 1 ∨ t = ((i - 1) - 1) - 1

/-- Local offsets around a backward-oriented Case-4 anchor after removing the
other endpoint of the anchor edge itself. -/
def BackwardCase4ResidualOffset {h : ℕ} [NeZero h] (i t : Fin h) : Prop :=
  t = i + 1 ∨
  t = (i + 1) + 1 ∨ t = (i - 1) - 1 ∨
  t = ((i + 1) + 1) + 1 ∨ t = ((i - 1) - 1) - 1

 theorem forward_residual_offset_of_local_ne_partner
    {h : ℕ} [NeZero h] {i t : Fin h}
    (hloc : t = i + 1 ∨ t = i - 1 ∨
      t = (i + 1) + 1 ∨ t = (i - 1) - 1 ∨
      t = ((i + 1) + 1) + 1 ∨ t = ((i - 1) - 1) - 1)
    (hne : t ≠ i + 1) : ForwardCase4ResidualOffset i t := by
  rcases hloc with hp1 | hm1 | hp2 | hm2 | hp3 | hm3
  · exact False.elim (hne hp1)
  · exact Or.inl hm1
  · exact Or.inr (Or.inl hp2)
  · exact Or.inr (Or.inr (Or.inl hm2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hp3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hm3)))

 theorem backward_residual_offset_of_local_ne_partner
    {h : ℕ} [NeZero h] {i t : Fin h}
    (hloc : t = i + 1 ∨ t = i - 1 ∨
      t = (i + 1) + 1 ∨ t = (i - 1) - 1 ∨
      t = ((i + 1) + 1) + 1 ∨ t = ((i - 1) - 1) - 1)
    (hne : t ≠ i - 1) : BackwardCase4ResidualOffset i t := by
  rcases hloc with hp1 | hm1 | hp2 | hm2 | hp3 | hm3
  · exact Or.inl hp1
  · exact False.elim (hne hm1)
  · exact Or.inr (Or.inl hp2)
  · exact Or.inr (Or.inr (Or.inl hm2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hp3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hm3)))

/-- Strongest finite-index normal form currently available for an actual
supporting-family mixed degree-five overload.  Besides the exact Case-4
secondary receiver geometry and pairwise distinct retained centers, the two
additional source indices have had the anchor-edge partner removed from their
six-position locality lists. -/
theorem supporting_family_overload_has_partner_free_case4_triple
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
      (let center := fun t : Fin h =>
        assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v t)
       center i ≠ center j ∧ center i ≠ center k ∧ center j ≠ center k) ∧
      ((ForwardCase4ResidualOffset i j ∧ ForwardCase4ResidualOffset i k) ∨
       (BackwardCase4ResidualOffset i j ∧ BackwardCase4ResidualOffset i k)) ∧
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
  classical
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko, hcenters, hside⟩ :=
    supporting_family_overload_has_side_resolved_distinct_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
  obtain ⟨hud, available, hpartner⟩ :=
    supporting_case4_anchor_partner_not_additional_source
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hjo hko
  refine ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hcenters, ?_, hside⟩
  rcases hpartner with hforward | hbackward
  · left
    exact ⟨forward_residual_offset_of_local_ne_partner hjo hforward.2.1,
      forward_residual_offset_of_local_ne_partner hko hforward.2.2⟩
  · right
    exact ⟨backward_residual_offset_of_local_ne_partner hjo hbackward.2.1,
      backward_residual_offset_of_local_ne_partner hko hbackward.2.2⟩

end Erdos957
