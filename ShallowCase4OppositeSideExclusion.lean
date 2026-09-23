import ShallowCase4TwoStepReduction

namespace Erdos957

/-- The other local side of a forward anchor also has at most one distinct
active Case-4 center at its two-step supporting edge. Sources at i-1 and
i-2 are forced to use the same edge [i-2,i-1], so endpoint uniqueness
excludes simultaneous activity with distinct retained centers. -/
theorem forward_case4_minus_one_minus_two_sources_impossible
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (i j k : Fin h)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hforward : ∃ (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (availableI : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q)),
      let first := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q availableI
      first.right = v i ∧ first.left = v (i + 1))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjidx : j = i - 1)
    (hkidx : k = (i - 1) - 1)
    (hijcenter :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j))
    (hikcenter :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k))
    (hjkcenter :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k))
    (hjcase : ∃ hjd : v j ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase4 p (v j)
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q)
    (hkcase : ∃ hkd : v k ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase4 p (v k)
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k) hkd).context.q) : False := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  have hforward0 := hforward
  obtain ⟨hid, availableI, hfirstR, hfirstL⟩ := hforward
  let aI := assignments (v i) hid
  let first := selectedSharedFiveCenter p aI.context.q availableI
  obtain ⟨hjd, hjpos, _hjlabels⟩ := hj
  obtain ⟨hjd', hjcase'⟩ := hjcase
  have hjproof : hjd' = hjd := Subsingleton.elim _ _
  subst hjd'
  let aJ := assignments (v j) hjd
  have hqIJ : aI.context.q ≠ aJ.context.q := by
    simpa only [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v i) hid,
      assignedDonorCenter_eq p (tightHullBadVertices p v)
        (hullSupportingHeight p v) assignments (v j) hjd,
      aI, aJ, assignments] using hijcenter
  obtain ⟨availableJ, hJleft, hJright⟩ :=
    forward_case4_minus_one_forces_two_step_pair
      p hp hn v hv hh hrange hsupport i j hjidx first
      (by simpa only [first, aI, assignments] using hfirstR)
      (by simpa only [first, aI, assignments] using hfirstL)
      aJ hjcase' hqIJ
  let secondJ := selectedSharedFiveCenter p aJ.context.q availableJ
  obtain ⟨hkd, hkpos, _hklabels⟩ := hk
  obtain ⟨hkd', hkcase'⟩ := hkcase
  have hkproof : hkd' = hkd := Subsingleton.elim _ _
  subst hkd'
  let aK := assignments (v k) hkd
  have hqIK : aI.context.q ≠ aK.context.q := by
    simpa only [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v i) hid,
      assignedDonorCenter_eq p (tightHullBadVertices p v)
        (hullSupportingHeight p v) assignments (v k) hkd,
      aI, aK, assignments] using hikcenter
  obtain ⟨availableK, hKright, hKleft⟩ :=
    forward_case4_minus_two_forces_two_step_pair
      p hp hn v hv hh hrange hsupport hpos x i hi hforward0 k hkidx
      hkd hkcase' hkpos hikcenter
  let secondK := selectedSharedFiveCenter p aK.context.q availableK
  have hoverlap : secondJ.right = secondK.right := by
    rw [hJright, hKright, hjidx, hkidx]
  have hqJK : aJ.context.q = aK.context.q :=
    sharedFive_centers_eq_of_endpoint_overlap p hp hn secondJ secondK
      (Or.inr (Or.inr (Or.inr hoverlap)))
  apply hjkcenter
  rw [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v j) hjd,
    assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v k) hkd]
  simpa only [aJ, aK, assignments] using hqJK

end Erdos957
