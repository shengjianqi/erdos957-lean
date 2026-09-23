import ShallowCase4ActiveGeometry
import ShallowCase4PartnerFreeNormalForm
import ReflectedSharedSixLowerExclusion

/-! Actual Case-4 sources at the outer `±3` source positions cannot point
farther away from a fixed Case-4 anchor.  If they did, their selected
shared-five supporting edges would be three hull edges apart, while both
retained centers are active at the same receiver; the three-edge separation
estimate rules this out.  Consequently an outer source that survives must be
the inward endpoint of a shared-five pair whose supporting edge is only two
edges away from the anchor edge. -/

namespace Erdos957

/-- A semantic Case-4 retained assignment at hull source `v i` uses the
center-indexed shared-five rule, and the selected pair is one of the two hull
edges incident to `v i`.  This is the Case-4 analogue of the orientation
certificate already available for canonical six-bottom sources, without any
assumption on which receiver is active. -/
theorem CertifiedDonorAssignment.paperCase4_oriented_selected_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    {height : Fin n → ℝ} (i : Fin h)
    (assignment : CertifiedDonorAssignment p (tightHullBadVertices p v) (v i) height)
    (hcase : PaperCase4 p (v i) assignment.context.q) :
    ∃ available : Nonempty (SharedFiveCenterChoice p assignment.context.q),
      let selected := selectedSharedFiveCenter p assignment.context.q available
      ((selected.right = v i ∧ selected.left = v (i + 1)) ∨
       (selected.left = v i ∧ selected.right = v (i - 1))) := by
  classical
  let available := assignment.rule.sharedFive_available_of_paperCase4 hcase
  let selected := selectedSharedFiveCenter p assignment.context.q available
  have hsource : v i = selected.left ∨ v i = selected.right :=
    selected.diameter_neighbor_cases (v i) assignment.context.endpoint
      assignment.context.central_adj.symm
  refine ⟨available, ?_⟩
  rcases hsource with hleft | hright
  · right
    refine ⟨hleft.symm, ?_⟩
    have hrightHull : selected.right ∈ hullVertexIndices p :=
      diameterEndpoints_subset_hullVertexIndices p hp selected.right_diameter
    have hrightNe : selected.right ≠ v i := by
      intro heq
      exact selected.base.ne (hleft.symm.trans heq.symm)
    apply supporting_hull_chord_eq_predecessor p hp v hv hh hrange hsupport
      i selected.right hrightHull hrightNe
    intro k
    simpa only [hleft] using selected.support k
  · left
    refine ⟨hright.symm, ?_⟩
    exact selected.left_eq_cyclic_successor_of_right
      p hp v hv hh hrange hsupport i hright.symm

/-- For a forward-oriented canonical Case-4 anchor on edge `[i,i+1]`, an
active semantic Case-4 source at `i+3` cannot use the outward edge
`[i+3,i+4]`.  Hence it must be the left endpoint of the inward edge
`[i+2,i+3]`. -/
theorem forward_case4_plus_three_forces_inward_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (i : Fin h)
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
    (j : Fin h) (hjidx : j = ((i + 1) + 1) + 1)
    (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
    (hjcase : PaperCase4 p (v j)
      ((supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q)
    (hjpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos)) (v j) x)
    (hcenters :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j)) :
    ∃ availableJ : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q),
      let second := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q availableJ
      second.left = v j ∧ second.right = v (j - 1) := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  obtain ⟨hid, availableI, hfirstR, hfirstL⟩ := hforward
  let aI := assignments (v i) hid
  let aJ := assignments (v j) hjd
  let first := selectedSharedFiveCenter p aI.context.q availableI
  obtain ⟨availableJ, horientJ⟩ :=
    (aJ.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase)
  let second := selectedSharedFiveCenter p aJ.context.q availableJ
  have hgood : v i ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hid).2.1
  have hix : (nearestGraph p).Adj aI.context.q x := by
    obtain ⟨hid', available', _hbottom, hxadj⟩ :=
      hi.receiver_adj_center_and_bottom p v (hullSupportingHeight p v) assignments
    have hh : hid' = hid := Subsingleton.elim _ _
    subst hid'
    simpa only [aI, assignments] using hxadj
  have hjx : x = aJ.context.q ∨ (nearestGraph p).Adj aJ.context.q x := by
    have hjrule : 0 < aJ.packet.weight x := by
      simpa only [localPacketCharge, dite_eq_left hjd, certifiedFamilyPackets,
        CertifiedDonorAssignment.packet, aJ, assignments] using hjpos
    exact aJ.paperCase4_positive_center_or_adj p hjcase x hjrule
  have hqne : aI.context.q ≠ aJ.context.q := by
    simpa only [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v i) hid,
      assignedDonorCenter_eq p (tightHullBadVertices p v)
        (hullSupportingHeight p v) assignments (v j) hjd,
      aI, aJ, assignments] using hcenters
  rcases horientJ with hout | hin
  · exfalso
    have hsecondR : second.right = v (((i + 1) + 1) + 1) := by
      simpa only [second, aJ, assignments, hjidx] using hout.1
    have hsecondL : second.left = v ((((i + 1) + 1) + 1) + 1) := by
      have : j + 1 = (((i + 1) + 1) + 1) + 1 := by rw [hjidx]
      simpa only [second, aJ, assignments, this] using hout.2
    exact sharedFive_centers_forward_three_edges_no_common_active_receiver
      p (by omega) hp v hv hh hpos i hgood first second
      (by simpa only [first, aI, assignments] using hfirstL)
      (by simpa only [first, aI, assignments] using hfirstR)
      hsecondL hsecondR hqne (Or.inr hix) hjx
  · refine ⟨availableJ, ?_⟩
    exact ⟨hin.1, hin.2⟩






/-- A Case-4 source at the forward two-step source position cannot point back
to the edge `[i+1,i+2]`, since that selected pair would overlap the anchor
pair at `i+1` and hence have the same high-degree supported center.  Distinct
centers therefore force the edge `[i+2,i+3]`. -/
theorem forward_case4_plus_two_forces_two_step_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (i j : Fin h) (hjidx : j = (i + 1) + 1)
    {q : Fin n} (first : SharedFiveCenterChoice p q)
    (hfirstR : first.right = v i) (hfirstL : first.left = v (i + 1))
    (assignment : CertifiedDonorAssignment p (tightHullBadVertices p v) (v j)
      (hullSupportingHeight p v (v j)))
    (hjcase : PaperCase4 p (v j) assignment.context.q)
    (hqne : q ≠ assignment.context.q) :
    ∃ availableJ : Nonempty (SharedFiveCenterChoice p assignment.context.q),
      let second := selectedSharedFiveCenter p assignment.context.q availableJ
      second.right = v j ∧ second.left = v (j + 1) := by
  classical
  obtain ⟨availableJ, horientJ⟩ :=
    assignment.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase
  let second := selectedSharedFiveCenter p assignment.context.q availableJ
  rcases horientJ with hforward | hbackward
  · exact ⟨availableJ, hforward.1, hforward.2⟩
  · exfalso
    have hoverlap : first.left = second.right := by
      rw [hfirstL, hbackward.2, hjidx]
      congr 1
      abel
    exact hqne (sharedFive_centers_eq_of_endpoint_overlap p hp hn first second
      (Or.inr (Or.inl hoverlap)))

/-- The analogous backward two-step source normalization: a source at `i-1`
cannot use `[i-1,i]`, because that would overlap the anchor pair at `i`.
Hence it must use `[i-2,i-1]`. -/
theorem forward_case4_minus_one_forces_two_step_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (i j : Fin h) (hjidx : j = i - 1)
    {q : Fin n} (first : SharedFiveCenterChoice p q)
    (hfirstR : first.right = v i) (hfirstL : first.left = v (i + 1))
    (assignment : CertifiedDonorAssignment p (tightHullBadVertices p v) (v j)
      (hullSupportingHeight p v (v j)))
    (hjcase : PaperCase4 p (v j) assignment.context.q)
    (hqne : q ≠ assignment.context.q) :
    ∃ availableJ : Nonempty (SharedFiveCenterChoice p assignment.context.q),
      let second := selectedSharedFiveCenter p assignment.context.q availableJ
      second.left = v j ∧ second.right = v (j - 1) := by
  classical
  obtain ⟨availableJ, horientJ⟩ :=
    assignment.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase
  let second := selectedSharedFiveCenter p assignment.context.q availableJ
  rcases horientJ with hforward | hbackward
  · exfalso
    have hoverlap : first.right = second.left := by
      rw [hfirstR, hforward.2, hjidx]
      congr 1
      abel
    exact hqne (sharedFive_centers_eq_of_endpoint_overlap p hp hn first second
      (Or.inr (Or.inr (Or.inl hoverlap))))
  · exact ⟨availableJ, hbackward.1, hbackward.2⟩


/-- On the backward side of a forward anchor, a Case-4 source at `i-2`
cannot use the farther edge `[i-3,i-2]`; that would put the two selected
shared-five edges three hull steps apart while their centers are simultaneously
active at `x`.  Hence it must use the two-step edge `[i-2,i-1]`. -/
theorem forward_case4_minus_two_forces_two_step_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (i : Fin h)
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
    (j : Fin h) (hjidx : j = (i - 1) - 1)
    (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
    (hjcase : PaperCase4 p (v j)
      ((supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q)
    (hjpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos)) (v j) x)
    (hcenters :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j)) :
    ∃ availableJ : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q),
      let second := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q availableJ
      second.right = v j ∧ second.left = v (j + 1) := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  obtain ⟨hid, availableI, hfirstR, hfirstL⟩ := hforward
  let aI := assignments (v i) hid
  let aJ := assignments (v j) hjd
  let first := selectedSharedFiveCenter p aI.context.q availableI
  obtain ⟨availableJ, horientJ⟩ :=
    (aJ.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase)
  let second := selectedSharedFiveCenter p aJ.context.q availableJ
  have hgood : v i ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hid).2.1
  have hix : (nearestGraph p).Adj aI.context.q x := by
    obtain ⟨hid', available', _hbottom, hxadj⟩ :=
      hi.receiver_adj_center_and_bottom p v (hullSupportingHeight p v) assignments
    have hhud : hid' = hid := Subsingleton.elim _ _
    subst hid'
    simpa only [aI, assignments] using hxadj
  have hjx : x = aJ.context.q ∨ (nearestGraph p).Adj aJ.context.q x := by
    have hjrule : 0 < aJ.packet.weight x := by
      simpa only [localPacketCharge, dite_eq_left hjd, certifiedFamilyPackets,
        CertifiedDonorAssignment.packet, aJ, assignments] using hjpos
    exact aJ.paperCase4_positive_center_or_adj p hjcase x hjrule
  have hqne : aI.context.q ≠ aJ.context.q := by
    simpa only [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v i) hid,
      assignedDonorCenter_eq p (tightHullBadVertices p v)
        (hullSupportingHeight p v) assignments (v j) hjd,
      aI, aJ, assignments] using hcenters
  rcases horientJ with hin | hout
  · exact ⟨availableJ, hin.1, hin.2⟩
  · exfalso
    have hsecondL : second.left = v ((i - 1) - 1) := by
      simpa only [second, aJ, assignments, hjidx] using hout.1
    have hsecondR : second.right = v (((i - 1) - 1) - 1) := by
      have hjm1 : j - 1 = ((i - 1) - 1) - 1 := by rw [hjidx]
      simpa only [second, aJ, assignments, hjm1] using hout.2
    exact sharedFive_centers_backward_three_edges_no_common_active_receiver
      p (by omega) hp v hv hh hpos i hgood first second
      (by simpa only [first, aI, assignments] using hfirstL)
      (by simpa only [first, aI, assignments] using hfirstR)
      hsecondL hsecondR hqne (Or.inr hix) hjx

@[simp] theorem SharedFiveCenterChoice.reflection_swap_left_index
    {n : ℕ} {p : Fin n → Point} {q : Fin n}
    (five : SharedFiveCenterChoice p q) (hp : Function.Injective p) :
    (five.reflection_swap hp).left = five.right := by
  rfl

@[simp] theorem SharedFiveCenterChoice.reflection_swap_right_index
    {n : ℕ} {p : Fin n → Point} {q : Fin n}
    (five : SharedFiveCenterChoice p q) (hp : Function.Injective p) :
    (five.reflection_swap hp).right = five.left := by
  rfl

/-- Backward mirror of `forward_case4_plus_three_forces_inward_pair`, proved
by reflecting the plane and reversing the hull cycle.  Thus a source at
`i-3` must use the inward edge `[i-3,i-2]`, rather than the outward edge
`[i-4,i-3]`. -/
theorem backward_case4_minus_three_forces_inward_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (i : Fin h)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hbackward : ∃ (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (availableI : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q)),
      let first := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q availableI
      first.left = v i ∧ first.right = v (i - 1))
    (j : Fin h) (hjidx : j = ((i - 1) - 1) - 1)
    (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
    (hjcase : PaperCase4 p (v j)
      ((supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q)
    (hjpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos)) (v j) x)
    (hcenters :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j)) :
    ∃ availableJ : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q),
      let second := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q availableJ
      second.right = v j ∧ second.left = v (j + 1) := by
  classical
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  obtain ⟨hid, availableI, hfirstL, hfirstR⟩ := hbackward
  let aI := assignments (v i) hid
  let aJ := assignments (v j) hjd
  let first := selectedSharedFiveCenter p aI.context.q availableI
  obtain ⟨availableJ, horientJ⟩ :=
    (aJ.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase)
  let second := selectedSharedFiveCenter p aJ.context.q availableJ
  have hgood : v i ∉ tightHullBadVertices p v := (Finset.mem_filter.mp hid).2.1
  have hix : (nearestGraph p).Adj aI.context.q x := by
    obtain ⟨hid', available', _hbottom, hxadj⟩ :=
      hi.receiver_adj_center_and_bottom p v (hullSupportingHeight p v) assignments
    have hhud : hid' = hid := Subsingleton.elim _ _
    subst hid'
    simpa only [aI, assignments] using hxadj
  have hjx : x = aJ.context.q ∨ (nearestGraph p).Adj aJ.context.q x := by
    have hjrule : 0 < aJ.packet.weight x := by
      simpa only [localPacketCharge, dite_eq_left hjd, certifiedFamilyPackets,
        CertifiedDonorAssignment.packet, aJ, assignments] using hjpos
    exact aJ.paperCase4_positive_center_or_adj p hjcase x hjrule
  have hqne : aI.context.q ≠ aJ.context.q := by
    simpa only [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v i) hid,
      assignedDonorCenter_eq p (tightHullBadVertices p v)
        (hullSupportingHeight p v) assignments (v j) hjd,
      aI, aJ, assignments] using hcenters
  rcases horientJ with hin | hout
  · exact ⟨availableJ, hin.1, hin.2⟩
  · exfalso
    let pR : Fin n → Point := fun k => planeReflection (p k)
    let vR : Fin h → Fin n := reversedHullCycle v
    have hpR : Function.Injective pR := planeReflection.injective.comp hp
    have hvR : Function.Injective vR := reversedHullCycle_injective v hv
    have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
      planeReflection.dist_map _ _
    have hG := nearestGraph_eq_of_dist_eq p pR hdist
    have hposR : ∀ t, 0 < hullExteriorAngle pR vR t := by
      intro t
      simpa only [pR, vR, hullExteriorAngle_planeReflection_reversed] using hpos (-t)
    let r : Fin h := -i
    have hgoodR : vR r ∉ tightHullBadVertices pR vR := by
      dsimp [r, pR, vR]
      exact tightHull_not_bad_planeReflection_reversed p v hv (-i) (by
        simpa only [neg_neg] using hgood)
    let firstR := first.reflection_swap hp
    let secondR := second.reflection_swap hp
    have hfirstRR : firstR.right = vR r := by
      dsimp [firstR, r, vR]
      simp only [SharedFiveCenterChoice.reflection_swap_right_index,
        reversedHullCycle_neg]
      simpa only [first, aI, assignments] using hfirstL
    have hfirstRL : firstR.left = vR (r + 1) := by
      dsimp [firstR, r, vR]
      simp only [SharedFiveCenterChoice.reflection_swap_left_index,
        reversedHullCycle_neg_successor]
      simpa only [first, aI, assignments] using hfirstR
    have hrj : -j = ((r + 1) + 1) + 1 := by
      dsimp [r]
      rw [hjidx]
      abel
    have hsecondRR : secondR.right = vR (((r + 1) + 1) + 1) := by
      dsimp [secondR, vR]
      simp only [SharedFiveCenterChoice.reflection_swap_right_index]
      rw [← hrj]
      simp only [reversedHullCycle, neg_neg]
      simpa only [second, aJ, assignments] using hout.1
    have hsecondRL : secondR.left = vR ((((r + 1) + 1) + 1) + 1) := by
      dsimp [secondR, vR]
      simp only [SharedFiveCenterChoice.reflection_swap_left_index]
      have hnegpred : -(j - 1) = ((r + 1) + 1) + 1 + 1 := by
        rw [hjidx]
        dsimp [r]
        abel
      rw [← hnegpred]
      simp only [reversedHullCycle, neg_neg]
      simpa only [second, aJ, assignments] using hout.2
    have hixR : (nearestGraph pR).Adj aI.context.q x := by
      rw [hG]
      exact hix
    have hjxR : x = aJ.context.q ∨ (nearestGraph pR).Adj aJ.context.q x := by
      rcases hjx with h | h
      · exact Or.inl h
      · right
        rw [hG]
        exact h
    exact sharedFive_centers_forward_three_edges_no_common_active_receiver
      pR (by omega) hpR vR hvR hh hposR r hgoodR firstR secondR
      hfirstRL hfirstRR hsecondRL hsecondRR hqne (Or.inr hixR) hjxR




/-- For a backward-oriented anchor on `[i-1,i]`, a Case-4 source at `i-2`
cannot use the adjacent edge `[i-2,i-1]`, because the two selected endpoint
pairs would overlap at `i-1` and force equal centers.  It therefore uses the
same two-step edge `[i-3,i-2]` as a surviving source at `i-3`. -/
theorem backward_case4_minus_two_forces_two_step_pair
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (i j : Fin h) (hjidx : j = (i - 1) - 1)
    {q : Fin n} (first : SharedFiveCenterChoice p q)
    (hfirstL : first.left = v i) (hfirstR : first.right = v (i - 1))
    (assignment : CertifiedDonorAssignment p (tightHullBadVertices p v) (v j)
      (hullSupportingHeight p v (v j)))
    (hjcase : PaperCase4 p (v j) assignment.context.q)
    (hqne : q ≠ assignment.context.q) :
    ∃ availableJ : Nonempty (SharedFiveCenterChoice p assignment.context.q),
      let second := selectedSharedFiveCenter p assignment.context.q availableJ
      second.left = v j ∧ second.right = v (j - 1) := by
  classical
  obtain ⟨availableJ, horientJ⟩ :=
    assignment.paperCase4_oriented_selected_pair p hp v hv hh hrange hsupport j hjcase
  let second := selectedSharedFiveCenter p assignment.context.q availableJ
  rcases horientJ with hforward | hbackward
  · exfalso
    have hoverlap : first.right = second.left := by
      rw [hfirstR, hforward.2, hjidx]
      congr 1
      abel
    exact hqne (sharedFive_centers_eq_of_endpoint_overlap p hp hn first second
      (Or.inr (Or.inr (Or.inl hoverlap))))
  · exact ⟨availableJ, hbackward.1, hbackward.2⟩

/-- Backward-orientation analogue of
`forward_case4_same_side_two_case4_sources_impossible`.  The two same-side
source indices `i-3` and `i-2` both normalize to the selected edge
`[i-3,i-2]`; hence they cannot have distinct retained centers. -/
theorem backward_case4_same_side_two_case4_sources_impossible
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
    (hbackward : ∃ (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (availableI : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q)),
      let first := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) hid).context.q availableI
      first.left = v i ∧ first.right = v (i - 1))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjidx : j = ((i - 1) - 1) - 1)
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
  have hbackward0 := hbackward
  obtain ⟨hid, availableI, hfirstL, hfirstR⟩ := hbackward
  let aI := assignments (v i) hid
  let first := selectedSharedFiveCenter p aI.context.q availableI
  obtain ⟨hjd, hjpos, _hjlabels⟩ := hj
  obtain ⟨hjd', hjcase'⟩ := hjcase
  have hjproof : hjd' = hjd := Subsingleton.elim _ _
  subst hjd'
  let aJ := assignments (v j) hjd
  obtain ⟨availableJ, hJright, hJleft⟩ :=
    backward_case4_minus_three_forces_inward_pair
      p hp hn v hv hh hrange hsupport hpos x i hi hbackward0 j hjidx
      hjd hjcase' hjpos hijcenter
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
  obtain ⟨availableK, hKleft, hKright⟩ :=
    backward_case4_minus_two_forces_two_step_pair
      p hp hn v hv hh hrange hsupport i k hkidx first
      (by simpa only [first, aI, assignments] using hfirstL)
      (by simpa only [first, aI, assignments] using hfirstR)
      aK hkcase' hqIK
  let secondK := selectedSharedFiveCenter p aK.context.q availableK
  have hoverlap : secondJ.right = secondK.right := by
    rw [hJright, hKright, hjidx, hkidx] <;> congr 1 <;> abel
  have hqJK : aJ.context.q = aK.context.q :=
    sharedFive_centers_eq_of_endpoint_overlap p hp hn secondJ secondK
      (Or.inr (Or.inr (Or.inr hoverlap)))
  apply hjkcenter
  rw [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v j) hjd,
    assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v k) hkd]
  simpa only [aJ, aK, assignments] using hqJK

/-- For a forward Case-4 anchor, the two same-side source positions `i+2`
and `i+3` cannot both be active semantic Case-4 sources with distinct retained
centers.  Both are forced onto the same selected supporting edge
`[i+2,i+3]`, so endpoint-overlap uniqueness identifies their centers. -/
theorem forward_case4_same_side_two_case4_sources_impossible
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
    (hjidx : j = (i + 1) + 1)
    (hkidx : k = ((i + 1) + 1) + 1)
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
  obtain ⟨availableJ, hJright, hJleft⟩ :=
    forward_case4_plus_two_forces_two_step_pair
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
  obtain ⟨availableK, hKleft, hKright⟩ :=
    forward_case4_plus_three_forces_inward_pair
      p hp hn v hv hh hrange hsupport hpos x i hi hforward0 k hkidx
      hkd hkcase' hkpos hikcenter
  let secondK := selectedSharedFiveCenter p aK.context.q availableK
  have hoverlap : secondJ.right = secondK.right := by
    rw [hJright, hKright, hjidx, hkidx] <;> congr 1 <;> abel
  have hqJK : aJ.context.q = aK.context.q :=
    sharedFive_centers_eq_of_endpoint_overlap p hp hn secondJ secondK
      (Or.inr (Or.inr (Or.inr hoverlap)))
  apply hjkcenter
  rw [assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v j) hjd,
    assignedDonorCenter_eq p (tightHullBadVertices p v)
      (hullSupportingHeight p v) assignments (v k) hkd]
  simpa only [aJ, aK, assignments] using hqJK

/-- Lossless supporting-family wrapper for the forward `+3` reduction.  The
source is assumed actually active at `x`; if its semantic label is Case 4,
then its selected shared-five edge is forced to point inward. -/
theorem forward_plus_three_active_case4_forces_inward
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (i j : Fin h)
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
    (hjidx : j = ((i + 1) + 1) + 1)
    (hcenters :
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j))
    (hjcase : ∃ hjd : v j ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase4 p (v j)
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q) :
    ∃ (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
      (availableJ : Nonempty
        (SharedFiveCenterChoice p
          ((supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q)),
      let second := selectedSharedFiveCenter p
        ((supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) hjd).context.q availableJ
      second.left = v j ∧ second.right = v (j - 1) := by
  classical
  obtain ⟨hjd, hjpos, _hjcases⟩ := hj
  obtain ⟨hjd', hjcase'⟩ := hjcase
  have hproof : hjd' = hjd := Subsingleton.elim _ _
  subst hjd'
  obtain ⟨availableJ, hin⟩ := forward_case4_plus_three_forces_inward_pair
    p hp hn v hv hh hrange hsupport hpos x i hi hforward j hjidx hjd hjcase'
    hjpos hcenters
  exact ⟨hjd, availableJ, hin⟩


end Erdos957
