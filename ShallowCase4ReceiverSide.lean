import ShallowCase4ForeignCenterGeometry

/-! Recover the actual left/right secondary receiver of the surviving
six-bottom Case-4 anchor.  The earlier orientation certificate remembers the
supporting hull edge but intentionally forgets which of the two separated
secondary sites is the current receiver.  The final one-source-per-side
argument needs this last piece of packet geometry. -/

namespace Erdos957

private theorem packet_positive_eq_right_of_left_ne
    {n : ℕ} {p : Fin n → Point} {u x q : Fin n}
    (packet : LocalChargePacket p u)
    (hl : packet.left = q) (hxq : x ≠ q)
    (hx : 0 < packet.weight x) : x = packet.right := by
  by_contra hxr
  simp [LocalChargePacket.weight, hl, hxq, hxr] at hx

/-- A canonical six-bottom indirect Case-4 source reaches the current
receiver at the secondary site belonging to that donor.  Thus a right
endpoint source uses the selected pair's `second.right`, while a left
endpoint source uses `first.right`.  This is the exact left/right receiver
certificate suppressed by `SixBottomSourceOrientation`. -/
theorem SixBottomIndirectSource.oriented_receiver_secondary
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (i : Fin h)
    (hsrc : SixBottomIndirectSource p v height assignments x (v i)) :
    ∃ (hud : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (available : Nonempty
        (SharedFiveCenterChoice p (assignments (v i) hud).context.q)),
      let selected := selectedSharedFiveCenter p
        (assignments (v i) hud).context.q available
      (nearestGraph p).degree selected.selection.bottom = 6 ∧
      (((selected.right = v i ∧ selected.left = v (i + 1)) ∧
          x = selected.selection.second.right) ∨
       ((selected.left = v i ∧ selected.right = v (i - 1)) ∧
          x = selected.selection.first.right)) := by
  classical
  have hsrcCopy := hsrc
  obtain ⟨hud, hx, hnot, available, hsix⟩ := hsrcCopy
  let assignment := assignments (v i) hud
  let selected := selectedSharedFiveCenter p assignment.context.q available
  have hxrule : 0 < assignment.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, assignment] using hx
  have hxcharge : 0 < selected.charge (v i) x := by
    simpa only [assignment.rule.weight_eq_selected_sharedFive available x,
      assignment, selected] using hxrule
  have hxq : x ≠ assignment.context.q := by
    intro heq
    exact hnot (heq ▸ assignment.context.central_adj)
  obtain ⟨hud', available', hsix', horient⟩ :=
    hsrc.oriented_selected_pair p hp v hv hh hrange hsupport
      height assignments x i
  have hhud : hud' = hud := Subsingleton.elim _ _
  subst hud'
  have hav : available' = available := Subsingleton.elim _ _
  subst available'
  refine ⟨hud, available, ?_, ?_⟩
  · simpa only [assignment, selected] using hsix
  rcases horient with hright | hleft
  · left
    refine ⟨by simpa only [assignment, selected] using hright, ?_⟩
    have hsourceR : v i = selected.right := by
      simpa only [assignment, selected] using hright.1.symm
    have hposSecond : 0 < selected.selection.second.weight x := by
      rw [SharedFiveCenterChoice.charge] at hxcharge
      simp [hsourceR, selected.base.ne.symm] at hxcharge
      exact hxcharge
    have hq : selected.selection.second.left = assignment.context.q := by
      simpa only [selected] using selected.selection.second_central
    exact packet_positive_eq_right_of_left_ne selected.selection.second hq hxq hposSecond
  · right
    refine ⟨by simpa only [assignment, selected] using hleft, ?_⟩
    have hsourceL : v i = selected.left := by
      simpa only [assignment, selected] using hleft.1.symm
    have hposFirst : 0 < selected.selection.first.weight x := by
      rw [SharedFiveCenterChoice.charge] at hxcharge
      simp [hsourceL, selected.base.ne] at hxcharge
      exact hxcharge
    have hq : selected.selection.first.left = assignment.context.q := by
      simpa only [selected] using selected.selection.first_central
    exact packet_positive_eq_right_of_left_ne selected.selection.first hq hxq hposFirst

/-- Besides identifying the side, the current Case-4 receiver is adjacent to
both the retained degree-five center and the degree-six deepest bottom. -/
theorem SixBottomIndirectSource.receiver_adj_center_and_bottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n}
    (hsrc : SixBottomIndirectSource p v height assignments x u) :
    ∃ (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
      (available : Nonempty
        (SharedFiveCenterChoice p (assignments u hud).context.q)),
      let selected := selectedSharedFiveCenter p (assignments u hud).context.q available
      (nearestGraph p).Adj selected.selection.bottom x ∧
      (nearestGraph p).Adj (assignments u hud).context.q x := by
  classical
  obtain ⟨hud, hx, hnot, available, hsix⟩ := hsrc
  let assignment := assignments u hud
  let selected := selectedSharedFiveCenter p assignment.context.q available
  have hxrule : 0 < assignment.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, assignment] using hx
  have hxcharge : 0 < selected.charge u x := by
    simpa only [assignment.rule.weight_eq_selected_sharedFive available x,
      assignment, selected] using hxrule
  have hsource : u = selected.left ∨ u = selected.right :=
    selected.diameter_neighbor_cases u assignment.context.endpoint
      assignment.context.central_adj.symm
  have hxq : x ≠ assignment.context.q := by
    intro heq
    exact hnot (heq ▸ assignment.context.central_adj)
  change (nearestGraph p).degree selected.selection.bottom = 6 at hsix
  rcases selected.selection.branch with hlow | hbranch
  · omega
  refine ⟨hud, available, ?_⟩
  rcases hsource with hul | hur
  · have hpos : 0 < selected.selection.first.weight x := by
      rw [SharedFiveCenterChoice.charge] at hxcharge
      simp [hul, selected.base.ne] at hxcharge
      exact hxcharge
    have hq : selected.selection.first.left = assignment.context.q :=
      selected.selection.first_central
    have hxr : x = selected.selection.first.right :=
      packet_positive_eq_right_of_left_ne selected.selection.first hq hxq hpos
    rw [hxr]
    exact ⟨hbranch.2.2.1, selected.selection.first_secondary.1⟩
  · have hpos : 0 < selected.selection.second.weight x := by
      rw [SharedFiveCenterChoice.charge] at hxcharge
      simp [hur, selected.base.ne.symm] at hxcharge
      exact hxcharge
    have hq : selected.selection.second.left = assignment.context.q :=
      selected.selection.second_central
    have hxr : x = selected.selection.second.right :=
      packet_positive_eq_right_of_left_ne selected.selection.second hq hxq hpos
    rw [hxr]
    exact ⟨hbranch.2.2.2.1, selected.selection.second_secondary.1⟩

end Erdos957

namespace Erdos957

/-- The two separated secondary sites in the six-bottom branch are ordered
in the supporting-edge frame.  After identifying the actual donor endpoint,
the current receiver is therefore the donor-side secondary site, with the
other site lying weakly on the opposite horizontal side. -/
theorem SixBottomIndirectSource.oriented_receiver_order
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (i : Fin h)
    (hsrc : SixBottomIndirectSource p v height assignments x (v i)) :
    ∃ (hud : v i ∈ chargeDonors p (tightHullBadVertices p v))
      (available : Nonempty
        (SharedFiveCenterChoice p (assignments (v i) hud).context.q)),
      let selected := selectedSharedFiveCenter p
        (assignments (v i) hud).context.q available
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
            (p selected.selection.second.right)).re)) := by
  classical
  obtain ⟨hud, available, hsix, hside⟩ :=
    hsrc.oriented_receiver_secondary p hp v hv hh hrange hsupport
      height assignments x i
  let assignment := assignments (v i) hud
  let selected := selectedSharedFiveCenter p assignment.context.q available
  change (nearestGraph p).degree selected.selection.bottom = 6 at hsix
  have hbranch :
      (nearestGraph p).degree selected.selection.bottom = 6 ∧
      selected.selection.first.right ≠ selected.selection.second.right ∧
      (nearestGraph p).Adj selected.selection.bottom selected.selection.first.right ∧
      (nearestGraph p).Adj selected.selection.bottom selected.selection.second.right ∧
      (edgeCoordinate (p selected.left) (p selected.right)
        (p selected.selection.first.right)).re ≤
      (edgeCoordinate (p selected.left) (p selected.right)
        (p selected.selection.second.right)).re := by
    rcases selected.selection.branch with hlow | hhigh
    · omega
    · exact hhigh
  refine ⟨hud, available, ?_⟩
  rcases hside with hright | hleft
  · left
    refine ⟨hright.1, hright.2, ?_, ?_⟩
    · exact fun heq => hbranch.2.1 (heq.trans hright.2)
    · simpa only [hright.2] using hbranch.2.2.2.2
  · right
    refine ⟨hleft.1, hleft.2, ?_, ?_⟩
    · exact fun heq => hbranch.2.1 (heq.trans hleft.2).symm
    · simpa only [hleft.2] using hbranch.2.2.2.2

end Erdos957

namespace Erdos957

/-- If the other endpoint of the oriented Case-4 supporting edge is itself an
eligible donor, its retained middle center is forced to be the same center as
the Case-4 anchor.  This is just uniqueness of the supported nearest triangle
at a degree-three diameter donor. -/
theorem SixBottomIndirectSource.partner_assigned_center_eq
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (i t : Fin h)
    (hsrc : SixBottomIndirectSource p v height assignments x (v i))
    (htd : v t ∈ chargeDonors p (tightHullBadVertices p v))
    (ht : t = i + 1 ∨ t = i - 1)
    (hpartner :
      (t = i + 1 ∧
        ∃ hud available,
          let selected := selectedSharedFiveCenter p
            (assignments (v i) hud).context.q available
          selected.right = v i ∧ selected.left = v (i + 1)) ∨
      (t = i - 1 ∧
        ∃ hud available,
          let selected := selectedSharedFiveCenter p
            (assignments (v i) hud).context.q available
          selected.left = v i ∧ selected.right = v (i - 1))) :
    assignedDonorCenter p (tightHullBadVertices p v) height assignments (v t) =
      assignedDonorCenter p (tightHullBadVertices p v) height assignments (v i) := by
  classical
  obtain ⟨hid, _hx, _hnot, availableI, _hsix⟩ := hsrc
  let aI := assignments (v i) hid
  let aT := assignments (v t) htd
  let selected := selectedSharedFiveCenter p aI.context.q availableI
  have hcenterT : assignedDonorCenter p (tightHullBadVertices p v)
      height assignments (v t) = aT.context.q :=
    assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v t) htd
  have hcenterI : assignedDonorCenter p (tightHullBadVertices p v)
      height assignments (v i) = aI.context.q :=
    assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v i) hid
  rcases hpartner with hforward | hbackward
  · rcases hforward with ⟨rfl, hid', available', hright, hleft⟩
    have hhid : hid' = hid := Subsingleton.elim _ _
    subst hid'
    have hav : available' = availableI := Subsingleton.elim _ _
    subst available'
    have htri : aI.context.q = aT.context.q := by
      apply supported_nearest_triangle_center_eq p (by omega) hp aT.context
      · simpa only [selected, aI, hleft, hright] using selected.base
      · simpa only [selected, aI, hleft] using selected.center_left.symm
      · simpa only [selected, aI, hright] using selected.center_right.symm
      · exact Or.inr (by
          intro k
          simpa only [selected, aI, hright, hleft] using selected.support k)
    rw [hcenterT, hcenterI]
    exact htri.symm
  · rcases hbackward with ⟨rfl, hid', available', hleft, hright⟩
    have hhid : hid' = hid := Subsingleton.elim _ _
    subst hid'
    have hav : available' = availableI := Subsingleton.elim _ _
    subst available'
    have htri : aI.context.q = aT.context.q := by
      apply supported_nearest_triangle_center_eq p (by omega) hp aT.context
      · simpa only [selected, aI, hleft, hright] using selected.base.symm
      · simpa only [selected, aI, hright] using selected.center_right.symm
      · simpa only [selected, aI, hleft] using selected.center_left.symm
      · exact Or.inl (by
          intro k
          simpa only [selected, aI, hleft, hright] using selected.support k)
    rw [hcenterT, hcenterI]
    exact htri.symm

end Erdos957
