import SupportingFamilyShallowNormalForm
import ActualSharedFiveGroups

/-! A six-bottom Case-4 source already saturates the one-unit noncentral
capacity of its retained shared-five center.  Consequently no distinct active
source can use the same retained center at the same receiver.  This removes
all same-center Case-4 overlap before the remaining left/right analysis. -/

namespace Erdos957

/-- The entire retained-center group of a canonical six-bottom Case-4 source
has noncentral weight at most one at its actual receiver. -/
theorem SixBottomIndirectSource.anchor_center_group_le_one
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n} (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hsrc : SixBottomIndirectSource p v height assignments x u) :
    centerPacketChargeTotal p (tightHullBadVertices p v) height assignments
      (assignments u hud).context.q x ≤ 1 := by
  classical
  obtain ⟨hud', _hx, hnot, available, hsix⟩ := hsrc
  have hproof : hud' = hud := Subsingleton.elim _ _
  subst hud'
  have hxne : x ≠ (assignments u hud).context.q := by
    intro hxq
    apply hnot
    simpa only [hxq] using (assignments u hud).context.central_adj
  exact centerPacketChargeTotal_sharedFive_noncentral_le_one
    p (tightHullBadVertices p v) height assignments
      (assignments u hud).context.q x available hsix hxne

/-- No distinct active donor can have the same retained center as a canonical
six-bottom Case-4 anchor.  The proof uses the exact assembled center group,
so it covers both direct and indirect activity of the second source. -/
theorem SixBottomIndirectSource.active_same_center_eq
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u w : Fin n}
    (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hsrc : SixBottomIndirectSource p v height assignments x u)
    (hwd : w ∈ chargeDonors p (tightHullBadVertices p v))
    (hwpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hcenter : (assignments w hwd).context.q = (assignments u hud).context.q) :
    w = u := by
  classical
  by_contra hwu
  have hcap := hsrc.anchor_center_group_le_one p v height assignments hud
  obtain ⟨hud', hupos, _hnot, _available, _hsix⟩ := hsrc
  have hproof : hud' = hud := Subsingleton.elim _ _
  subst hud'
  let q := (assignments u hud).context.q
  let packets := certifiedFamilyPackets p (tightHullBadVertices p v) height assignments
  change centerPacketChargeTotal p (tightHullBadVertices p v)
    height assignments q x ≤ 1 at hcap
  have huCenter : u ∈ centerChargeSources p (tightHullBadVertices p v)
      height assignments q := by
    apply Finset.mem_filter.mpr
    refine ⟨hud, ?_⟩
    rw [assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments u hud]
  have hwCenter : w ∈ centerChargeSources p (tightHullBadVertices p v)
      height assignments q := by
    apply Finset.mem_filter.mpr
    refine ⟨hwd, ?_⟩
    rw [assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments w hwd]
    exact hcenter
  have hsub : ({u, w} : Finset (Fin n)) ⊆
      centerChargeSources p (tightHullBadVertices p v) height assignments q := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact huCenter
    · exact hwCenter
  have hpairle :
      ∑ a ∈ ({u, w} : Finset (Fin n)),
          localPacketCharge p (tightHullBadVertices p v) packets a x ≤
        centerPacketChargeTotal p (tightHullBadVertices p v) height assignments q x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => Nat.zero_le _)
  have hpair :
      ∑ a ∈ ({u, w} : Finset (Fin n)),
          localPacketCharge p (tightHullBadVertices p v) packets a x =
        localPacketCharge p (tightHullBadVertices p v) packets u x +
          localPacketCharge p (tightHullBadVertices p v) packets w x := by
    simp [Ne.symm hwu]
  have hupos' : 0 < localPacketCharge p (tightHullBadVertices p v) packets u x := by
    simpa only [packets] using hupos
  have hwpos' : 0 < localPacketCharge p (tightHullBadVertices p v) packets w x := by
    simpa only [packets] using hwpos
  rw [hpair] at hpairle
  omega

end Erdos957

namespace Erdos957

/-- Proof-independent version of the same-center exclusion. -/
theorem SixBottomIndirectSource.active_assigned_center_eq_implies_source_eq
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u w : Fin n}
    (hsrc : SixBottomIndirectSource p v height assignments x u)
    (hwd : w ∈ chargeDonors p (tightHullBadVertices p v))
    (hwpos : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hcenter : assignedDonorCenter p (tightHullBadVertices p v) height assignments w =
      assignedDonorCenter p (tightHullBadVertices p v) height assignments u) :
    w = u := by
  have hsrcCopy := hsrc
  obtain ⟨hud, _hupos, _hnot, _available, _hsix⟩ := hsrcCopy
  have hcenter' : (assignments w hwd).context.q = (assignments u hud).context.q := by
    rw [← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments w hwd,
      ← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments u hud]
    exact hcenter
  exact hsrc.active_same_center_eq p v height assignments hud hwd hwpos hcenter'

/-- In the lossless supporting-family normal form, every distinct active
source has a retained center different from the six-bottom Case-4 anchor. -/
theorem supporting_case4_anchor_center_ne_of_distinct_active
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) {i j : Fin h} (hij : i ≠ j)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j) :
    assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) ≠
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v i) := by
  intro hcenter
  obtain ⟨hjd, hjpos, _hjcase⟩ := hj
  have hji : v j = v i :=
    hi.active_assigned_center_eq_implies_source_eq p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) hjd hjpos hcenter
  exact hij (hv hji.symm)

/-- Both non-anchor sources in the final three-source obstruction have centers
strictly different from the Case-4 anchor center. -/
theorem supporting_family_degree_five_overload_triple_has_foreign_centers
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
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
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) ≠
        assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) ∧
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v k) ≠
        assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v i) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, _hiorient, hj, hk, _hjo, _hko⟩ :=
    supporting_family_degree_five_overload_has_lossless_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hdegree hover hdiam
  refine ⟨i, j, k, hij, hik, hjk, hi, hj, hk, ?_, ?_⟩
  · exact supporting_case4_anchor_center_ne_of_distinct_active
      p hp hn v hv hh hrange hsupport hpos x hij hi hj
  · exact supporting_case4_anchor_center_ne_of_distinct_active
      p hp hn v hv hh hrange hsupport hpos x hik hi hk

end Erdos957

namespace Erdos957

/-- If two distinct active sources in the supporting family have the same
retained center, then each source is in a shared-diameter case.  Thus the
UniqueD paper cases (1 and 3) cannot participate in a same-center overlap. -/
theorem activeSupporting_same_center_distinct_forces_sharedD
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) {j k : Fin h} (hjk : j ≠ k)
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hcenter : assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) =
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k)) :
    ∃ hjd : v j ∈ chargeDonors p (tightHullBadVertices p v),
      ∃ hkd : v k ∈ chargeDonors p (tightHullBadVertices p v),
        SharedD p (v j)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q ∧
        SharedD p (v k)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos (v k) hkd).context.q := by
  obtain ⟨hjd, _hjpos, hjcase⟩ := hj
  obtain ⟨hkd, _hkpos, hkcase⟩ := hk
  let aJ := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos (v j) hjd
  let aK := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos (v k) hkd
  have hctx : aJ.context.q = aK.context.q := by
    rw [← assignedDonorCenter_eq p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v j) hjd,
      ← assignedDonorCenter_eq p (tightHullBadVertices p v) (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) (v k) hkd]
    exact hcenter
  have hneq : v j ≠ v k := hv.ne hjk
  have hkD : v k ∈ diameterEndpoints p := (Finset.mem_filter.mp hkd).1
  have hjD : v j ∈ diameterEndpoints p := (Finset.mem_filter.mp hjd).1
  have hJshared : SharedD p (v j) aJ.context.q := by
    rcases hjcase with h1 | h2 | h3 | h4
    · exfalso
      have hkadj : (nearestGraph p).Adj aJ.context.q (v k) := by
        rw [hctx]
        exact aK.context.central_adj.symm
      have heq := h1.2 (v k) hkadj hkD
      exact hneq heq.symm
    · exact h2.2
    · exfalso
      have hkadj : (nearestGraph p).Adj aJ.context.q (v k) := by
        rw [hctx]
        exact aK.context.central_adj.symm
      have heq := h3.1.2 (v k) hkadj hkD
      exact hneq heq.symm
    · exact h4.2
  have hKshared : SharedD p (v k) aK.context.q := by
    rcases hkcase with h1 | h2 | h3 | h4
    · exfalso
      have hjadj : (nearestGraph p).Adj aK.context.q (v j) := by
        rw [← hctx]
        exact aJ.context.central_adj.symm
      have heq := h1.2 (v j) hjadj hjD
      exact hneq heq
    · exact h2.2
    · exfalso
      have hjadj : (nearestGraph p).Adj aK.context.q (v j) := by
        rw [← hctx]
        exact aJ.context.central_adj.symm
      have heq := h3.1.2 (v j) hjadj hjD
      exact hneq heq
    · exact h4.2
  exact ⟨hjd, hkd, by simpa only [aJ] using hJshared, by simpa only [aK] using hKshared⟩

end Erdos957

namespace Erdos957

/-- In an actual degree-five overload, two distinct active sources that share
one retained center must both be direct, and their common positive receiver is
exactly that center.  Hence their shared center has degree five and both
sources are semantic Case 4 (Case 2 is impossible here). -/
theorem supporting_overload_same_center_pair_forces_case4_central_receiver
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
    {j k : Fin h} (hjk : j ≠ k)
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hcenter : assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) =
      assignedDonorCenter p (tightHullBadVertices p v) (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k)) :
    ∃ hjd : v j ∈ chargeDonors p (tightHullBadVertices p v),
      ∃ hkd : v k ∈ chargeDonors p (tightHullBadVertices p v),
        DirectActiveSource p v (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) x (v j) ∧
        DirectActiveSource p v (hullSupportingHeight p v)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos) x (v k) ∧
        x = (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q ∧
        PaperCase4 p (v j)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos (v j) hjd).context.q ∧
        PaperCase4 p (v k)
          (supportingCertifiedDonorRules_of_tight_flat_hull
            p hp hn v hv hh hrange hsupport hpos (v k) hkd).context.q := by
  have hshared := activeSupporting_same_center_distinct_forces_sharedD
    p hp hn v hv hh hrange hsupport hpos x hjk hj hk hcenter
  obtain ⟨hjd, hjpos, _hjcase⟩ := hj
  obtain ⟨hkd, hkpos, _hkcase⟩ := hk
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  let height := hullSupportingHeight p v
  let aJ := assignments (v j) hjd
  let aK := assignments (v k) hkd
  have hctx : aJ.context.q = aK.context.q := by
    rw [← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v j) hjd,
      ← assignedDonorCenter_eq p (tightHullBadVertices p v) height assignments (v k) hkd]
    exact hcenter
  have hneq : v j ≠ v k := hv.ne hjk
  have hjType := active_source_direct_or_sixBottom p hp hn v hv hh hrange hsupport hpos
    height assignments x (v j) hxdeg hover hdiam hjd hjpos
  have hkType := active_source_direct_or_sixBottom p hp hn v hv hh hrange hsupport hpos
    height assignments x (v k) hxdeg hover hdiam hkd hkpos
  have hjDirect : DirectActiveSource p v height assignments x (v j) := by
    rcases hjType with hd | hi
    · exact hd
    · exfalso
      have heq := hi.active_assigned_center_eq_implies_source_eq p v height assignments
        hkd hkpos hcenter.symm
      exact hneq heq.symm
  have hkDirect : DirectActiveSource p v height assignments x (v k) := by
    rcases hkType with hd | hi
    · exact hd
    · exfalso
      have heq := hi.active_assigned_center_eq_implies_source_eq p v height assignments
        hjd hjpos hcenter
      exact hneq heq
  have hjx := hjDirect.choose_spec.2
  have hkx := hkDirect.choose_spec.2
  have hkD : v k ∈ diameterEndpoints p := (Finset.mem_filter.mp hkd).1
  have hqk : (nearestGraph p).Adj aJ.context.q (v k) := by
    rw [hctx]
    exact aK.context.central_adj.symm
  obtain ⟨hjkAdj, hwhere⟩ := tight_flat_shared_central_neighbor_nearest
    p hp hn v hv hh hsupport hpos j aJ.context (v k) hkD hqk hneq.symm
  have hsup : (∀ z, 0 ≤ turn (p (v j)) (p (v k)) (p z)) ∨
      (∀ z, 0 ≤ turn (p (v k)) (p (v j)) (p z)) := by
    rcases hwhere with hnext | hprev
    · left
      intro z
      simpa only [hnext] using hsupport j z
    · right
      intro z
      rw [hprev]
      simpa only [sub_add_cancel] using hsupport (j - 1) z
  have hxcenter : x = aJ.context.q :=
    supported_nearest_triangle_center_eq p (by omega) hp aJ.context
      hjkAdj hjx hkx hsup
  have hdegJ : (nearestGraph p).degree aJ.context.q = 5 := by
    rw [← hxcenter]
    exact hxdeg
  obtain ⟨_hjdS, _hkdS, hjShared, hkShared⟩ := hshared
  have hdegK : (nearestGraph p).degree aK.context.q = 5 := by
    rw [← hctx]
    exact hdegJ
  refine ⟨hjd, hkd, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [height, assignments] using hjDirect
  · simpa only [height, assignments] using hkDirect
  · simpa only [aJ, assignments] using hxcenter
  · exact ⟨by simpa only [aJ, assignments] using hdegJ,
      by simpa only [aJ, assignments] using hjShared⟩
  · exact ⟨by simpa only [aK, assignments] using hdegK,
      by simpa only [aK, assignments] using hkShared⟩

end Erdos957
