import ShallowDegreeFiveOverload
import DirectChargeCapacity

/-! A degree-five overload cannot be made entirely from direct sources.  Hence
it necessarily exposes one of the already rigid indirect shared-five
six-bottom configurations.  This is the entry point for the final shallow
source-overlap analysis. -/

namespace Erdos957

/-- Every degree-five overload contains a positive source that is not a
nearest neighbor of the receiver.  The proof uses the actual simultaneous
source set: at most two eligible diameter endpoints can be adjacent to one
receiver, whereas an overload needs at least three positive donors. -/
theorem certified_family_degree_five_overload_has_indirect_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x) :
    ∃ u, u ∈ chargeDonors p (tightHullBadVertices p v) ∧
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
      ¬ (nearestGraph p).Adj u x := by
  classical
  let bad := tightHullBadVertices p v
  let packets := certifiedFamilyPackets p bad height assignments
  let A := (chargeDonors p bad).filter (fun u =>
    0 < localPacketCharge p bad packets u x)
  have hA3 : 3 ≤ A.card := by
    simpa only [bad, packets] using
      certified_family_degree_five_overload_active_card_ge_three
        p bad height assignments x hdegree hover
  by_contra hnone
  push Not at hnone
  have hsub : A ⊆ directChargeSources p bad x := by
    intro u huA
    obtain ⟨hud, hupos⟩ := Finset.mem_filter.mp huA
    exact Finset.mem_filter.mpr ⟨hud, hnone u hud hupos⟩
  have hcard : A.card ≤ 2 := by
    exact (Finset.card_le_card hsub).trans
      (tight_flat_direct_sources_card_le_two p hp hn v hv hh hrange hsupport hpos x)
  omega

/-- Consequently every mixed degree-five overload contains an actual
shared-five indirect source whose selected deepest bottom has degree six.
This is the formal Case-4 obstruction that all remaining shallow analysis
may anchor at. -/
theorem certified_family_degree_five_mixed_overload_has_six_bottom_source
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ (u : Fin n) (hud : u ∈ chargeDonors p (tightHullBadVertices p v)),
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
      ¬ (nearestGraph p).Adj u x ∧
      ∃ available : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q),
        (nearestGraph p).degree
          (selectedSharedFiveCenter p (assignments u hud).context.q available).selection.bottom = 6 := by
  obtain ⟨u, hud, hx, hnot⟩ :=
    certified_family_degree_five_overload_has_indirect_source
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover
  refine ⟨u, hud, hx, hnot, ?_⟩
  exact certified_family_degree_five_mixed_overload_indirect_forces_six_bottom
    p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
      u hud hx hnot


/-- A mixed degree-five overload contains a three-source obstruction anchored
at an indirect six-bottom shared-five source.  All three sources are actual
hull vertices and every ordered pair is confined by the seven-position source
locality theorem.  Thus the remaining obstruction is genuinely finite and
cyclic-local, rather than a global receiver sum. -/
theorem certified_family_degree_five_mixed_overload_has_pairwise_local_triple
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ i j k : Fin h,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v i) x ∧
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v j) x ∧
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v k) x ∧
      v j ∈ chargeDonors p (tightHullBadVertices p v) ∧
      v k ∈ chargeDonors p (tightHullBadVertices p v) ∧
      ¬ (nearestGraph p).Adj (v i) x ∧
      (∃ hui : v i ∈ chargeDonors p (tightHullBadVertices p v),
        ∃ available : Nonempty (SharedFiveCenterChoice p (assignments (v i) hui).context.q),
          (nearestGraph p).degree
            (selectedSharedFiveCenter p (assignments (v i) hui).context.q available).selection.bottom = 6) ∧
      v j ∈ hullSourceNeighborhood v i ∧
      v k ∈ hullSourceNeighborhood v i ∧
      v i ∈ hullSourceNeighborhood v j ∧
      v k ∈ hullSourceNeighborhood v j ∧
      v i ∈ hullSourceNeighborhood v k ∧
      v j ∈ hullSourceNeighborhood v k := by
  classical
  let bad := tightHullBadVertices p v
  let packets := certifiedFamilyPackets p bad height assignments
  let A := (chargeDonors p bad).filter (fun u =>
    0 < localPacketCharge p bad packets u x)
  obtain ⟨u, hud, hux, hunot, available, hsix⟩ :=
    certified_family_degree_five_mixed_overload_has_six_bottom_source
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  have huA : u ∈ A := by
    exact Finset.mem_filter.mpr ⟨hud, by simpa only [bad, packets] using hux⟩
  have hA3 : 3 ≤ A.card := by
    simpa only [bad, packets] using
      certified_family_degree_five_overload_active_card_ge_three
        p bad height assignments x hdegree hover
  have hsingle : ({u} : Finset (Fin n)).card < A.card := by
    simp
    omega
  obtain ⟨w, hwA, hwu⟩ := Finset.exists_mem_notMem_of_card_lt_card hsingle
  have hwu' : w ≠ u := by simpa using hwu
  have hpaircard : ({u, w} : Finset (Fin n)).card = 2 := by simp [hwu'.symm]
  have hpairlt : ({u, w} : Finset (Fin n)).card < A.card := by
    rw [hpaircard]
    omega
  obtain ⟨z, hzA, hzuw⟩ := Finset.exists_mem_notMem_of_card_lt_card hpairlt
  have hzu : z ≠ u ∧ z ≠ w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hzuw
  obtain ⟨hwd, hwx⟩ := Finset.mem_filter.mp hwA
  obtain ⟨hzd, hzx⟩ := Finset.mem_filter.mp hzA
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hud).1
  have hwD : w ∈ diameterEndpoints p := (Finset.mem_filter.mp hwd).1
  have hzD : z ∈ diameterEndpoints p := (Finset.mem_filter.mp hzd).1
  have hurange : u ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp huD
  have hwrange : w ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp hwD
  have hzrange : z ∈ Set.range v := by
    rw [hrange]
    exact diameterEndpoints_subset_hullVertexIndices p hp hzD
  obtain ⟨i, rfl⟩ := hurange
  obtain ⟨j, rfl⟩ := hwrange
  obtain ⟨k, rfl⟩ := hzrange
  have hi_ne_j : i ≠ j := fun hij => hwu' (congrArg v hij).symm
  have hi_ne_k : i ≠ k := fun hik => hzu.1 (congrArg v hik).symm
  have hj_ne_k : j ≠ k := fun hjk => hzu.2 (congrArg v hjk).symm
  have hix : 0 < localPacketCharge p bad packets (v i) x := by
    simpa only [bad, packets] using hux
  have hjx : 0 < localPacketCharge p bad packets (v j) x := by
    simpa only [bad, packets] using hwx
  have hkx : 0 < localPacketCharge p bad packets (v k) x := by
    simpa only [bad, packets] using hzx
  refine ⟨i, j, k, hi_ne_j, hi_ne_k, hj_ne_k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [bad, packets] using hix
  · simpa only [bad, packets] using hjx
  · simpa only [bad, packets] using hkx
  · simpa only [bad] using hwd
  · simpa only [bad] using hzd
  · simpa using hunot
  · refine ⟨?_, ?_⟩
    · simpa only [bad] using hud
    · exact ⟨available, hsix⟩
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments i (v j) x (by simpa only [bad, packets] using hix)
        (by simpa only [bad, packets] using hjx)
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments i (v k) x (by simpa only [bad, packets] using hix)
        (by simpa only [bad, packets] using hkx)
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments j (v i) x (by simpa only [bad, packets] using hjx)
        (by simpa only [bad, packets] using hix)
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments j (v k) x (by simpa only [bad, packets] using hjx)
        (by simpa only [bad, packets] using hkx)
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments k (v i) x (by simpa only [bad, packets] using hkx)
        (by simpa only [bad, packets] using hix)
  · exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
      height assignments k (v j) x (by simpa only [bad, packets] using hkx)
        (by simpa only [bad, packets] using hjx)


end Erdos957
