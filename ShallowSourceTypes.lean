import ShallowCaseFourObstruction

/-! Canonical source types for the final degree-five shallow obstruction.
Under an overload, every positive indirect donor is exactly a degree-five
shared-five source whose selected bottom has degree six. -/

namespace Erdos957

/-- The only indirect source type that can survive inside a mixed degree-five
overload.  The donor proof is retained because the selected center belongs to
the actual assembled assignment. -/
def SixBottomIndirectSource {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x u : Fin n) : Prop :=
  ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
    0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
    ¬ (nearestGraph p).Adj u x ∧
    ∃ available : Nonempty (SharedFiveCenterChoice p (assignments u hud).context.q),
      (nearestGraph p).degree
        (selectedSharedFiveCenter p (assignments u hud).context.q available).selection.bottom = 6

/-- In the mixed degree-five overload regime, positive indirect contribution
is equivalent to the canonical six-bottom source predicate. -/
theorem sixBottomIndirectSource_iff_active_not_adj_of_degree_five_overload
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
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    (u : Fin n) :
    SixBottomIndirectSource p v height assignments x u ↔
      (u ∈ chargeDonors p (tightHullBadVertices p v) ∧
        0 < localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
        ¬ (nearestGraph p).Adj u x) := by
  constructor
  · rintro ⟨hud, hx, hnot, _available, _hsix⟩
    exact ⟨hud, hx, hnot⟩
  · rintro ⟨hud, hx, hnot⟩
    refine ⟨hud, hx, hnot, ?_⟩
    exact certified_family_degree_five_mixed_overload_indirect_forces_six_bottom
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
        u hud hx hnot

/-- Every mixed degree-five overload has at least one canonical six-bottom
indirect source. -/
theorem exists_sixBottomIndirectSource_of_degree_five_overload
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
    ∃ u, SixBottomIndirectSource p v height assignments x u := by
  obtain ⟨u, hud, hx, hnot, available, hsix⟩ :=
    certified_family_degree_five_mixed_overload_has_six_bottom_source
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  exact ⟨u, hud, hx, hnot, available, hsix⟩

end Erdos957

namespace Erdos957

/-- A positive source whose transfer to `x` is direct. -/
def DirectActiveSource {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x u : Fin n) : Prop :=
  ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
    0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ∧
    (nearestGraph p).Adj u x

/-- In the mixed degree-five overload regime every positive source has exactly
one of the two source types relevant to the final obstruction: direct, or a
six-bottom indirect source. -/
theorem active_source_direct_or_sixBottom
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x u : Fin n) (hdegree : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hux : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x) :
    DirectActiveSource p v height assignments x u ∨
      SixBottomIndirectSource p v height assignments x u := by
  by_cases hadj : (nearestGraph p).Adj u x
  · exact Or.inl ⟨hud, hux, hadj⟩
  · exact Or.inr ((sixBottomIndirectSource_iff_active_not_adj_of_degree_five_overload
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam u).2
        ⟨hud, hux, hadj⟩)

/-- The three-source obstruction can be typed without reopening the five
`CertifiedDonorAssignment` constructors: one source is a canonical six-bottom
anchor, and each of the other two is either direct or six-bottom indirect. -/
theorem degree_five_mixed_overload_has_typed_local_triple
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
      SixBottomIndirectSource p v height assignments x (v i) ∧
      (DirectActiveSource p v height assignments x (v j) ∨
        SixBottomIndirectSource p v height assignments x (v j)) ∧
      (DirectActiveSource p v height assignments x (v k) ∨
        SixBottomIndirectSource p v height assignments x (v k)) ∧
      v j ∈ hullSourceNeighborhood v i ∧
      v k ∈ hullSourceNeighborhood v i ∧
      v i ∈ hullSourceNeighborhood v j ∧
      v k ∈ hullSourceNeighborhood v j ∧
      v i ∈ hullSourceNeighborhood v k ∧
      v j ∈ hullSourceNeighborhood v k := by
  obtain ⟨i, j, k, hij, hik, hjk, hiPos, hjPos, hkPos, hjDonor, hkDonor, hiIndirect,
      ⟨hiDonor, available, hbottom6⟩, hji, hki, hijLoc, hkj, hikLoc, hjkLoc⟩ :=
    certified_family_degree_five_mixed_overload_has_pairwise_local_triple
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  have hiSix : SixBottomIndirectSource p v height assignments x (v i) :=
    ⟨hiDonor, hiPos, hiIndirect, available, hbottom6⟩
  refine ⟨i, j, k, hij, hik, hjk, hiSix, ?_, ?_, hji, hki, hijLoc, hkj, hikLoc, hjkLoc⟩
  · exact active_source_direct_or_sixBottom p hp hn v hv hh hrange hsupport hpos
      height assignments x (v j) hdegree hover hdiam hjDonor hjPos
  · exact active_source_direct_or_sixBottom p hp hn v hv hh hrange hsupport hpos
      height assignments x (v k) hdegree hover hdiam hkDonor hkPos

end Erdos957
