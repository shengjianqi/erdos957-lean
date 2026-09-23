import ShallowCaseFourOrientation
import SupportingHeightFamily

/-! Specialize the final shallow obstruction to the one charging family that
is actually needed for the existential certificate.  In this family the
unique-five (paper Case 3) rule uses the true outgoing hull supporting height,
so its retained secondary site is the global maximum required by the paper's
left/right overlap argument. -/

namespace Erdos957

/-- A Case-3 source in the concrete supporting-height family carries the
full global supporting-height maximum, not merely a maximum over the donor's
common-neighbor set.  This is the geometric datum used in the published
Case-3/Case-4 overlap analysis. -/
theorem supporting_family_case3_global_maximum
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (hcase3 : PaperCase3 p (v i)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos (v i) hu).context.q) :
    let assignment := supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos (v i) hu
    (nearestGraph p).Adj (v i) assignment.packet.right ∧
      (nearestGraph p).Adj assignment.context.q assignment.packet.right ∧
      ∀ b, (nearestGraph p).Adj assignment.context.q b → b ≠ v i →
        supportingHeight p (v i) (v (i + 1)) b ≤
          supportingHeight p (v i) (v (i + 1)) assignment.packet.right := by
  dsimp [PaperCase3] at hcase3
  exact supportingCertifiedDonorRules_five_global_maximum
    p hp hn v hv hh hrange hsupport hpos i hu hcase3.1 hcase3.2

/-- The final oriented Case-4 triple, specialized to the actual supporting
family.  The point of this wrapper is logical rather than cosmetic: the
remaining side-capacity proof may now use `supporting_family_case3_global_maximum`
for every Case-3 source without carrying an arbitrary score function. -/
theorem supporting_family_degree_five_mixed_overload_has_oriented_case4_triple
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
      SixBottomSourceOrientation p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x i ∧
      PaperFourWaySource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v j) ∧
      PaperFourWaySource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) (v k) ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) := by
  exact degree_five_mixed_overload_has_oriented_case4_paper_triple
    p hp hn v hv hh hrange hsupport hpos
    (hullSupportingHeight p v)
    (supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos)
    x hdegree hover hdiam

end Erdos957

namespace Erdos957

/-- Paper-level source data for the concrete supporting family.  Case 3 is
strengthened by carrying the global highest-neighbor certificate that is
specific to this family. -/
def SupportingPaperFourWaySource
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) : Prop :=
  ∃ hu : v i ∈ chargeDonors p (tightHullBadVertices p v),
    let assignment := supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos (v i) hu
    PaperCase1 p (v i) assignment.context.q ∨
      PaperCase2 p (v i) assignment.context.q ∨
      (PaperCase3 p (v i) assignment.context.q ∧
        (nearestGraph p).Adj (v i) assignment.packet.right ∧
        (nearestGraph p).Adj assignment.context.q assignment.packet.right ∧
        ∀ b, (nearestGraph p).Adj assignment.context.q b → b ≠ v i →
          supportingHeight p (v i) (v (i + 1)) b ≤
            supportingHeight p (v i) (v (i + 1)) assignment.packet.right) ∨
      PaperCase4 p (v i) assignment.context.q

/-- Every semantic four-way source in the concrete family upgrades to
`SupportingPaperFourWaySource`; only the Case-3 branch requires work, and
there the supporting-height family supplies exactly the missing maximum. -/
theorem paperFourWaySource_to_supporting
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h)
    (hsrc : PaperFourWaySource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) (v i)) :
    SupportingPaperFourWaySource p hp hn v hv hh hrange hsupport hpos i := by
  rcases hsrc with ⟨hu, h1 | h2 | h3 | h4⟩
  · exact ⟨hu, Or.inl h1⟩
  · exact ⟨hu, Or.inr (Or.inl h2)⟩
  · have hmax := supporting_family_case3_global_maximum
      p hp hn v hv hh hrange hsupport hpos i hu h3
    exact ⟨hu, Or.inr (Or.inr (Or.inl ⟨h3, hmax⟩))⟩
  · exact ⟨hu, Or.inr (Or.inr (Or.inr h4))⟩

/-- Strongest current overload normal form for the family that will actually
be used in the final certificate: an oriented six-bottom Case-4 anchor and two
nearby sources whose Case-3 branches already carry the global maximum. -/
theorem supporting_family_degree_five_overload_has_enriched_case4_triple
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
      SixBottomSourceOrientation p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x i ∧
      SupportingPaperFourWaySource p hp hn v hv hh hrange hsupport hpos j ∧
      SupportingPaperFourWaySource p hp hn v hv hh hrange hsupport hpos k ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hiorient, hj, hk, hjo, hko⟩ :=
    supporting_family_degree_five_mixed_overload_has_oriented_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hdegree hover hdiam
  exact ⟨i, j, k, hij, hik, hjk, hi, hiorient,
    paperFourWaySource_to_supporting p hp hn v hv hh hrange hsupport hpos j hj,
    paperFourWaySource_to_supporting p hp hn v hv hh hrange hsupport hpos k hk,
    hjo, hko⟩

end Erdos957

namespace Erdos957

/-- Lossless paper-level source data for the concrete supporting family.
Unlike `PaperFourWaySource`, this predicate retains that the source actually
contributes positive weight to the current receiver.  Case 3 additionally
carries the global supporting-height maximum. -/
def ActiveSupportingPaperFourWaySource
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (i : Fin h) : Prop :=
  ∃ hu : v i ∈ chargeDonors p (tightHullBadVertices p v),
    0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v)
        (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos)) (v i) x ∧
    let assignment := supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos (v i) hu
    PaperCase1 p (v i) assignment.context.q ∨
      PaperCase2 p (v i) assignment.context.q ∨
      (PaperCase3 p (v i) assignment.context.q ∧
        (nearestGraph p).Adj (v i) assignment.packet.right ∧
        (nearestGraph p).Adj assignment.context.q assignment.packet.right ∧
        ∀ b, (nearestGraph p).Adj assignment.context.q b → b ≠ v i →
          supportingHeight p (v i) (v (i + 1)) b ≤
            supportingHeight p (v i) (v (i + 1)) assignment.packet.right) ∨
      PaperCase4 p (v i) assignment.context.q

/-- A positive direct source at a degree-five receiver upgrades to the
lossless supporting-family paper classification. -/
theorem directActiveSource_to_activeSupportingPaper
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (i : Fin h)
    (hsrc : DirectActiveSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i)) :
    ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x i := by
  obtain ⟨hu, hx, hadj⟩ := hsrc
  let assignment := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos (v i) hu
  have hxrule : 0 < assignment.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hu, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, assignment] using hx
  have hcases := assignment.direct_degree_five_paper_four_way p x hxrule hadj hxdeg
  refine ⟨hu, hx, ?_⟩
  rcases hcases with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · have hmax := supporting_family_case3_global_maximum
      p hp hn v hv hh hrange hsupport hpos i hu h3
    exact Or.inr (Or.inr (Or.inl ⟨h3, hmax⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

/-- A canonical six-bottom indirect source is an active Case-4 source in the
lossless supporting-family classification. -/
theorem sixBottomSource_to_activeSupportingPaper
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (i : Fin h)
    (hsrc : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i)) :
    ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x i := by
  obtain ⟨hu', hcase4⟩ := hsrc.paperCase4 p v (hullSupportingHeight p v)
    (supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos)
  obtain ⟨hu, hx, _hnot, _available, _hsix⟩ := hsrc
  have hhu : hu' = hu := Subsingleton.elim _ _
  subst hu'
  exact ⟨hu, hx, Or.inr (Or.inr (Or.inr hcase4))⟩

/-- The coarse active dichotomy upgrades losslessly in the concrete family. -/
theorem direct_or_sixBottom_to_activeSupportingPaper
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (i : Fin h)
    (hsrc : DirectActiveSource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x (v i) ∨
      SixBottomIndirectSource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x (v i)) :
    ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x i := by
  rcases hsrc with hd | hi
  · exact directActiveSource_to_activeSupportingPaper
      p hp hn v hv hh hrange hsupport hpos x hxdeg i hd
  · exact sixBottomSource_to_activeSupportingPaper
      p hp hn v hv hh hrange hsupport hpos x i hi

/-- Lossless final overload normal form.  All three sources are known to be
actually active at `x`; the anchor is oriented Case 4, and each of the other
two has a paper case label with the Case-3 global maximum already attached. -/
theorem supporting_family_degree_five_overload_has_lossless_case4_triple
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
      SixBottomSourceOrientation p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x i ∧
      ActiveSupportingPaperFourWaySource
        p hp hn v hv hh hrange hsupport hpos x j ∧
      ActiveSupportingPaperFourWaySource
        p hp hn v hv hh hrange hsupport hpos x k ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko⟩ :=
    degree_five_mixed_overload_has_typed_offset_triple
      p hp hn v hv hh hrange hsupport hpos
      (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos)
      x hdegree hover hdiam
  exact ⟨i, j, k, hij, hik, hjk, hi,
    hi.has_orientation p hp v hv hh hrange hsupport
      (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x i,
    direct_or_sixBottom_to_activeSupportingPaper
      p hp hn v hv hh hrange hsupport hpos x hdegree j hj,
    direct_or_sixBottom_to_activeSupportingPaper
      p hp hn v hv hh hrange hsupport hpos x hdegree k hk,
    hjo, hko⟩

end Erdos957

namespace Erdos957

/-- The single remaining local mathematical obligation for degree-five mixed
receivers in the concrete supporting family.  It states that the lossless
oriented Case-4 three-source obstruction produced above cannot occur. -/
def SupportingCase4TripleExclusion : Prop :=
  ∀ {n h : ℕ} [NeZero h]
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
    (i j k : Fin h),
    i ≠ j → i ≠ k → j ≠ k →
    SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i) →
    SixBottomSourceOrientation p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x i →
    ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j →
    ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k →
    (j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) →
    (k = i + 1 ∨ k = i - 1 ∨
      k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
      k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) → False

/-- Once the single local Case-4 triple obstruction is excluded, every
mixed degree-five receiver in the concrete supporting family satisfies its
full two-unit capacity. -/
theorem supporting_family_degree_five_mixed_capacity_of_triple_exclusion
    (hexcl : SupportingCase4TripleExclusion)
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
      2 * (6 - (nearestGraph p).degree x) := by
  by_contra hnot
  have hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x := by omega
  obtain ⟨i, j, k, hij, hik, hjk, hi, hiorient, hj, hk, hjo, hko⟩ :=
    supporting_family_degree_five_overload_has_lossless_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
  exact hexcl p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
    i j k hij hik hjk hi hiorient hj hk hjo hko

end Erdos957
