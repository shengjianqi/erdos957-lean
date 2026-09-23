import ShallowTripleNormalForm

/-! Refine the coarse direct/indirect normal form by recovering the four
published charging cases from the retained donor center.  This is the right
level for the final shallow overlap analysis: the paper's last argument is
case-sensitive, while the previous `DirectActiveSource` predicate deliberately
forgot that information. -/

namespace Erdos957

/-- Semantic versions of the four published charging cases, expressed only
through the retained central neighbor.  They do not depend on how the packet
was constructed syntactically. -/
def PaperCase1 {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  (nearestGraph p).degree q = 6 ∧ UniqueD p u q

def PaperCase2 {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  (nearestGraph p).degree q = 6 ∧ SharedD p u q

def PaperCase3 {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  (nearestGraph p).degree q = 5 ∧ UniqueD p u q

def PaperCase4 {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  (nearestGraph p).degree q = 5 ∧ SharedD p u q

/-- Every positive direct transfer to a degree-five receiver belongs to one
of the four semantic paper cases.  The low-center branch of `DonorFiveWay`
is impossible: whichever certified constructor was retained, a center of
degree at most four cannot produce a positive transfer to a degree-five
receiver. -/
theorem CertifiedDonorAssignment.direct_degree_five_paper_four_way
    {n : ℕ} (p : Fin n → Point) {bad : Finset (Fin n)}
    {u : Fin n} {height : Fin n → ℝ}
    (assignment : CertifiedDonorAssignment p bad u height)
    (x : Fin n) (hx : 0 < assignment.packet.weight x)
    (_hadj : (nearestGraph p).Adj u x)
    (hxdeg : (nearestGraph p).degree x = 5) :
    PaperCase1 p u assignment.context.q ∨
      PaperCase2 p u assignment.context.q ∨
      PaperCase3 p u assignment.context.q ∨
      PaperCase4 p u assignment.context.q := by
  have hfiveway := donorFiveWay_of_degree_le_six p u assignment.context.q
    assignment.context.central_degree_le_six
  have hnotlow : ¬ (nearestGraph p).degree assignment.context.q ≤ 4 := by
    intro hlow
    cases hrule : assignment.rule with
    | low choice =>
        have hx' : 0 < choice.packet.weight x := by
          simpa only [CertifiedDonorAssignment.packet, hrule, CertifiedDonorRule.packet] using hx
        have := (choice.positive_geometry hx').2.2
        omega
    | unique choice high => omega
    | sharedFive available endpoint central =>
        have hd := (selectedSharedFiveCenter p assignment.context.q available).center_degree
        omega
    | sharedSix choice =>
        have hd := choice.center_degree
        omega
    | reflectedSharedSix choice =>
        have hd := choice.original_neighbors.1
        omega
  unfold DonorFiveWay at hfiveway
  rcases hfiveway with hlow | hcase3 | hcase1 | hcase4 | hcase2
  · exact False.elim (hnotlow hlow)
  · exact Or.inr (Or.inr (Or.inl hcase3))
  · exact Or.inl hcase1
  · exact Or.inr (Or.inr (Or.inr hcase4))
  · exact Or.inr (Or.inl hcase2)


/-- The canonical six-bottom indirect source is semantically a published
Case-4 source: its retained center has degree five and has another diameter
endpoint among its nearest neighbors. -/
theorem SixBottomIndirectSource.paperCase4
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n}
    (hsrc : SixBottomIndirectSource p v height assignments x u) :
    ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase4 p u (assignments u hud).context.q := by
  classical
  obtain ⟨hud, _hx, _hnot, available, _hbottom⟩ := hsrc
  let aU := assignments u hud
  let selected := selectedSharedFiveCenter p aU.context.q available
  have hcase : u = selected.left ∨ u = selected.right :=
    selected.diameter_neighbor_cases u aU.context.endpoint aU.context.central_adj.symm
  refine ⟨hud, selected.center_degree, ?_⟩
  rcases hcase with hul | hur
  · refine ⟨selected.right, ?_, selected.center_right, selected.right_diameter⟩
    exact fun h => selected.base.ne (hul.symm.trans h.symm)
  · refine ⟨selected.left, ?_, selected.center_left, selected.left_diameter⟩
    exact fun h => selected.base.ne (h.trans hur)

/-- Lift the four-way semantic classification from one retained assignment to
the assembled-family `DirectActiveSource` predicate. -/
theorem DirectActiveSource.paper_four_way_of_degree_five
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n} (hxdeg : (nearestGraph p).degree x = 5)
    (hsrc : DirectActiveSource p v height assignments x u) :
    ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase1 p u (assignments u hud).context.q ∨
      PaperCase2 p u (assignments u hud).context.q ∨
      PaperCase3 p u (assignments u hud).context.q ∨
      PaperCase4 p u (assignments u hud).context.q := by
  obtain ⟨hud, hx, hadj⟩ := hsrc
  have hxrule : 0 < (assignments u hud).packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  exact ⟨hud, (assignments u hud).direct_degree_five_paper_four_way
    p x hxrule hadj hxdeg⟩


/-- A source type that retains the published four-way direct classification,
while keeping the already rigid six-bottom indirect branch explicit. -/
def PaperTypedSource {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x u : Fin n) : Prop :=
  (∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
      PaperCase1 p u (assignments u hud).context.q ∨
      PaperCase2 p u (assignments u hud).context.q ∨
      PaperCase3 p u (assignments u hud).context.q ∨
      PaperCase4 p u (assignments u hud).context.q) ∨
    SixBottomIndirectSource p v height assignments x u

/-- The coarse direct/six-bottom dichotomy refines to the paper-level type
at a degree-five receiver. -/
theorem direct_or_sixBottom_to_paperTypedSource
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n} (hxdeg : (nearestGraph p).degree x = 5)
    (hsrc : DirectActiveSource p v height assignments x u ∨
      SixBottomIndirectSource p v height assignments x u) :
    PaperTypedSource p v height assignments x u := by
  rcases hsrc with hdirect | hindirect
  · exact Or.inl (hdirect.paper_four_way_of_degree_five p v height assignments hxdeg)
  · exact Or.inr hindirect

/-- Final paper-level normal form for the two non-anchor sources.  A
hypothetical mixed degree-five overload has a canonical Case-4 six-bottom
anchor; each other source is either an indirect Case-4 source or one of the
four direct paper cases. -/
theorem degree_five_mixed_overload_has_paper_case_triple
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
      PaperTypedSource p v height assignments x (v j) ∧
      PaperTypedSource p v height assignments x (v k) ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) ∧
      (∃ hud : v i ∈ chargeDonors p (tightHullBadVertices p v),
        PaperCase4 p (v i) (assignments (v i) hud).context.q) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko⟩ :=
    degree_five_mixed_overload_has_typed_offset_triple
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  exact ⟨i, j, k, hij, hik, hjk, hi,
    direct_or_sixBottom_to_paperTypedSource p v height assignments hdegree hj,
    direct_or_sixBottom_to_paperTypedSource p v height assignments hdegree hk,
    hjo, hko, hi.paperCase4 p v height assignments⟩

/-- Forget whether a positive source reached the receiver directly or indirectly,
and retain only the semantic published charging case of its retained center. -/
def PaperFourWaySource {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (u : Fin n) : Prop :=
  ∃ hud : u ∈ chargeDonors p (tightHullBadVertices p v),
    PaperCase1 p u (assignments u hud).context.q ∨
    PaperCase2 p u (assignments u hud).context.q ∨
    PaperCase3 p u (assignments u hud).context.q ∨
    PaperCase4 p u (assignments u hud).context.q

/-- At a degree-five receiver every paper-typed positive source has one of the
four semantic published case labels.  In the indirect branch the label is
necessarily Case 4. -/
theorem PaperTypedSource.paper_four_way
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x u : Fin n}
    (hsrc : PaperTypedSource p v height assignments x u) :
    PaperFourWaySource p v height assignments u := by
  rcases hsrc with hdirect | hindirect
  · exact hdirect
  · obtain ⟨hud, hcase4⟩ := hindirect.paperCase4 p v height assignments
    exact ⟨hud, Or.inr (Or.inr (Or.inr hcase4))⟩

/-- Strongest current shallow normal form.  Every hypothetical mixed
degree-five overload has a distinguished six-bottom Case-4 anchor, and the
other two distinct local sources each carry one of the four published case
labels.  Both lie within three hull steps of the anchor. -/
theorem degree_five_mixed_overload_has_case4_anchored_paper_triple
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
      PaperFourWaySource p v height assignments (v j) ∧
      PaperFourWaySource p v height assignments (v k) ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) ∧
      (∃ hud : v i ∈ chargeDonors p (tightHullBadVertices p v),
        PaperCase4 p (v i) (assignments (v i) hud).context.q) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko, hicase4⟩ :=
    degree_five_mixed_overload_has_paper_case_triple
      p hp hn v hv hh hrange hsupport hpos height assignments x hdegree hover hdiam
  exact ⟨i, j, k, hij, hik, hjk, hi,
    hj.paper_four_way p v height assignments,
    hk.paper_four_way p v height assignments, hjo, hko, hicase4⟩

end Erdos957
