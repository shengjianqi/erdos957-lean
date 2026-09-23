import ShallowPaperCaseTypes
import SharedFiveSixExtensionExclusion

/-! Orientation data for the surviving shallow Case-4 obstruction.  The
selected shared-five pair is a supported hull edge, so once the actual donor
is fixed its partner is the corresponding cyclic successor or predecessor.
This is the bridge from the source-local normal form to the paper's
left/right overcharging analysis. -/

namespace Erdos957

/-- A six-bottom indirect Case-4 source is an endpoint of its retained
shared-five pair, and that pair is an actual oriented hull edge.  If the
source is the right endpoint, the left endpoint is its successor; if it is
the left endpoint, the right endpoint is its predecessor. -/
theorem SixBottomIndirectSource.oriented_selected_pair
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
      (nearestGraph p).degree
          (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).selection.bottom = 6 ∧
      (((selectedSharedFiveCenter p (assignments (v i) hud).context.q available).right = v i ∧
          (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).left = v (i + 1)) ∨
       ((selectedSharedFiveCenter p (assignments (v i) hud).context.q available).left = v i ∧
          (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).right = v (i - 1))) := by
  classical
  obtain ⟨hud, _hx, _hnot, available, hbottom⟩ := hsrc
  let assignment := assignments (v i) hud
  let selected := selectedSharedFiveCenter p assignment.context.q available
  have hsource : v i = selected.left ∨ v i = selected.right :=
    selected.diameter_neighbor_cases (v i) assignment.context.endpoint
      assignment.context.central_adj.symm
  refine ⟨hud, available, ?_, ?_⟩
  · simpa only [assignment, selected] using hbottom
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

/-- Pure left/right orientation predicate for a surviving six-bottom Case-4
source.  This intentionally forgets the center and packet internals after
certifying the selected hull edge. -/
def SixBottomSourceOrientation {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (i : Fin h) : Prop :=
  ∃ (hud : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (available : Nonempty
      (SharedFiveCenterChoice p (assignments (v i) hud).context.q)),
    (nearestGraph p).degree
        (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).selection.bottom = 6 ∧
    (((selectedSharedFiveCenter p (assignments (v i) hud).context.q available).right = v i ∧
        (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).left = v (i + 1)) ∨
     ((selectedSharedFiveCenter p (assignments (v i) hud).context.q available).left = v i ∧
        (selectedSharedFiveCenter p (assignments (v i) hud).context.q available).right = v (i - 1)))

/-- Every canonical six-bottom source carries the orientation certificate. -/
theorem SixBottomIndirectSource.has_orientation
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
    SixBottomSourceOrientation p v height assignments x i :=
  hsrc.oriented_selected_pair p hp v hv hh hrange hsupport height assignments x i

/-- The current overload normal form with the Case-4 anchor already oriented.
This is the direct input expected by a left/right side-capacity argument. -/
theorem degree_five_mixed_overload_has_oriented_case4_paper_triple
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
      SixBottomSourceOrientation p v height assignments x i ∧
      PaperFourWaySource p v height assignments (v j) ∧
      PaperFourWaySource p v height assignments (v k) ∧
      (j = i + 1 ∨ j = i - 1 ∨
        j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
        j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1) ∧
      (k = i + 1 ∨ k = i - 1 ∨
        k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
        k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hjo, hko, _hicase4⟩ :=
    degree_five_mixed_overload_has_case4_anchored_paper_triple
      p hp hn v hv hh hrange hsupport hpos height assignments
        x hdegree hover hdiam
  exact ⟨i, j, k, hij, hik, hjk, hi,
    hi.has_orientation p hp v hv hh hrange hsupport height assignments x i,
    hj, hk, hjo, hko⟩

end Erdos957
