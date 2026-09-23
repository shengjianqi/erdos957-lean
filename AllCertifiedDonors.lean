import FlatSharedClassification
import CertifiedDonorRules
import CollinearBound

/-! Uniform coverage by the explicit retained rule certificates. This gives
one certified rule per donor, with center-indexed shared-five reuse. A global
capacity bound and the remaining supporting-frame estimates are separate. -/

namespace Erdos957

/-- Retain the actual donor context together with its rule, so that the
center, diameter partner and central-angle evidence survive family selection. -/
structure CertifiedDonorAssignment {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n)) (u : Fin n) (height : Fin n → ℝ) where
  context : DonorContext p bad u
  rule : CertifiedDonorRule p u context.q height

noncomputable def CertifiedDonorAssignment.packet {n : ℕ}
    {p : Fin n → Point} {bad : Finset (Fin n)} {u : Fin n} {height : Fin n → ℝ}
    (assignment : CertifiedDonorAssignment p bad u height) : LocalChargePacket p u :=
  assignment.rule.packet

/-- Every actual tight-flat donor is covered by a full rule constructor.
The shared branch uses proved hull geometry, not an additional premise. -/
theorem tight_flat_donor_has_certified_rule {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (height : Fin n → ℝ) :
    Nonempty (CertifiedDonorRule p (v i) ctx.q height) := by
  rcases certified_direct_rule_or_shared p (by omega) hp ctx height with hdone | hshared
  · exact hdone
  · obtain ⟨w, hwD, huw, hqw, hwhere⟩ :=
      tight_flat_sharedD_has_nearest_triangle p hp hn v hv hh hsupport hpos i ctx
        hshared.2
    exact certifiedDonorRule_of_adjacent_shared p hp hn v hv hh hrange hsupport
      hpos i ctx height hshared.1 w hwD huw hqw hwhere

/-- A single certified family is selected on the actual donor set. A scoring
function may be supplied separately for each donor's central rule. -/
noncomputable def certifiedDonorRules_of_tight_flat_hull
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (height : Fin n → Fin n → ℝ)
    (u : Fin n) (hu : u ∈ chargeDonors p (tightHullBadVertices p v)) :
    CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u) := by
  apply Classical.choice
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hu).1
  have huhull := diameterEndpoints_subset_hullVertexIndices p hp huD
  have hurange : u ∈ Set.range v := by rw [hrange]; exact huhull
  obtain ⟨i, rfl⟩ := hurange
  let ctx := donorContext_of_large_card p hp hn (tightHullBadVertices p v) (v i) hu
  obtain ⟨rule⟩ := tight_flat_donor_has_certified_rule
    p hp hn v hv hh hrange hsupport hpos i ctx (height (v i))
  exact ⟨⟨ctx, rule⟩⟩

/-- The actual hull and bounded exceptional set provide every required
geometric premise for the retained rule family in a large noncollinear set. -/
theorem exists_certified_rules_of_large_noncollinear {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (hnot : ¬ Collinear ℝ (Set.range p)) (height : Fin n → Fin n → ℝ) :
    ∃ bad : Finset (Fin n), bad.card ≤ 25200 ∧
      Nonempty (∀ u, u ∈ chargeDonors p bad →
        CertifiedDonorAssignment p bad u (height u)) := by
  have hh := hullVertexCount_ge_three_of_noncollinear p hnot
  let : NeZero (hullVertexCount p) := ⟨by omega⟩
  obtain ⟨v, hv, hrange, hsupport, hpos, _hsum, hcard, _hsub, _hgood⟩ :=
    exists_tight_hull_bad_vertices_of_noncollinear p (by omega) hp hnot
  exact ⟨tightHullBadVertices p v, hcard,
    ⟨certifiedDonorRules_of_tight_flat_hull p hp hn v hv hh hrange
      hsupport (fun i => (hpos i).1) height⟩⟩

/-- All point counts and degenerate configurations are covered, with the
same uniform exception constant. This does not assert simultaneous capacity. -/
theorem exists_uniform_certified_rules {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (height : Fin n → Fin n → ℝ) :
    ∃ bad : Finset (Fin n), bad.card ≤ 25200 ∧
      Nonempty (∀ u, u ∈ chargeDonors p bad →
        CertifiedDonorAssignment p bad u (height u)) := by
  have hall : Nonempty (∀ u, u ∈ chargeDonors p (diameterEndpoints p) →
      CertifiedDonorAssignment p (diameterEndpoints p) u (height u)) := by
    refine ⟨fun u hu => False.elim ?_⟩
    obtain ⟨huD, hunot, _⟩ := Finset.mem_filter.mp hu
    exact hunot huD
  by_cases hsmall : n ≤ 1681
  · refine ⟨diameterEndpoints p, ?_, hall⟩
    have hc := diameterEndpointCount_le p
    change (diameterEndpoints p).card ≤ n at hc
    omega
  by_cases hcol : Collinear ℝ (Set.range p)
  · refine ⟨diameterEndpoints p, ?_, hall⟩
    have hc := diameterEndpointCount_le_two_of_collinear p hp hcol
    change (diameterEndpoints p).card ≤ 2 at hc
    omega
  exact exists_certified_rules_of_large_noncollinear p hp (by omega) hcol height

end Erdos957
