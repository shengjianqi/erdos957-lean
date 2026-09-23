import AllCertifiedDonors
import FiveHighestSelection

/-! A single donor-indexed height family using the actual outgoing hull
edge. Its unique-five choices maximize this supporting height among every
non-donor neighbor of the retained center. -/

namespace Erdos957

/-- On the indexed hull, score by height toward the exterior in the
outgoing-edge frame. The score is zero for indices outside that hull. -/
noncomputable def hullSupportingHeight {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (u x : Fin n) : ℝ := by
  classical
  exact if hu : u ∈ Set.range v then
    supportingHeight p u (v (Classical.choose hu + 1)) x else 0

/-- Injectivity makes the chosen hull index the actual index, independently
of the proof of membership used by classical choice. -/
theorem hullSupportingHeight_at {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (hv : Function.Injective v)
    (i : Fin h) :
    hullSupportingHeight p v (v i) = supportingHeight p (v i) (v (i + 1)) := by
  classical
  funext x
  have hi : v i ∈ Set.range v := Set.mem_range_self i
  have hindex : Classical.choose hi = i := hv (Classical.choose_spec hi)
  simp only [hullSupportingHeight, dite_eq_left hi, hindex]

/-- Every five-degree rule with a unique diameter neighbor is the central
rule, and actual supporting-height scoring gives the global maximum. -/
theorem CertifiedDonorRule.five_supporting_global_maximum {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u s : Fin n} (ctx : DonorContext p bad u)
    (hus : u ≠ s) (hsupport : ∀ k, 0 ≤ turn (p u) (p s) (p k))
    {height : Fin n → ℝ} (rule : CertifiedDonorRule p u ctx.q height)
    (hheight : height = supportingHeight p u s)
    (hfive : (nearestGraph p).degree ctx.q = 5) (hunique : UniqueD p u ctx.q) :
    (nearestGraph p).Adj u rule.packet.right ∧
      (nearestGraph p).Adj ctx.q rule.packet.right ∧
      ∀ b, (nearestGraph p).Adj ctx.q b → b ≠ u →
        supportingHeight p u s b ≤ supportingHeight p u s rule.packet.right := by
  subst height
  cases rule with
  | low choice =>
    have := choice.central_degree
    omega
  | unique choice _ =>
    exact choice.five_supporting_global_maximum p hn hp ctx hus hsupport hfive
  | sharedFive available _ _ =>
    let choice := selectedSharedFiveCenter p ctx.q available
    have hl := hunique choice.left choice.center_left choice.left_diameter
    have hr := hunique choice.right choice.center_right choice.right_diameter
    exact False.elim (choice.base.ne (hl.trans hr.symm))
  | sharedSix choice =>
    have := choice.center_degree
    omega
  | reflectedSharedSix choice =>
    have := choice.original_neighbors.1
    omega

/-- The existing certified-family construction instantiated once with the
actual donor-indexed outgoing-edge scores. Shared-five center reuse is inherited. -/
noncomputable def supportingCertifiedDonorRules_of_tight_flat_hull
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (u : Fin n) (hu : u ∈ chargeDonors p (tightHullBadVertices p v)) :
    CertifiedDonorAssignment p (tightHullBadVertices p v) u (hullSupportingHeight p v u) :=
  certifiedDonorRules_of_tight_flat_hull p hp hn v hv hh hrange hsupport hpos
    (hullSupportingHeight p v) u hu

/-- Any retained assignment using the hull scores has the highest actual
outgoing-frame secondary site in its unique-five branch. -/
theorem CertifiedDonorAssignment.five_hull_supporting_global_maximum
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    {bad : Finset (Fin n)} (i : Fin h)
    (assignment : CertifiedDonorAssignment p bad (v i) (hullSupportingHeight p v (v i)))
    (hfive : (nearestGraph p).degree assignment.context.q = 5)
    (hunique : UniqueD p (v i) assignment.context.q) :
    (nearestGraph p).Adj (v i) assignment.packet.right ∧
      (nearestGraph p).Adj assignment.context.q assignment.packet.right ∧
      ∀ b, (nearestGraph p).Adj assignment.context.q b → b ≠ v i →
        supportingHeight p (v i) (v (i + 1)) b ≤
          supportingHeight p (v i) (v (i + 1)) assignment.packet.right :=
  assignment.rule.five_supporting_global_maximum p hn hp assignment.context
    (hv.ne (cyclic_three_distinct hh i).1) (hsupport i)
    (hullSupportingHeight_at p v hv i) hfive hunique

/-- The concrete chosen family, including its actual retained centers,
inherits the global supporting-height maximum whenever the center is unique-five. -/
theorem supportingCertifiedDonorRules_five_global_maximum
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v)) :
    let assignment := supportingCertifiedDonorRules_of_tight_flat_hull
      p hp hn v hv hh hrange hsupport hpos (v i) hu
    (nearestGraph p).degree assignment.context.q = 5 →
      UniqueD p (v i) assignment.context.q →
      (nearestGraph p).Adj (v i) assignment.packet.right ∧
        (nearestGraph p).Adj assignment.context.q assignment.packet.right ∧
        ∀ b, (nearestGraph p).Adj assignment.context.q b → b ≠ v i →
          supportingHeight p (v i) (v (i + 1)) b ≤
            supportingHeight p (v i) (v (i + 1)) assignment.packet.right := by
  intro assignment hfive hunique
  exact assignment.five_hull_supporting_global_maximum p (by omega) hp
    v hv hh hsupport i hfive hunique

end Erdos957
