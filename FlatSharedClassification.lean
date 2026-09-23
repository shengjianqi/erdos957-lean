import TightFlatDiameterLocality
import FlatCentralProjection

/-! Actual tight-flat geometry turns every shared central diameter neighbor
into a nearest boundary triangle. There is no ordinary-packet early return
and no assumed nearest base edge. -/

namespace Erdos957

/-- A distinct diameter endpoint sharing the actual central neighbor lies
at the predecessor or successor. All remote positions and both two-step
positions are excluded by uniform inequalities. -/
theorem tight_flat_shared_central_neighbor_adjacent {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (w : Fin n) (hwD : w ∈ diameterEndpoints p)
    (hqw : (nearestGraph p).Adj ctx.q w) (hne : w ≠ v i) :
    w = v (i + 1) ∨ w = v (i - 1) := by
  have hclose : dist (p (v i)) (p w) ≤ 2 * pairDist p ctx.minPair := by
    have ht := dist_triangle (p (v i)) (p ctx.q) (p w)
    rw [nearestGraph_adj_dist_eq p ctx.minPair_spec ctx.central_adj,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hqw] at ht
    linarith
  rcases tight_flat_nearby_diameter_endpoint_local p hp hn v hv hh hsupport
      hpos ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint w hwD hclose
    with hself | hnext | hprev | hnext2 | hprev2
  · exact False.elim (hne hself)
  · exact Or.inl hnext
  · exact Or.inr hprev
  · exact False.elim ((tight_flat_central_neighbor_not_adjacent_two_step
      p (by omega) hp v hv hh hsupport hpos i ctx w (Or.inl hnext2)) hqw)
  · exact False.elim ((tight_flat_central_neighbor_not_adjacent_two_step
      p (by omega) hp v hv hh hsupport hpos i ctx w (Or.inr hprev2)) hqw)

/-- The actual neighboring hull edge supports the point set; centrality then
forces its length to be the minimum distance. No degree condition on q is used. -/
theorem tight_flat_shared_central_neighbor_nearest {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (w : Fin n) (hwD : w ∈ diameterEndpoints p)
    (hqw : (nearestGraph p).Adj ctx.q w) (hne : w ≠ v i) :
    (nearestGraph p).Adj (v i) w ∧
      (w = v (i + 1) ∨ w = v (i - 1)) := by
  have hwhere := tight_flat_shared_central_neighbor_adjacent
    p hp hn v hv hh hsupport hpos i ctx w hwD hqw hne
  refine ⟨central_common_neighbor_nearest_of_support p (by omega) hp ctx
    hne.symm hqw ?_, hwhere⟩
  rcases hwhere with hnext | hprev
  · left
    rw [hnext]
    exact hsupport i
  · right
    rw [hprev]
    simpa only [sub_add_cancel] using hsupport (i - 1)

/-- SharedD now always yields a genuine nearest boundary triangle at a
tight-flat donor, with no unrelated direct packet alternative. -/
theorem tight_flat_sharedD_has_nearest_triangle {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (hshared : SharedD p (v i) ctx.q) :
    ∃ w, w ∈ diameterEndpoints p ∧ (nearestGraph p).Adj (v i) w ∧
      (nearestGraph p).Adj ctx.q w ∧ (w = v (i + 1) ∨ w = v (i - 1)) := by
  obtain ⟨w, hne, hqw, hwD⟩ := hshared
  obtain ⟨huw, hwhere⟩ := tight_flat_shared_central_neighbor_nearest
    p hp hn v hv hh hsupport hpos i ctx w hwD hqw hne
  exact ⟨w, hwD, huw, hqw, hwhere⟩

end Erdos957
