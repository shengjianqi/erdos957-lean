import HullChordAdjacency
import TightFlatSharedCharge
import LargeScaleReduction

/-! Shared-six packets from an actual supporting nearest chord. The cyclic
successor identity and the long-diameter ratio are derived, not supplied. -/

namespace Erdos957

/-- In a sufficiently large configuration, an oriented supporting nearest
chord to another diameter endpoint supplies the verified shared-six packet.
The support condition itself remains an explicit geometric obligation. -/
noncomputable def localChargePacket_of_supported_shared_six_of_large_card
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q u : Fin n)
    (hbase : (nearestGraph p).Adj (v i) u)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 6)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : u ∈ diameterEndpoints p)
    (hchord : ∀ k, 0 ≤ turn (p (v i)) (p u) (p k)) :
    LocalChargePacket p (v i) := by
  apply Classical.choice
  have hn2 : 2 ≤ n := by omega
  have huhull := diameterEndpoints_subset_hullVertexIndices p hp hu
  have hunext := supporting_hull_chord_eq_successor p hp v hv hh hrange
    hsupport i u huhull hbase.ne.symm hchord
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn2
  obtain ⟨kl, hmax⟩ := exists_max_pair p hn2
  have hscale : 10 * dist (p u) (p (v i)) < dist (p u) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  subst u
  exact ⟨localChargePacket_of_tight_flat_shared_six p hn2 hp v hv hh hrange
    hsupport hpos i q j hbase hqu hqw hqdeg hgood hdiam hscale⟩

end Erdos957
