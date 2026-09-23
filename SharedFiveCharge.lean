import SharedFiveReceiver
import BoundaryTriangleSix
import TightFlatHullSpan
import LargeScaleReduction

/-! Shared-five local packets with the receiver exclusion proved from an
actual shallow hull span. Simultaneous global charge capacity is separate. -/

namespace Erdos957

/-- A shared-five triangle with an actual shallow hull span has a local
packet for its right endpoint. All receiver exclusions are derived. -/
noncomputable def localChargePacket_of_shared_five_hull_span {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q j : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hqdeg : (nearestGraph p).degree q = 5)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) : LocalChargePacket p w := by
  classical
  apply Classical.choice
  have hcard : ({u, w} : Finset (Fin n)).card <
      ((nearestGraph p).neighborFinset q).card := by
    rw [(nearestGraph p).card_neighborFinset_eq_degree, hqdeg]
    simp [huw.ne]
  obtain ⟨t, ht, htnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hqt := ((nearestGraph p).mem_neighborFinset q t).mp ht
  have htne : t ≠ u ∧ t ≠ w := by simpa only [Finset.mem_insert,
    Finset.mem_singleton, not_or] using htnot
  have hout (a : Fin n) (hqa : (nearestGraph p).Adj q a) (hau : a ≠ u) (haw : a ≠ w) :
      a ∉ diameterEndpoints p :=
    shared_triangle_other_neighbor_not_diameter p hn hp hqu hqw huw hqa
      hau haw hsupport hdiam hscale span
  by_cases htlow : (nearestGraph p).degree t ≤ 5
  · have hqout : q ∉ diameterEndpoints p := by
      intro hq
      have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp q hq
      omega
    exact ⟨{
      left := q
      right := t
      left_outside := hqout
      right_outside := hout t hqt htne.1 htne.2
      left_degree := hqdeg.le
      right_degree := htlow
      repeated_degree := fun heq => False.elim (hqt.ne heq)
      left_reachable := Or.inl hqw.symm
      right_reachable := Or.inr ⟨q, hqw.symm, hqt⟩
    }⟩
  · have htdeg : (nearestGraph p).degree t = 6 := by
      have := nearestGraph_degree_le_six p hn hp t
      omega
    have hcommonout (a : Fin n) (hqa : (nearestGraph p).Adj q a)
        (hta : (nearestGraph p).Adj t a) : a ∉ diameterEndpoints p := by
      have hne := shared_five_six_neighbor_ne_diameter_triangle_endpoints
        p hn hp hu hw hqdeg htdeg hqu hqw huw hta
      exact hout a hqa hne.1 hne.2
    exact ⟨localChargePacket_of_shared_five_six_edge p hn hp hqdeg htdeg
      hqt hqw hqu huw.symm hw hu hcommonout⟩

/-- The shallow span is constructed from the real tight-flat neighborhood;
no receiver-exclusion or span witness is assumed at this interface. -/
noncomputable def localChargePacket_of_tight_flat_shared_five
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (_hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q j : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hqu : (nearestGraph p).Adj q (v (i + 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) (hw : v i ∈ diameterEndpoints p)
    (hdiam : (diameterGraph p).Adj (v (i + 1)) j)
    (hscale : 10 * dist (p (v (i + 1))) (p (v i)) <
      dist (p (v (i + 1))) (p j)) : LocalChargePacket p (v i) := by
  exact localChargePacket_of_shared_five_hull_span p hn hp hqu hqw hbase.symm
    hqdeg hu hw (hsupport i) hdiam hscale
    (normalizedHullSpan_of_tight_flat_vertex p hn hp v hv hh i hbase
      (hsupport i) hpos hgood)

noncomputable def localChargePacket_of_forward_shared_five_of_large_card
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hqu : (nearestGraph p).Adj q (v (i + 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) (hw : v i ∈ diameterEndpoints p) :
    LocalChargePacket p (v i) := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i + 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  have hscale : 10 * dist (p (v (i + 1))) (p (v i)) <
      dist (p (v (i + 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨localChargePacket_of_tight_flat_shared_five p (by omega) hp
    v hv hh hrange hsupport hpos i q j hbase hqu hqw hqdeg hgood hu hw hdiam hscale⟩

end Erdos957
