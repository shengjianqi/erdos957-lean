import TightFlatHullSpan
import SharedHexagonCharge

/-! The shared degree-six right-donor packet from a real tight-flat hull edge. -/

namespace Erdos957

noncomputable def localChargePacket_of_tight_flat_shared_six {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q j : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hqu : (nearestGraph p).Adj q (v (i + 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 6)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hdiam : (diameterGraph p).Adj (v (i + 1)) j)
    (hscale : 10 * dist (p (v (i + 1))) (p (v i)) <
      dist (p (v (i + 1))) (p j)) : LocalChargePacket p (v i) := by
  have hw : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  exact localChargePacket_of_shared_six_hull_span p hn hp hqu hqw hbase.symm
    hqdeg hw (hsupport i) hdiam hscale
    (normalizedHullSpan_of_tight_flat_vertex p hn hp v hv hh i hbase
      (hsupport i) hpos hgood)

/-- A real hull order with uniformly bounded exceptions supplies all packets
of the adjacent shared-six type. Other donor types and congestion are separate. -/
theorem exists_tight_shared_six_packets_of_noncollinear {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hnot : ¬ Collinear ℝ (Set.range p)) :
    letI : NeZero (hullVertexCount p) :=
      ⟨by have := hullVertexCount_ge_three_of_noncollinear p hnot; omega⟩
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      (∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k)) ∧
      (tightHullBadVertices p v).card ≤ 25200 ∧
      (∀ (i : Fin (hullVertexCount p)) (q j : Fin n),
        (nearestGraph p).Adj (v i) (v (i + 1)) →
        (nearestGraph p).Adj q (v (i + 1)) →
        (nearestGraph p).Adj q (v i) →
        (nearestGraph p).degree q = 6 →
        v i ∉ tightHullBadVertices p v →
        (diameterGraph p).Adj (v (i + 1)) j →
        10 * dist (p (v (i + 1))) (p (v i)) < dist (p (v (i + 1))) (p j) →
        Nonempty (LocalChargePacket p (v i))) := by
  have hh := hullVertexCount_ge_three_of_noncollinear p hnot
  have : NeZero (hullVertexCount p) := ⟨by omega⟩
  obtain ⟨v, hv, hrange, hsupport, hpos, _hsum, hcard, _hsub, _hgood⟩ :=
    exists_tight_hull_bad_vertices_of_noncollinear p hn hp hnot
  refine ⟨v, hv, hrange, hsupport, hcard, ?_⟩
  intro i q j hbase hqu hqw hqdeg hgood hdiam hscale
  exact ⟨localChargePacket_of_tight_flat_shared_six p hn hp v hv hh hrange
    hsupport (fun k => (hpos k).1) i q j hbase hqu hqw hqdeg hgood hdiam hscale⟩

end Erdos957
