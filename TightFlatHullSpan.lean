import HullSpanFromDirections
import TightHullDirections
import TightFlatOffsets

/-! Construct the shallow hull span from the actual small exterior angles. -/

namespace Erdos957

/-- No span witness is assumed: it is constructed from the closest hull edge
and the five small turns guaranteed outside the tight exceptional set. -/
noncomputable def normalizedHullSpan_of_tight_flat_vertex {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h) (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hsupport : ∀ k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (hgood : v i ∉ tightHullBadVertices p v) :
    NormalizedHullSpan p (v (i + 1)) (v i) := by
  obtain ⟨hi, hm1, hm2, hp1, hp2⟩ := tight_hull_five_turns_of_not_bad p v hv i hgood
  exact normalizedHullSpan_of_nearby_edge_args p hn hp v hv hh i hbase hsupport
    (tight_hull_nearby_edge_args p hp v hv hh i hpos hi hm1 hm2 hp1 hp2)

end Erdos957
