import FiveMiddleCommon
import CentralLocalCharge

/-! Local packets at the central neighbor of a long-diameter endpoint, under
the explicit condition that this central neighbor has no other diameter
endpoint among its nearest neighbors. The selected common neighbor is proved
outside the diameter endpoint set; no interior status or global receiver
overlap bound is claimed for it. -/

namespace Erdos957

/-- A degree-five central nearest neighbor has a common nearest neighbor
with the diameter endpoint, yielding a split local packet. -/
noncomputable def localChargePacket_of_central_degree_five {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdegreeu : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j))
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hvdegree : (nearestGraph p).degree v = 5)
    (hunique : ∀ w, (nearestGraph p).Adj v w →
      w ∈ diameterEndpoints p → w = u) :
    LocalChargePacket p u := by
  classical
  let hex := degree_five_central_neighbor_has_common_neighbor
    p hn hp hdiam hdegreeu huv hvlo hvhi hvdegree
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  exact localChargePacket_of_central_common p hn hp hdiam hdegreeu
    ij hmin hscale huv hvlo hvhi (by omega) ha.1 ha.2 hunique

/-- The unique-diameter-neighbor condition gives a local packet for every
degree of the central neighbor. Degree at most four uses a repeated receiver;
degree five uses a common neighbor; degree six uses the two common neighbors
of the boundary edge. -/
noncomputable def localChargePacket_of_unique_central_neighbor {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdegreeu : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j))
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hunique : ∀ w, (nearestGraph p).Adj v w →
      w ∈ diameterEndpoints p → w = u) :
    LocalChargePacket p u := by
  have hle := nearestGraph_degree_le_six p hn hp v
  by_cases hlow : (nearestGraph p).degree v ≤ 4
  · exact localChargePacket_of_central_low_degree p hn hp hdiam hdegreeu
      ij hmin hscale huv hvlo hvhi hlow
  by_cases hfive : (nearestGraph p).degree v = 5
  · exact localChargePacket_of_central_degree_five p hn hp hdiam hdegreeu
      ij hmin hscale huv hvlo hvhi hfive hunique
  have hsix : (nearestGraph p).degree v = 6 := by omega
  have hu : u ∈ diameterEndpoints p :=
    (mem_diameterEndpoints_iff_exists_adj p u).mpr ⟨j, hdiam⟩
  exact localChargePacket_of_six_neighbor p hn hp hu huv hsix hunique

end Erdos957
