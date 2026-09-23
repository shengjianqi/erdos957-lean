import LocalCharge
import MiddleNeighborInterior
import CentralCommonNeighbors

/-! Charge packets for a central nearest neighbor of a diameter endpoint. -/

namespace Erdos957

/-- When the central nearest neighbor has degree at most four, both local
charge units can be sent to that interior neighbor. -/
def localChargePacket_of_central_low_degree {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdegreeu : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j))
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hvdegree : (nearestGraph p).degree v ≤ 4) :
    LocalChargePacket p u := by
  have hinner := diameter_degree_three_central_neighbor_mem_interior
    p hn hp hdiam hdegreeu ij hmin hscale v huv hvlo hvhi
  have hvout := interior_not_diameterEndpoints p hp v hinner
  exact localChargePacket_of_low_degree_neighbor p huv hvout hvdegree

/-- Given a common nearest neighbor of the central edge, the central
interior neighbor and this common neighbor each receive one local unit.
The existence of a common neighbor remains an explicit premise. -/
def localChargePacket_of_central_common {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v a : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdegreeu : (nearestGraph p).degree u = 3)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (hscale : 2 * pairDist p ij < dist (p u) (p j))
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hvdegree : (nearestGraph p).degree v ≤ 5)
    (hua : (nearestGraph p).Adj u a)
    (hva : (nearestGraph p).Adj v a)
    (hunique : ∀ w, (nearestGraph p).Adj v w →
      w ∈ diameterEndpoints p → w = u) :
    LocalChargePacket p u := by
  have hinner := diameter_degree_three_central_neighbor_mem_interior
    p hn hp hdiam hdegreeu ij hmin hscale v huv hvlo hvhi
  have hvout := interior_not_diameterEndpoints p hp v hinner
  have hadegree := common_neighbor_degree_le_five_of_central
    p hn hp hdiam huv hvlo hvhi hua hva
  have haout : a ∉ diameterEndpoints p := by
    intro ha
    exact ((nearestGraph p).ne_of_adj hua) ((hunique a hva ha).symm)
  exact {
    left := v
    right := a
    left_outside := hvout
    right_outside := haout
    left_degree := hvdegree
    right_degree := hadegree
    repeated_degree := fun h => False.elim (((nearestGraph p).ne_of_adj hva) h)
    left_reachable := Or.inl huv
    right_reachable := Or.inl hua
  }

end Erdos957
