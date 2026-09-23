import ConfigurationCongruence
import ReflectedHull
import SharedFiveCharge
import LargeScaleReduction

/-! Reflection and reversal supply predecessor-side shared-five packets.
All original diameter memberships and the actual seven-position flatness
certificate are transported unchanged on the point indices. -/

namespace Erdos957

noncomputable def localChargePacket_of_tight_flat_shared_five_backward
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q j : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i - 1)))
    (hqu : (nearestGraph p).Adj q (v (i - 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i - 1) ∈ diameterEndpoints p)
    (hw : v i ∈ diameterEndpoints p)
    (hdiam : (diameterGraph p).Adj (v (i - 1)) j)
    (hscale : 10 * dist (p (v (i - 1))) (p (v i)) <
      dist (p (v (i - 1))) (p j)) : LocalChargePacket p (v i) := by
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterGraph_eq_of_dist_eq p pR hdist
  have hEnd := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdeg := nearestGraph_degree_eq_of_dist_eq p pR hdist q
  have hvR := reversedHullCycle_injective v hv
  have hrangeR : Set.range (reversedHullCycle v) =
      (hullVertexIndices pR : Set (Fin n)) := reflectedHull_range p v hrange
  have hsupportR : ∀ a k, 0 ≤ turn (pR (reversedHullCycle v a))
      (pR (reversedHullCycle v (a + 1))) (pR k) := reflectedHull_support p v hsupport
  have hposR : ∀ a, 0 < hullExteriorAngle pR (reversedHullCycle v) a := by
    intro a
    simpa only [pR, hullExteriorAngle_planeReflection_reversed] using hpos (-a)
  have hgoodR : reversedHullCycle v (-i) ∉
      tightHullBadVertices pR (reversedHullCycle v) := by
    apply tightHull_not_bad_planeReflection_reversed p v hv (-i)
    simpa only [neg_neg] using hgood
  let packetR := localChargePacket_of_tight_flat_shared_five pR hn hpR
    (reversedHullCycle v) hvR hh hrangeR hsupportR hposR (-i) q j
    (by simpa only [hG, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hbase)
    (by simpa only [hG, reversedHullCycle_neg_successor] using hqu)
    (by simpa only [hG, reversedHullCycle_neg] using hqw)
    (hdeg.trans hqdeg) hgoodR
    (by simpa only [hEnd, reversedHullCycle_neg_successor] using hu)
    (by simpa only [hEnd, reversedHullCycle_neg] using hw)
    (by simpa only [hD, reversedHullCycle_neg_successor] using hdiam)
    (by simpa only [hdist, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hscale)
  have packet : LocalChargePacket pR (v i) := by
    simpa only [reversedHullCycle_neg] using packetR
  exact packet.of_dist_eq p pR hdist

/-- Actual diameter membership gives a partner, while large cardinality
gives the required scale separation. The partner need not be a donor. -/
noncomputable def localChargePacket_of_backward_shared_five_of_large_card
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i - 1)))
    (hqu : (nearestGraph p).Adj q (v (i - 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i - 1) ∈ diameterEndpoints p)
    (hw : v i ∈ diameterEndpoints p) : LocalChargePacket p (v i) := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i - 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  have hscale : 10 * dist (p (v (i - 1))) (p (v i)) <
      dist (p (v (i - 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨localChargePacket_of_tight_flat_shared_five_backward
    p (by omega) hp v hv hh hrange hsupport hpos i q j
    hbase hqu hqw hqdeg hgood hu hw hdiam hscale⟩

end Erdos957
