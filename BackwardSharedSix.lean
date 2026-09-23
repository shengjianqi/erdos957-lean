import ConfigurationCongruence
import ReflectedHull
import TightFlatSharedCharge
import AdjacentDonorReduction

/-! Reflection and reversal supply the missing predecessor-side shared-six
packet, with the original seven-position flatness certificate. -/

namespace Erdos957

noncomputable def localChargePacket_of_tight_flat_shared_six_backward
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
    (hqdeg : (nearestGraph p).degree q = 6)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hdiam : (diameterGraph p).Adj (v (i - 1)) j)
    (hscale : 10 * dist (p (v (i - 1))) (p (v i)) <
      dist (p (v (i - 1))) (p j)) : LocalChargePacket p (v i) := by
  let pR : Fin n → Point := fun k => planeReflection (p k)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterGraph_eq_of_dist_eq p pR hdist
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
  let packetR := localChargePacket_of_tight_flat_shared_six pR hn hpR
    (reversedHullCycle v) hvR hh hrangeR hsupportR hposR (-i) q j
    (by simpa only [hG, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hbase)
    (by simpa only [hG, reversedHullCycle_neg_successor] using hqu)
    (by simpa only [hG, reversedHullCycle_neg] using hqw)
    (hdeg.trans hqdeg) hgoodR
    (by simpa only [hD, reversedHullCycle_neg_successor] using hdiam)
    (by simpa only [hdist, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hscale)
  have packet : LocalChargePacket pR (v i) := by
    simpa only [reversedHullCycle_neg] using packetR
  exact packet.of_dist_eq p pR hdist

/-- The scale and the partner diameter are obtained from actual diameter
membership, without requiring the partner to be a nonexceptional donor. -/
noncomputable def localChargePacket_of_backward_shared_six_of_large_card
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
    (hqdeg : (nearestGraph p).degree q = 6)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i - 1) ∈ diameterEndpoints p) : LocalChargePacket p (v i) := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i - 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  have hscale : 10 * dist (p (v (i - 1))) (p (v i)) <
      dist (p (v (i - 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨localChargePacket_of_tight_flat_shared_six_backward
    p (by omega) hp v hv hh hrange hsupport hpos i q j
    hbase hqu hqw hqdeg hgood hdiam hscale⟩

/-- All shared-six orientations now have local packets. The only remaining
local obstruction in the complete donor reduction is shared degree five. -/
theorem tight_flat_donor_packet_or_shared_five
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hu : v i ∈ chargeDonors p (tightHullBadVertices p v)) :
    ∃ ctx : DonorContext p (tightHullBadVertices p v) (v i),
      Nonempty (LocalChargePacket p (v i)) ∨
        ((nearestGraph p).degree ctx.q = 5 ∧
          ∃ w : Fin n, w ∈ diameterEndpoints p ∧
            (nearestGraph p).Adj (v i) w ∧ (nearestGraph p).Adj ctx.q w ∧
            (w = v (i + 1) ∨ w = v (i - 1))) := by
  obtain ⟨ctx, hpacket | ⟨w, hwD, huw, hqw, hcases⟩⟩ :=
    tight_flat_donor_packet_or_five_or_backward_six p hp hn v hv hh hrange
      hsupport hpos i hu
  · exact ⟨ctx, Or.inl hpacket⟩
  · rcases hcases with ⟨hfive, hwhere⟩ | ⟨hsix, rfl⟩
    · exact ⟨ctx, Or.inr ⟨hfive, w, hwD, huw, hqw, hwhere⟩⟩
    · exact ⟨ctx, Or.inl ⟨localChargePacket_of_backward_shared_six_of_large_card
        p hp hn v hv hh hrange hsupport hpos i ctx.q huw hqw
        ctx.central_adj.symm hsix ctx.outside_bad hwD⟩⟩

end Erdos957
