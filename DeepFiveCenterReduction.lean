import DeepFiveDegreeSixSourceCapacity
import DeepReceiverCapacity

/-! In a hypothetical deep degree-five overload, every active source must
come from a retained degree-five center.  Degree-six centers are eliminated
by the full shared-six right-receiver capacity theorem. -/

namespace Erdos957

/-- Every positive donor in a genuine deep degree-five overload has retained
center degree exactly five.  Thus all degree-six shared-six/reflected-shared-six
constructors disappear from the remaining overload classification. -/
theorem certified_family_deep_five_overload_active_center_degree_five
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v i ∈ diameterEndpoints p) (x : Fin n)
    (hclose : dist (p (v i)) (p x) ≤ 2 * pairDist p ij)
    (hdeep : (3 / 2 : ℝ) * (pairDist p ij / dist (p (v i)) (p (v (i + 1)))) ≤
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).im)
    (hdegree : (nearestGraph p).degree x = 5)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (hover : 2 < ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x) :
    ∀ u (hud : u ∈ chargeDonors p (tightHullBadVertices p v)),
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x →
      (nearestGraph p).degree (assignments u hud).context.q = 5 := by
  have hno := tight_flat_deep_receiver_no_diameter_neighbor p hp hn v hv hh hsupport hpos
    ij hmin i hgood hu x hclose hdeep
  intro u hud hx
  have huD : u ∈ diameterEndpoints p := (Finset.mem_filter.mp hud).1
  have hnot : ¬ (nearestGraph p).Adj u x := by
    intro hux
    exact hno u hux.symm huD
  have hxrule : 0 < (assignments u hud).rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using hx
  rcases (assignments u hud).rule.center_degree_five_or_six_of_indirect x hxrule hnot with
      hfive | hsix
  · exact hfive
  · have hcap := certified_family_capacity_of_indirect_degree_six_center_source
      p hp hn v hv hh hrange hsupport hpos height assignments u hud x hx hnot hdegree hsix
    rw [hdegree] at hcap
    norm_num at hcap
    omega

end Erdos957
