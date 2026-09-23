import AllCertifiedDonors
import ChargeNeighborhood
import PacketMetricLocality
import SupportingPacketFrames
import FourDeltaDiameterLocality

/-! Supporting coordinates restrict all simultaneous positive sources of a
certified family to a single seven-position hull neighborhood. The resulting
sum is exact; a weighted capacity bound remains a separate obligation. -/

namespace Erdos957

/-- A receiver's horizontal bound plus the actual two-step packet distance
bounds the horizontal position of any other source using that receiver. -/
theorem packet_source_horizontal_bound {n : ℕ}
    (p : Fin n → Point) (a b w x : Fin n) (hab : p a ≠ p b)
    (ij : Fin n × Fin n) (hmin : isMinPair p ij)
    (packet : LocalChargePacket p w) (hx : 0 < packet.weight x)
    (hreceiver : |(edgeCoordinate (p a) (p b) (p x)).re| ≤
      (7 / 4 : ℝ) * (pairDist p ij / dist (p a) (p b))) :
    |(edgeCoordinate (p a) (p b) (p w)).re| ≤
      (15 / 4 : ℝ) * (pairDist p ij / dist (p a) (p b)) := by
  let M := fun k => edgeCoordinate (p a) (p b) (p k)
  have hd := packet.positive_dist_le_two_min hmin hx
  have hnorm : ‖M w - M x‖ ≤ 2 * (pairDist p ij / dist (p a) (p b)) := by
    rw [← dist_eq_norm]
    dsimp [M]
    rw [edgeCoordinate_dist _ _ _ _ hab]
    calc
      dist (p w) (p x) / dist (p a) (p b) ≤
          (2 * pairDist p ij) / dist (p a) (p b) :=
        div_le_div_of_nonneg_right hd dist_nonneg
      _ = 2 * (pairDist p ij / dist (p a) (p b)) := by ring
  have htriangle : |(M w).re| ≤ |(M x).re| + ‖M w - M x‖ := by
    calc
      |(M w).re| = |(M x).re + (M w - M x).re| := by
        congr 1
        simp only [Complex.sub_re]
        ring
      _ ≤ |(M x).re| + |(M w - M x).re| := abs_add_le _ _
      _ ≤ |(M x).re| + ‖M w - M x‖ :=
        add_le_add le_rfl (Complex.abs_re_le_norm _)
  change |(M x).re| ≤ _ at hreceiver
  change |(M w).re| ≤ _
  linarith

/-- A retained rule family supplies the actual packets used in the total. -/
noncomputable def certifiedFamilyPackets {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (u : Fin n) (hu : u ∈ chargeDonors p bad) : LocalChargePacket p u :=
  (assignments u hu).packet

theorem localPacketCharge_pos_donor {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (u x : Fin n) (hx : 0 < localPacketCharge p bad packets u x) :
    u ∈ chargeDonors p bad := by
  classical
  by_contra hnot
  simp only [localPacketCharge, dite_eq_right hnot] at hx
  omega

/-- Every diameter endpoint whose packet shares a positive receiver with a
certified donor belongs to the seven actual hull positions around that donor.
The second packet needs no geometric certificate beyond LocalChargePacket. -/
theorem certified_rule_common_receiver_source_local {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (height : Fin n → ℝ) (rule : CertifiedDonorRule p (v i) ctx.q height)
    (w : Fin n) (hwD : w ∈ diameterEndpoints p) (packet : LocalChargePacket p w)
    (x : Fin n) (hx : 0 < rule.packet.weight x) (hwx : 0 < packet.weight x) :
    w ∈ hullSourceNeighborhood v i := by
  have hrect := certifiedDonorRule_supporting_rectangle
    p hp hn v hv hh hrange hsupport hpos i ctx height rule x hx
  have hab : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have hhorizontal := packet_source_horizontal_bound p (v i) (v (i + 1)) w x
    hab ctx.minPair ctx.minPair_spec packet hwx hrect.1
  have hclose := rule.packet.sources_dist_le_four_min packet ctx.minPair_spec hx hwx
  exact (mem_hullSourceNeighborhood_iff v i w).mpr
    (tight_flat_four_distance_diameter_endpoint_local p hp hn v hv hh hsupport hpos
      ctx.minPair ctx.minPair_spec i ctx.outside_bad ctx.endpoint w hwD hclose hhorizontal)

/-- The support restriction holds for the complete assembled charge family,
including every simultaneous contribution and every mixture of rule types. -/
theorem certified_family_positive_source_local {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (i : Fin h) (w x : Fin n)
    (hix : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v i) x)
    (hwx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x) :
    w ∈ hullSourceNeighborhood v i := by
  classical
  let packets := certifiedFamilyPackets p (tightHullBadVertices p v) height assignments
  have hi := localPacketCharge_pos_donor p (tightHullBadVertices p v) packets (v i) x hix
  have hw := localPacketCharge_pos_donor p (tightHullBadVertices p v) packets w x hwx
  let assignment := assignments (v i) hi
  have hiweight : 0 < assignment.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hi, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, assignment] using hix
  have hwweight : 0 < (packets w hw).weight x := by
    simpa only [localPacketCharge, dite_eq_left hw] using hwx
  exact certified_rule_common_receiver_source_local p hp hn v hv hh hrange hsupport hpos
    i assignment.context (height (v i)) assignment.rule w (Finset.mem_filter.mp hw).1
    (packets w hw) x hiweight hwweight

/-- Once any positive source is anchored, the full incoming weighted sum is
exactly the sum over its seven-position neighborhood. No contribution is lost. -/
theorem certified_family_charge_sum_eq_seven_positions {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (i : Fin h) (x : Fin n)
    (hix : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v i) x) :
    let packets := certifiedFamilyPackets p (tightHullBadVertices p v) height assignments
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v) packets u x =
      ∑ u ∈ hullSourceNeighborhood v i,
        localPacketCharge p (tightHullBadVertices p v) packets u x := by
  apply localPacketCharge_sum_eq_neighborhood
  intro w hwx
  exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
    height assignments i w x hix hwx

/-- At most seven donors contribute positively to one receiver. This count
alone does not establish the degree-dependent weighted receiver capacity. -/
theorem certified_family_positive_sources_card_le_seven {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (i : Fin h) (x : Fin n)
    (hix : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) (v i) x) :
    ((chargeDonors p (tightHullBadVertices p v)).filter (fun u =>
      0 < localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)).card ≤
      7 := by
  apply le_trans (localPacketCharge_active_card_le_neighborhood p (tightHullBadVertices p v)
    (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments)
    (hullSourceNeighborhood v i) x ?_) (hullSourceNeighborhood_card_le_seven v i)
  intro w hwx
  exact certified_family_positive_source_local p hp hn v hv hh hrange hsupport hpos
    height assignments i w x hix hwx

end Erdos957
