import TightFlatSharedCharge
import LargeScaleReduction

/-! Shared-six packet choices that retain their actual hexagon witnesses,
degree-dependent selection rule and receiver geometry. Global capacity and
cyclic hull locality are separate obligations. -/

namespace Erdos957

/-- The first available low-degree site along the shared-six extension.
The last branch records the sharper degree-four bound and the actual
intermediate degree-six vertex. -/
def SharedSixReceiverRule {n : ℕ} (p : Fin n → Point)
    (u w v b t : Fin n) (h : ℝ) (k : Fin n) : Prop :=
  ((nearestGraph p).degree t ≤ 5 ∧ k = t) ∨
    ((nearestGraph p).degree t = 6 ∧ ∃ t₂ : Fin n,
      (nearestGraph p).Adj t t₂ ∧ (nearestGraph p).Adj b t₂ ∧
      p v + p t₂ = p t + p b ∧
      edgeCoordinate (p u) (p w) (p t₂) =
        (2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I ∧
      (((nearestGraph p).degree t₂ ≤ 5 ∧ k = t₂) ∨
        ((nearestGraph p).degree t₂ = 6 ∧ (nearestGraph p).Adj t₂ k ∧
          p k = 2 • p b - p v ∧
          edgeCoordinate (p u) (p w) (p k) =
            (5 / 2 : ℂ) - (h : ℂ) * Complex.I ∧
          (nearestGraph p).degree k ≤ 4)))

/-- A right-source packet together with the geometric and branch witnesses
used to select it. Every certificate remains accessible after classical choice. -/
structure SharedSixPacketChoice {n : ℕ} (p : Fin n → Point)
    (u w v : Fin n) where
  base : (nearestGraph p).Adj u w
  partner_diameter : u ∈ diameterEndpoints p
  height : ℝ
  height_pos : 0 < height
  height_sq : height ^ 2 = 3 / 4
  center_degree : (nearestGraph p).degree v = 6
  center_coordinate : edgeCoordinate (p u) (p w) (p v) =
    (1 / 2 : ℂ) - (height : ℂ) * Complex.I
  outer : Fin n
  lower : Fin n
  outer_adj_center : (nearestGraph p).Adj v outer
  outer_adj_source : (nearestGraph p).Adj w outer
  lower_adj_center : (nearestGraph p).Adj v lower
  outer_adj_lower : (nearestGraph p).Adj outer lower
  lower_ne_source : lower ≠ w
  outer_identity : p u + p outer = p v + p w
  lower_identity : p w + p lower = p v + p outer
  outer_coordinate : edgeCoordinate (p u) (p w) (p outer) =
    (3 / 2 : ℂ) - (height : ℂ) * Complex.I
  lower_coordinate : edgeCoordinate (p u) (p w) (p lower) =
    (1 : ℂ) - ((2 * height : ℝ) : ℂ) * Complex.I
  packet : LocalChargePacket p w
  packet_left : packet.left = outer
  sites_adjacent : (nearestGraph p).Adj packet.left packet.right
  sites_distinct : packet.left ≠ packet.right
  branch : SharedSixReceiverRule p u w v outer lower height packet.right
  receivers_in_region : ∀ k, 0 < packet.weight k →
    sharedReceiverRegion (edgeCoordinate (p u) (p w) (p k))
  receivers_interior : ∀ k, 0 < packet.weight k →
    p k ∈ interior (convexHull ℝ (Set.range p))

/-- The selected right receiver is one of the three exact normalized sites.
The branch field additionally retains the rule and intermediate witnesses. -/
theorem SharedSixPacketChoice.right_coordinate_cases {n : ℕ}
    {p : Fin n → Point} {u w v : Fin n}
    (choice : SharedSixPacketChoice p u w v) :
    edgeCoordinate (p u) (p w) (p choice.packet.right) =
        (1 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p u) (p w) (p choice.packet.right) =
        (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I ∨
      edgeCoordinate (p u) (p w) (p choice.packet.right) =
        (5 / 2 : ℂ) - (choice.height : ℂ) * Complex.I := by
  rcases choice.branch with ⟨_, hright⟩ | ⟨_, t₂, _, _, _, ht₂, hcases⟩
  · exact Or.inl (hright ▸ choice.lower_coordinate)
  rcases hcases with ⟨_, hright⟩ | ⟨_, _, _, hd, _⟩
  · exact Or.inr (Or.inl (hright ▸ ht₂))
  · exact Or.inr (Or.inr hd)

/-- The two distinct retained sites each receive one doubled charge unit,
equivalently one half-unit in the original charging convention. -/
theorem SharedSixPacketChoice.site_weights {n : ℕ}
    {p : Fin n → Point} {u w v : Fin n}
    (choice : SharedSixPacketChoice p u w v) :
    choice.packet.weight choice.packet.left = 1 ∧
      choice.packet.weight choice.packet.right = 1 := by
  simp [LocalChargePacket.weight, choice.sites_distinct, choice.sites_distinct.symm]

/-- The same actual hull-span hypotheses as the original shared-six packet
construction now produce a packet with all selection certificates retained. -/
noncomputable def sharedSixPacketChoice_of_hull_span {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v j : Fin n}
    (hvu : (nearestGraph p).Adj v u)
    (hvw : (nearestGraph p).Adj v w)
    (huw : (nearestGraph p).Adj u w)
    (hvdeg : (nearestGraph p).degree v = 6)
    (hw : w ∈ hullVertexIndices p)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) : SharedSixPacketChoice p u w v := by
  classical
  apply Classical.choice
  obtain ⟨b, t, hvb, hwb, hvt, hbt, htw, hbsum, htsum, hcases⟩ :=
    degree_six_shared_edge_low_degree_extension p hn hp hvu hvw huw hvdeg hw hsupport
  obtain ⟨h, hh, hhsq, hMv, hMb, hMt⟩ :=
    shared_hexagon_base_coordinates p hn hp hvu hvw huw hsupport hbsum htsum
  obtain ⟨hbreg, htreg, ht₂reg, hdreg⟩ := hexagon_receiver_sites_in_region h hh hhsq
  have hinterior (k : Fin n)
      (hk : sharedReceiverRegion (edgeCoordinate (p u) (p w) (p k))) :
      p k ∈ interior (convexHull ℝ (Set.range p)) :=
    span.receiver_mem_interior p (hp.ne huw.ne) hdiam hscale
      (hsupport j) (p k) hk
  have hout (k : Fin n)
      (hk : sharedReceiverRegion (edgeCoordinate (p u) (p w) (p k))) :
      k ∉ diameterEndpoints p :=
    interior_not_diameterEndpoints p hp k (hinterior k hk)
  have hbregion : sharedReceiverRegion (edgeCoordinate (p u) (p w) (p b)) :=
    hMb.symm ▸ hbreg
  have hbout : b ∉ diameterEndpoints p := hout b hbregion
  have hbdeg : (nearestGraph p).degree b ≤ 5 :=
    shared_outer_neighbor_degree_le_five p hn hp hvw hvb hwb hbsum hw huw.ne.symm
  have makeChoice (k : Fin n) (hbk : (nearestGraph p).Adj b k)
      (hkregion : sharedReceiverRegion (edgeCoordinate (p u) (p w) (p k)))
      (hkdeg : (nearestGraph p).degree k ≤ 5)
      (hrule : SharedSixReceiverRule p u w v b t h k) :
      Nonempty (SharedSixPacketChoice p u w v) := by
    let packet : LocalChargePacket p w := {
      left := b
      right := k
      left_outside := hbout
      right_outside := hout k hkregion
      left_degree := hbdeg
      right_degree := hkdeg
      repeated_degree := fun heq => False.elim (hbk.ne heq)
      left_reachable := Or.inl hwb
      right_reachable := Or.inr ⟨b, hwb, hbk⟩
    }
    have hregion (x : Fin n) (hx : 0 < packet.weight x) :
        sharedReceiverRegion (edgeCoordinate (p u) (p w) (p x)) := by
      by_cases hxb : x = b
      · exact hxb ▸ hbregion
      by_cases hxk : x = k
      · exact hxk ▸ hkregion
      simp [packet, LocalChargePacket.weight, hxb, hxk] at hx
    exact ⟨{
      base := huw
      partner_diameter := (mem_diameterEndpoints_iff_exists_adj p u).mpr ⟨j, hdiam⟩
      height := h
      height_pos := hh
      height_sq := hhsq
      center_degree := hvdeg
      center_coordinate := hMv
      outer := b
      lower := t
      outer_adj_center := hvb
      outer_adj_source := hwb
      lower_adj_center := hvt
      outer_adj_lower := hbt
      lower_ne_source := htw
      outer_identity := hbsum
      lower_identity := htsum
      outer_coordinate := hMb
      lower_coordinate := hMt
      packet := packet
      packet_left := rfl
      sites_adjacent := hbk
      sites_distinct := hbk.ne
      branch := hrule
      receivers_in_region := hregion
      receivers_interior := fun x hx => hinterior x (hregion x hx)
    }⟩
  by_cases htlow : (nearestGraph p).degree t ≤ 5
  · exact makeChoice t hbt (hMt.symm ▸ htreg) htlow (Or.inl ⟨htlow, rfl⟩)
  have htdeg : (nearestGraph p).degree t = 6 := by
    have := nearestGraph_degree_le_six p hn hp t
    omega
  rcases hcases with hfalse | ⟨t₂, htt₂, hbt₂, ht₂sum, hcases₂⟩
  · exact False.elim (htlow hfalse)
  have hMt₂ := shared_hexagon_t2_coordinate p h hMv hMb hMt ht₂sum
  by_cases ht₂low : (nearestGraph p).degree t₂ ≤ 5
  · exact makeChoice t₂ hbt₂ (hMt₂.symm ▸ ht₂reg) ht₂low
      (Or.inr ⟨htdeg, t₂, htt₂, hbt₂, ht₂sum, hMt₂, Or.inl ⟨ht₂low, rfl⟩⟩)
  have ht₂deg : (nearestGraph p).degree t₂ = 6 := by
    have := nearestGraph_degree_le_six p hn hp t₂
    omega
  rcases hcases₂ with hfalse | ⟨d, ht₂d, hbd, hdeq, hddeg⟩
  · exact False.elim (ht₂low hfalse)
  have hMd := shared_hexagon_d_coordinate p h hMv hMb hdeq
  exact makeChoice d hbd (hMd.symm ▸ hdreg) (by omega)
    (Or.inr ⟨htdeg, t₂, htt₂, hbt₂, ht₂sum, hMt₂,
      Or.inr ⟨ht₂deg, ht₂d, hdeq, hMd, hddeg⟩⟩)

/-- Actual tight-flat hull data construct the shared-six certificates;
the hull span is derived rather than supplied. -/
noncomputable def sharedSixPacketChoice_of_tight_flat_hull
    {n h : ℕ} [NeZero h]
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
      dist (p (v (i + 1))) (p j)) :
    SharedSixPacketChoice p (v (i + 1)) (v i) q := by
  have hw : v i ∈ hullVertexIndices p := by
    change v i ∈ (hullVertexIndices p : Set (Fin n))
    rw [← hrange]
    exact Set.mem_range_self i
  exact sharedSixPacketChoice_of_hull_span p hn hp hqu hqw hbase.symm
    hqdeg hw (hsupport i) hdiam hscale
    (normalizedHullSpan_of_tight_flat_vertex p hn hp v hv hh i hbase
      (hsupport i) hpos hgood)

/-- Large cardinality and actual diameter membership supply the scale
and partner, leaving only the actual tight-flat hull configuration. -/
noncomputable def sharedSixPacketChoice_of_large_card
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
    (hqdeg : (nearestGraph p).degree q = 6)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) :
    SharedSixPacketChoice p (v (i + 1)) (v i) q := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i + 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega : 2 ≤ n)
  have hscale : 10 * dist (p (v (i + 1))) (p (v i)) <
      dist (p (v (i + 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨sharedSixPacketChoice_of_tight_flat_hull p (by omega) hp v hv hh hrange
    hsupport hpos i q j hbase hqu hqw hqdeg hgood hdiam hscale⟩

end Erdos957
