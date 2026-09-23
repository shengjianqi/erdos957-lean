import ShallowCase4OppositeSideExclusion

/-! Uniform projection exclusions for direct competitors of a Case-4 source.
The estimates apply to every direct donor, independently of its paper case. -/

namespace Erdos957

/-- In a nearest outgoing-edge frame, the three remote local positions
`i+3`, `i-2`, and `i-3` cannot be adjacent to a point in the shared-five
receiving strip. -/
theorem tight_flat_remote_not_adj_of_receiving_strip
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (hgood : v i ∉ tightHullBadVertices p v)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (x : Fin n)
    (hxlo : -(1 / 2 : ℝ) ≤ (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re)
    (hxhi : (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re ≤ 3 / 2)
    (j : Fin h)
    (hj : j = ((i + 1) + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i - 1) - 1) - 1) :
    ¬ (nearestGraph p).Adj (v j) x := by
  intro hadj
  let M := edgeCoordinate (p (v i)) (p (v (i + 1)))
  have hAB : p (v i) ≠ p (v (i + 1)) := hp.ne hbase.ne
  have hstep (k : Fin h)
      (hk : k = ((i - 1) - 1) - 1 ∨ k = (i - 1) - 1 ∨
        k = i - 1 ∨ k = i + 1 ∨ k = (i + 1) + 1) :
      (99 / 100 : ℝ) ≤ (M (p (v (k + 1)))).re - (M (p (v k))).re := by
    have harg := tight_hull_eight_edge_args p hp v hv hh i hpos hgood k
      (by rcases hk with rfl | rfl | rfl | rfl | rfl <;> tauto)
    have hnorm := hullEdgeDirection_div_norm_ge_one p hn hp v hv hh i hbase k
    have hproj := (extended_small_arg_projection
      (hullEdgeDirection p v k / hullEdgeDirection p v i) harg).1
    have heq : M (p (v (k + 1))) - M (p (v k)) =
        hullEdgeDirection p v k / hullEdgeDirection p v i := by
      exact edgeCoordinate_sub (p (v i)) (p (v (i + 1)))
        (p (v k)) (p (v (k + 1)))
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re] at hre
    nlinarith
  have hp1 := hstep (i + 1) (by tauto)
  have hp2 := hstep ((i + 1) + 1) (by tauto)
  have hm1 := hstep (i - 1) (by tauto)
  have hm2 := hstep ((i - 1) - 1) (by tauto)
  have hm3 := hstep (((i - 1) - 1) - 1) (by tauto)
  simp only [sub_add_cancel] at hm1 hm2 hm3
  have hzero : M (p (v i)) = 0 := by simp [M, edgeCoordinate]
  have hone : M (p (v (i + 1))) = 1 := edgeCoordinate_axis _ _ hAB
  rw [hzero, Complex.zero_re] at hm1
  rw [hone, Complex.one_re] at hp1
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ab := pairDist_pos p hp hmin.1
  have hdist : dist (M (p (v j))) (M (p x)) = 1 := by
    rw [edgeCoordinate_dist _ _ _ _ hAB,
      nearestGraph_adj_dist_eq p hmin hadj,
      nearestGraph_adj_dist_eq p hmin hbase, div_self hδ.ne']
  have hreal : |(M (p (v j))).re - (M (p x)).re| ≤ 1 := by
    have hb := Complex.abs_re_le_norm (M (p (v j)) - M (p x))
    simpa only [Complex.sub_re, ← dist_eq_norm, hdist] using hb
  have hlow := (abs_le.mp hreal).1
  have hhigh := (abs_le.mp hreal).2
  change -(1 / 2 : ℝ) ≤ (M (p x)).re at hxlo
  change (M (p x)).re ≤ 3 / 2 at hxhi
  rcases hj with rfl | rfl | rfl <;> linarith

/-- Strip geometry alone rules out two residual direct competitors. -/
theorem tight_flat_two_direct_competitors_impossible_of_strip
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i j k : Fin h) (x : Fin n)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hjgood : v j ∉ tightHullBadVertices p v)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hxlo : -(1 / 2 : ℝ) ≤ (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re)
    (hxhi : (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re ≤ 3 / 2)
    (hjloc : ForwardCase4ResidualOffset i j)
    (hkloc : ForwardCase4ResidualOffset i k)
    (hjk : j ≠ k)
    (hjdirect : (nearestGraph p).Adj (v j) x)
    (hkdirect : (nearestGraph p).Adj (v k) x) : False := by
  have hoff (t : Fin h) (ht : ForwardCase4ResidualOffset i t)
      (hadj : (nearestGraph p).Adj (v t) x) : t = i - 1 ∨ t = (i + 1) + 1 := by
    rcases ht with hm1 | hp2 | hm2 | hp3 | hm3
    · exact Or.inl hm1
    · exact Or.inr hp2
    all_goals
      exact False.elim ((tight_flat_remote_not_adj_of_receiving_strip
        p hn hp v hv hh hpos i hgood hbase x hxlo hxhi t (by tauto)) hadj)
  have hjoff := hoff j hjloc hjdirect
  have hkoff := hoff k hkloc hkdirect
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hremote : k = ((j + 1) + 1) + 1 ∨ k = ((j - 1) - 1) - 1 := by
    rcases hjoff with hjm | hjp <;> rcases hkoff with hkm | hkp
    · exact False.elim (hjk (hjm.trans hkm.symm))
    · left
      rw [hjm, hkp]
      abel
    · right
      rw [hjp, hkm]
      abel
    · exact False.elim (hjk (hjp.trans hkp.symm))
  exact (tight_flat_three_step_no_common_nearest p hp v hv hh ab hmin
    j hpos hjgood (v k)
    (by rcases hremote with h | h <;> simp only [h] <;> tauto))
      ⟨x, hjdirect, hkdirect.symm⟩

/-- A positive canonical Case-4 source supplies the receiving strip in its
actual outgoing hull frame. The orientation premise identifies its retained
choice; no auxiliary receiver coordinates are assumed. -/
theorem SixBottomIndirectSource.forward_receiving_strip
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (available : Nonempty (SharedFiveCenterChoice p (assignments (v i) hid).context.q))
    (hR : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).right = v i)
    (hL : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).left = v (i + 1)) :
    -(1 / 2 : ℝ) ≤ (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re ∧
      (edgeCoordinate (p (v i)) (p (v (i + 1))) (p x)).re ≤ 3 / 2 := by
  classical
  obtain ⟨hid', hx, _hnot, _available, _hsix⟩ := hi
  have hproof : hid' = hid := Subsingleton.elim _ _
  subst hid'
  let aI := assignments (v i) hid
  let first := selectedSharedFiveCenter p aI.context.q available
  change first.right = v i at hR
  change first.left = v (i + 1) at hL
  have hxrule : 0 < aI.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hid, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aI] using hx
  have hxcharge : 0 < first.charge (v i) x := by
    simpa only [aI.rule.weight_eq_selected_sharedFive available x] using hxrule
  have hxsecond : 0 < first.selection.second.weight x := by
    simpa [SharedFiveCenterChoice.charge, ← hR, first.base.ne.symm] using hxcharge
  obtain ⟨hlo, hhi, _⟩ := first.selection.receivers_in_rectangle x (Or.inr hxsecond)
  have hne : p (v (i + 1)) ≠ p (v i) := by
    simpa only [hL, hR] using hp.ne first.base.ne
  rw [hL, hR] at hlo hhi
  rw [edgeCoordinate_swap_base (p (v (i + 1))) (p (v i)) (p x) hne]
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> linarith

/-- Every direct competitor in the partner-free forward normal form is at
one of just two indices. This quantifies over all direct rule classes. -/
theorem SixBottomIndirectSource.forward_direct_competitor_offset
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i j : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (available : Nonempty (SharedFiveCenterChoice p (assignments (v i) hid).context.q))
    (hR : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).right = v i)
    (hL : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).left = v (i + 1))
    (hjloc : ForwardCase4ResidualOffset i j)
    (hjdirect : (nearestGraph p).Adj (v j) x) :
    j = i - 1 ∨ j = (i + 1) + 1 := by
  obtain ⟨hxlo, hxhi⟩ := hi.forward_receiving_strip p hp v height assignments hid available hR hL
  have hbase : (nearestGraph p).Adj (v i) (v (i + 1)) := by
    simpa only [hR, hL] using
      (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).base.symm
  have hgood := (Finset.mem_filter.mp hid).2.1
  rcases hjloc with hm1 | hp2 | hm2 | hp3 | hm3
  · exact Or.inl hm1
  · exact Or.inr hp2
  all_goals
    exact False.elim ((tight_flat_remote_not_adj_of_receiving_strip
      p hn hp v hv hh hpos i hgood hbase x hxlo hxhi j (by tauto)) hjdirect)

/-- In a degree-five mixed overload every active Case-1/2/3 source is
direct. An indirect source is already known to have semantic Case 4. -/
theorem active_paper_cases123_direct_of_overload
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    (u : Fin n) (hud : u ∈ chargeDonors p (tightHullBadVertices p v))
    (hx : 0 < localPacketCharge p (tightHullBadVertices p v)
      (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x)
    (hcase : PaperCase1 p u (assignments u hud).context.q ∨
      PaperCase2 p u (assignments u hud).context.q ∨
      PaperCase3 p u (assignments u hud).context.q) :
    (nearestGraph p).Adj u x := by
  rcases active_source_direct_or_sixBottom p hp hn v hv hh hrange hsupport hpos
      height assignments x u hxdeg hover hdiam hud hx with hdirect | hindirect
  · exact hdirect.choose_spec.2
  · obtain ⟨hud', hfour⟩ := hindirect.paperCase4 p v height assignments
    have hproof : hud' = hud := Subsingleton.elim _ _
    subst hud'
    rcases hcase with hone | htwo | hthree
    · have h6 := hone.1
      have h5 := hfour.1
      omega
    · have h6 := htwo.1
      have h5 := hfour.1
      omega
    · obtain ⟨w, hwu, hqw, hwD⟩ := hfour.2
      exact False.elim (hwu (hthree.2 w hqw hwD))

/-- A forward Case-4 anchor cannot have two distinct direct competitors.
The only residual direct positions are three hull steps apart. -/
theorem SixBottomIndirectSource.forward_two_direct_competitors_impossible
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i j k : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (available : Nonempty (SharedFiveCenterChoice p (assignments (v i) hid).context.q))
    (hR : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).right = v i)
    (hL : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).left = v (i + 1))
    (hjloc : ForwardCase4ResidualOffset i j)
    (hkloc : ForwardCase4ResidualOffset i k)
    (hjk : j ≠ k)
    (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
    (hjdirect : (nearestGraph p).Adj (v j) x)
    (hkdirect : (nearestGraph p).Adj (v k) x) : False := by
  have hjoff := hi.forward_direct_competitor_offset p hn hp v hv hh hpos
    height assignments hid available hR hL hjloc hjdirect
  have hkoff := hi.forward_direct_competitor_offset p hn hp v hv hh hpos
    height assignments hid available hR hL hkloc hkdirect
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hremote : k = ((j + 1) + 1) + 1 ∨ k = ((j - 1) - 1) - 1 := by
    rcases hjoff with hjm | hjp <;> rcases hkoff with hkm | hkp
    · exact False.elim (hjk (hjm.trans hkm.symm))
    · left
      rw [hjm, hkp]
      abel
    · right
      rw [hjp, hkm]
      abel
    · exact False.elim (hjk (hjp.trans hkp.symm))
  exact (tight_flat_three_step_no_common_nearest p hp v hv hh ab hmin
    j hpos (Finset.mem_filter.mp hjd).2.1 (v k)
    (by rcases hremote with h | h <;> simp only [h] <;> tauto))
      ⟨x, hjdirect, hkdirect.symm⟩

/-- Negating cyclic indices exchanges the two residual orientation lists. -/
theorem BackwardCase4ResidualOffset.neg_forward
    {h : ℕ} [NeZero h] {i j : Fin h}
    (hj : BackwardCase4ResidualOffset i j) : ForwardCase4ResidualOffset (-i) (-j) := by
  rcases hj with hp1 | hp2 | hm2 | hp3 | hm3
  · exact Or.inl (by rw [hp1]; abel)
  · exact Or.inr (Or.inr (Or.inl (by rw [hp2]; abel)))
  · exact Or.inr (Or.inl (by rw [hm2]; abel))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [hp3]; abel))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hm3]; abel))))

/-- The same two-direct-source exclusion for the backward orientation.
Only geometric data are reflected; the actual assignments stay unchanged. -/
theorem SixBottomIndirectSource.backward_two_direct_competitors_impossible
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    {x : Fin n} {i j k : Fin h}
    (hi : SixBottomIndirectSource p v height assignments x (v i))
    (hid : v i ∈ chargeDonors p (tightHullBadVertices p v))
    (available : Nonempty (SharedFiveCenterChoice p (assignments (v i) hid).context.q))
    (hL : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).left = v i)
    (hR : (selectedSharedFiveCenter p (assignments (v i) hid).context.q available).right = v (i - 1))
    (hjloc : BackwardCase4ResidualOffset i j)
    (hkloc : BackwardCase4ResidualOffset i k)
    (hjk : j ≠ k)
    (hjd : v j ∈ chargeDonors p (tightHullBadVertices p v))
    (hjdirect : (nearestGraph p).Adj (v j) x)
    (hkdirect : (nearestGraph p).Adj (v k) x) : False := by
  classical
  obtain ⟨hid', hx, _hnot, _available, _hsix⟩ := hi
  have hproof : hid' = hid := Subsingleton.elim _ _
  subst hid'
  let aI := assignments (v i) hid
  let first := selectedSharedFiveCenter p aI.context.q available
  change first.right = v (i - 1) at hR
  change first.left = v i at hL
  have hxrule : 0 < aI.rule.packet.weight x := by
    simpa only [localPacketCharge, dite_eq_left hid, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet, aI] using hx
  have hxcharge : 0 < first.charge (v i) x := by
    simpa only [aI.rule.weight_eq_selected_sharedFive available x] using hxrule
  have hxfirst : 0 < first.selection.first.weight x := by
    simpa [SharedFiveCenterChoice.charge, ← hL, first.base.ne] using hxcharge
  obtain ⟨hxlo, hxhi, _⟩ := first.selection.receivers_in_rectangle x (Or.inl hxfirst)
  rw [hL, hR] at hxlo hxhi
  let pR : Fin n → Point := fun a => planeReflection (p a)
  let vR : Fin h → Fin n := reversedHullCycle v
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hvR : Function.Injective vR := reversedHullCycle_injective v hv
  have hG := nearestGraph_eq_of_dist_eq p pR (fun a b => planeReflection.dist_map (p a) (p b))
  have hposR : ∀ t, 0 < hullExteriorAngle pR vR t := by
    intro t
    simpa only [pR, vR, hullExteriorAngle_planeReflection_reversed] using hpos (-t)
  have hgoodR : vR (-i) ∉ tightHullBadVertices pR vR := by
    exact tightHull_not_bad_planeReflection_reversed p v hv (-i)
      (by simpa only [neg_neg] using (Finset.mem_filter.mp hid).2.1)
  have hjgoodR : vR (-j) ∉ tightHullBadVertices pR vR := by
    exact tightHull_not_bad_planeReflection_reversed p v hv (-j)
      (by simpa only [neg_neg] using (Finset.mem_filter.mp hjd).2.1)
  have hbaseR : (nearestGraph pR).Adj (vR (-i)) (vR (-i + 1)) := by
    simpa only [← hG, vR, reversedHullCycle_neg, reversedHullCycle_neg_successor,
      hL, hR] using first.base
  apply tight_flat_two_direct_competitors_impossible_of_strip
    pR hn hpR vR hvR hh hposR (-i) (-j) (-k) x hgoodR hjgoodR hbaseR
  · simpa only [pR, vR, reversedHullCycle_neg, reversedHullCycle_neg_successor,
      edgeCoordinate_planeReflection, Complex.conj_re] using hxlo
  · simpa only [pR, vR, reversedHullCycle_neg, reversedHullCycle_neg_successor,
      edgeCoordinate_planeReflection, Complex.conj_re] using hxhi
  · exact hjloc.neg_forward
  · exact hkloc.neg_forward
  · exact fun heq => hjk (neg_injective heq)
  · simpa only [← hG, vR, reversedHullCycle_neg] using hjdirect
  · simpa only [← hG, vR, reversedHullCycle_neg] using hkdirect

/-- Every actual three-source obstruction has a second indirect Case-4
source. Both orientations are covered, and every source belongs to the
original supporting family. -/
theorem supporting_case4_triple_has_second_indirect
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a)
    {i j k : Fin h} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v i))
    (hj : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x j)
    (hk : ActiveSupportingPaperFourWaySource
      p hp hn v hv hh hrange hsupport hpos x k)
    (hjo : j = i + 1 ∨ j = i - 1 ∨
      j = (i + 1) + 1 ∨ j = (i - 1) - 1 ∨
      j = ((i + 1) + 1) + 1 ∨ j = ((i - 1) - 1) - 1)
    (hko : k = i + 1 ∨ k = i - 1 ∨
      k = (i + 1) + 1 ∨ k = (i - 1) - 1 ∨
      k = ((i + 1) + 1) + 1 ∨ k = ((i - 1) - 1) - 1) :
    SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v j) ∨
    SixBottomIndirectSource p v (hullSupportingHeight p v)
      (supportingCertifiedDonorRules_of_tight_flat_hull
        p hp hn v hv hh hrange hsupport hpos) x (v k) := by
  let assignments := supportingCertifiedDonorRules_of_tight_flat_hull
    p hp hn v hv hh hrange hsupport hpos
  obtain ⟨hid, available, horient⟩ :=
    supporting_case4_anchor_partner_not_additional_source
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
      hij hik hjk hi hj hk hjo hko
  obtain ⟨hjd, hjpos, _⟩ := hj
  obtain ⟨hkd, hkpos, _⟩ := hk
  by_cases hjdirect : (nearestGraph p).Adj (v j) x
  · by_cases hkdirect : (nearestGraph p).Adj (v k) x
    · exfalso
      rcases horient with hforward | hbackward
      · exact hi.forward_two_direct_competitors_impossible
          p (by omega) hp v hv hh hpos (hullSupportingHeight p v) assignments
          hid available hforward.1.1 hforward.1.2
          (forward_residual_offset_of_local_ne_partner hjo hforward.2.1)
          (forward_residual_offset_of_local_ne_partner hko hforward.2.2)
          hjk hjd hjdirect hkdirect
      · exact hi.backward_two_direct_competitors_impossible
          p (by omega) hp v hv hh hpos (hullSupportingHeight p v) assignments
          hid available hbackward.1.1 hbackward.1.2
          (backward_residual_offset_of_local_ne_partner hjo hbackward.2.1)
          (backward_residual_offset_of_local_ne_partner hko hbackward.2.2)
          hjk hjd hjdirect hkdirect
    · right
      exact (sixBottomIndirectSource_iff_active_not_adj_of_degree_five_overload
        p hp hn v hv hh hrange hsupport hpos (hullSupportingHeight p v) assignments
        x hxdeg hover hdiam (v k)).2 ⟨hkd, hkpos, hkdirect⟩
  · left
    exact (sixBottomIndirectSource_iff_active_not_adj_of_degree_five_overload
      p hp hn v hv hh hrange hsupport hpos (hullSupportingHeight p v) assignments
      x hxdeg hover hdiam (v j)).2 ⟨hjd, hjpos, hjdirect⟩

/-- Unconditional reduction of a hypothetical shallow overload to two
distinct actual six-bottom indirect sources and a third actual active source.
In particular, an anchor with two Case-1/2/3 competitors is impossible. -/
theorem supporting_family_overload_has_two_indirect_sources
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (x : Fin n) (hxdeg : (nearestGraph p).degree x = 5)
    (hover : 2 * (6 - (nearestGraph p).degree x) <
      ∑ w ∈ chargeDonors p (tightHullBadVertices p v),
        localPacketCharge p (tightHullBadVertices p v)
          (certifiedFamilyPackets p (tightHullBadVertices p v)
            (hullSupportingHeight p v)
            (supportingCertifiedDonorRules_of_tight_flat_hull
              p hp hn v hv hh hrange hsupport hpos)) w x)
    (hdiam : ∃ a, a ∈ diameterEndpoints p ∧ (nearestGraph p).Adj x a) :
    ∃ i j k : Fin h, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      SixBottomIndirectSource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x (v i) ∧
      SixBottomIndirectSource p v (hullSupportingHeight p v)
        (supportingCertifiedDonorRules_of_tight_flat_hull
          p hp hn v hv hh hrange hsupport hpos) x (v j) ∧
      ActiveSupportingPaperFourWaySource
        p hp hn v hv hh hrange hsupport hpos x k := by
  obtain ⟨i, j, k, hij, hik, hjk, hi, _horient, hj, hk, hjo, hko⟩ :=
    supporting_family_degree_five_overload_has_lossless_case4_triple
      p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
  have hsecond := supporting_case4_triple_has_second_indirect
    p hp hn v hv hh hrange hsupport hpos x hxdeg hover hdiam
    hij hik hjk hi hj hk hjo hko
  rcases hsecond with hjind | hkind
  · exact ⟨i, j, k, hij, hik, hjk, hi, hjind, hk⟩
  · exact ⟨i, k, j, hik, hij, hjk.symm, hi, hkind, hj⟩

end Erdos957
