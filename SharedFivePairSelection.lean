import SharedFiveCharge
import DeepestSharedFiveGeometry
import SharedFiveReceiverRegion
import DeepestNeighborHeight

/-! Coordinated shared-five packet choices. The selected type retains the
minimum-height rule, receiver ordering and actual geometric region. These
certificates do not assert compatibility with other boundary pairs. -/

namespace Erdos957

/-- One joint choice for both endpoints of a shared-five triangle. The
coordinate origin is `u`, with `w` at 1 and the configuration below the axis.
The names `first` and `second` refer to the two donors, not packet slots. -/
structure SharedFivePairSelection {n : ℕ} (p : Fin n → Point)
    (u w q : Fin n) where
  bottom : Fin n
  bottom_adj : (nearestGraph p).Adj q bottom
  bottom_ne_left : bottom ≠ u
  bottom_ne_right : bottom ≠ w
  bottom_minimal : ∀ a, (nearestGraph p).Adj q a → a ≠ u → a ≠ w →
    (edgeCoordinate (p u) (p w) (p bottom)).im ≤
      (edgeCoordinate (p u) (p w) (p a)).im
  bottom_depth : (edgeCoordinate (p u) (p w) (p bottom)).im ≤ -Real.sqrt 3
  diameter_neighbors : ∀ a, (nearestGraph p).Adj q a →
    a ∈ diameterEndpoints p → a = u ∨ a = w
  first : LocalChargePacket p u
  second : LocalChargePacket p w
  first_central : first.left = q
  second_central : second.left = q
  first_secondary : (nearestGraph p).Adj q first.right ∧
    first.right ≠ u ∧ first.right ≠ w
  second_secondary : (nearestGraph p).Adj q second.right ∧
    second.right ≠ u ∧ second.right ≠ w
  branch : ((nearestGraph p).degree bottom ≤ 5 ∧
      first.right = bottom ∧ second.right = bottom) ∨
    ((nearestGraph p).degree bottom = 6 ∧ first.right ≠ second.right ∧
      (nearestGraph p).Adj bottom first.right ∧
      (nearestGraph p).Adj bottom second.right ∧
      (edgeCoordinate (p u) (p w) (p first.right)).re ≤
        (edgeCoordinate (p u) (p w) (p second.right)).re)
  receivers_in_rectangle : ∀ k, 0 < first.weight k ∨ 0 < second.weight k →
    -(1 / 2 : ℝ) ≤ (edgeCoordinate (p u) (p w) (p k)).re ∧
      (edgeCoordinate (p u) (p w) (p k)).re ≤ 3 / 2 ∧
      -2 ≤ (edgeCoordinate (p u) (p w) (p k)).im ∧
      (edgeCoordinate (p u) (p w) (p k)).im ≤ 0

private theorem positive_packet_eq_site {n : ℕ} {p : Fin n → Point}
    {u k q a : Fin n} (packet : LocalChargePacket p u)
    (hl : packet.left = q) (hr : packet.right = a)
    (hk : 0 < packet.weight k) : k = q ∨ k = a := by
  by_cases hkq : k = q
  · exact Or.inl hkq
  by_cases hka : k = a
  · exact Or.inr hka
  simp [LocalChargePacket.weight, hl, hr, hkq, hka] at hk

/-- The actual span supplies receiver exclusion; all selection and geometry
certificates are retained in the result of classical choice. In the six-degree
branch the two donors receive different, horizontally ordered common sites. -/
noncomputable def sharedFivePairSelection_of_hull_span {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q j : Fin n}
    (hqu : (nearestGraph p).Adj q u) (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hqdeg : (nearestGraph p).degree q = 5)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k))
    (hdiam : (diameterGraph p).Adj u j)
    (hscale : 10 * dist (p u) (p w) < dist (p u) (p j))
    (span : NormalizedHullSpan p u w) : SharedFivePairSelection p u w q := by
  classical
  apply Classical.choice
  let S := (nearestGraph p).neighborFinset q \ {u, w}
  have hSne : S.Nonempty := by
    have hc : ({u, w} : Finset (Fin n)).card <
        ((nearestGraph p).neighborFinset q).card := by
      rw [(nearestGraph p).card_neighborFinset_eq_degree, hqdeg]
      simp [huw.ne]
    obtain ⟨a, ha, hanot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨a, Finset.mem_sdiff.mpr ⟨ha, hanot⟩⟩
  obtain ⟨t, ht, htmin⟩ := S.exists_min_image
    (fun a => (edgeCoordinate (p u) (p w) (p a)).im) hSne
  have hqt := ((nearestGraph p).mem_neighborFinset q t).mp
    (Finset.mem_sdiff.mp ht).1
  have htne : t ≠ u ∧ t ≠ w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      (Finset.mem_sdiff.mp ht).2
  have hminimal (a : Fin n) (hqa : (nearestGraph p).Adj q a)
      (hau : a ≠ u) (haw : a ≠ w) :
      (edgeCoordinate (p u) (p w) (p t)).im ≤
        (edgeCoordinate (p u) (p w) (p a)).im := by
    apply htmin a
    exact Finset.mem_sdiff.mpr ⟨((nearestGraph p).mem_neighborFinset q a).mpr hqa,
      by simp [hau, haw]⟩
  have hqout : q ∉ diameterEndpoints p := by
    intro hq
    have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp q hq
    omega
  have hout (a : Fin n) (hqa : (nearestGraph p).Adj q a)
      (hau : a ≠ u) (haw : a ≠ w) : a ∉ diameterEndpoints p :=
    shared_triangle_other_neighbor_not_diameter p hn hp hqu hqw huw hqa
      hau haw hsupport hdiam hscale span
  let packet (src : Fin n) (hsrc : (nearestGraph p).Adj q src)
      (a : Fin n) (hqa : (nearestGraph p).Adj q a)
      (hau : a ≠ u) (haw : a ≠ w) (hadeg : (nearestGraph p).degree a ≤ 5) :
      LocalChargePacket p src := {
    left := q
    right := a
    left_outside := hqout
    right_outside := hout a hqa hau haw
    left_degree := hqdeg.le
    right_degree := hadeg
    repeated_degree := fun heq => False.elim (hqa.ne heq)
    left_reachable := Or.inl hsrc.symm
    right_reachable := Or.inr ⟨q, hsrc.symm, hqa⟩
  }
  have makePair (a b : Fin n)
      (hqa : (nearestGraph p).Adj q a) (hqb : (nearestGraph p).Adj q b)
      (hane : a ≠ u ∧ a ≠ w) (hbne : b ≠ u ∧ b ≠ w)
      (hadeg : (nearestGraph p).degree a ≤ 5)
      (hbdeg : (nearestGraph p).degree b ≤ 5)
      (hcase : ((nearestGraph p).degree t ≤ 5 ∧ a = t ∧ b = t) ∨
        ((nearestGraph p).degree t = 6 ∧ a ≠ b ∧
          (nearestGraph p).Adj t a ∧ (nearestGraph p).Adj t b ∧
          (edgeCoordinate (p u) (p w) (p a)).re ≤
            (edgeCoordinate (p u) (p w) (p b)).re)) :
      Nonempty (SharedFivePairSelection p u w q) := by
    refine ⟨{
      bottom := t
      bottom_adj := hqt
      bottom_ne_left := htne.1
      bottom_ne_right := htne.2
      bottom_minimal := hminimal
      bottom_depth := shared_five_deepest_neighbor_height
        p hn hp hqu hqw huw hqdeg hsupport hminimal
      diameter_neighbors := ?_
      first := packet u hqu a hqa hane.1 hane.2 hadeg
      second := packet w hqw b hqb hbne.1 hbne.2 hbdeg
      first_central := rfl
      second_central := rfl
      first_secondary := ⟨hqa, hane⟩
      second_secondary := ⟨hqb, hbne⟩
      branch := hcase
      receivers_in_rectangle := ?_
    }⟩
    · intro k hqk hkD
      by_cases hku : k = u
      · exact Or.inl hku
      by_cases hkw : k = w
      · exact Or.inr hkw
      exact False.elim (hout k hqk hku hkw hkD)
    ·
      intro k hk
      apply shared_triangle_neighbor_receiver_rectangle p hn hp hqu hqw huw hsupport
      rcases hk with hk | hk
      · rcases positive_packet_eq_site (packet u hqu a hqa hane.1 hane.2 hadeg)
          rfl rfl hk with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨hqa, hane⟩
      · rcases positive_packet_eq_site (packet w hqw b hqb hbne.1 hbne.2 hbdeg)
          rfl rfl hk with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨hqb, hbne⟩
  by_cases htlow : (nearestGraph p).degree t ≤ 5
  · exact makePair t t hqt hqt htne htne htlow htlow (Or.inl ⟨htlow, rfl, rfl⟩)
  have htdeg : (nearestGraph p).degree t = 6 := by
    have := nearestGraph_degree_le_six p hn hp t
    omega
  obtain ⟨a, b, hab, hqa, hta, hadeg, hqb, htb, hbdeg⟩ :=
    shared_five_diameter_triangle_two_low_common_neighbors
      p hn hp hqdeg htdeg hqt hqu hqw huw hu hw
  have hane := shared_five_six_neighbor_ne_diameter_triangle_endpoints
    p hn hp hu hw hqdeg htdeg hqu hqw huw hta
  have hbne := shared_five_six_neighbor_ne_diameter_triangle_endpoints
    p hn hp hu hw hqdeg htdeg hqu hqw huw htb
  by_cases habre : (edgeCoordinate (p u) (p w) (p a)).re ≤
      (edgeCoordinate (p u) (p w) (p b)).re
  · exact makePair a b hqa hqb hane hbne hadeg hbdeg
      (Or.inr ⟨htdeg, hab, hta, htb, habre⟩)
  · exact makePair b a hqb hqa hbne hane hbdeg hadeg
      (Or.inr ⟨htdeg, hab.symm, htb, hta, le_of_not_ge habre⟩)

/-- Actual tight-flat hull data construct the coordinated choice without
assuming a shallow span or a scale inequality. Only the current endpoint
needs a nonexceptional neighborhood; the partner need not be a donor. -/
noncomputable def sharedFivePairSelection_of_tight_flat_hull
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (q : Fin n)
    (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (hqu : (nearestGraph p).Adj q (v (i + 1)))
    (hqw : (nearestGraph p).Adj q (v i))
    (hqdeg : (nearestGraph p).degree q = 5)
    (hgood : v i ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) (hw : v i ∈ diameterEndpoints p) :
    SharedFivePairSelection p (v (i + 1)) (v i) q := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i + 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega)
  have hscale : 10 * dist (p (v (i + 1))) (p (v i)) <
      dist (p (v (i + 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨sharedFivePairSelection_of_hull_span p (by omega) hp hqu hqw hbase.symm
    hqdeg hu hw (hsupport i) hdiam hscale
    (normalizedHullSpan_of_tight_flat_vertex p (by omega) hp v hv hh i hbase
      (hsupport i) hpos hgood)⟩

/-- The combined two-donor packet always respects each receiver's capacity
for this pair alone. Contributions from all other donors remain to be bounded. -/
theorem SharedFivePairSelection.pair_weight_le_capacity {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedFivePairSelection p u w q) (x : Fin n) :
    choice.first.weight x + choice.second.weight x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have hfirst := choice.first.weight_le_degree_slack x
  have hsecond := choice.second.weight_le_degree_slack x
  omega

/-- Both donors send exactly one half-unit to the shared central vertex. -/
theorem SharedFivePairSelection.central_weight {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedFivePairSelection p u w q) :
    choice.first.weight q = 1 ∧ choice.second.weight q = 1 := by
  constructor
  · simp [LocalChargePacket.weight, choice.first_central,
      choice.first_secondary.1.ne]
  · simp [LocalChargePacket.weight, choice.second_central,
      choice.second_secondary.1.ne]

/-- When the bottom neighbor has degree six, any noncentral receiver gets
at most one half-unit from the coordinated pair, because its sites differ. -/
theorem SharedFivePairSelection.noncentral_weight_le_one {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedFivePairSelection p u w q)
    (hbottom : (nearestGraph p).degree choice.bottom = 6)
    (x : Fin n) (hx : x ≠ q) :
    choice.first.weight x + choice.second.weight x ≤ 1 := by
  have hdistinct : choice.first.right ≠ choice.second.right := by
    rcases choice.branch with hlow | hhigh
    · omega
    · exact hhigh.2.1
  by_cases hfirst : x = choice.first.right
  · have hsecond : x ≠ choice.second.right := fun h => hdistinct (hfirst.symm.trans h)
    simp only [LocalChargePacket.weight, choice.first_central, choice.second_central,
      ite_eq_right hx, ite_eq_left hfirst, ite_eq_right hsecond]
    norm_num
  · by_cases hsecond : x = choice.second.right
    · simp only [LocalChargePacket.weight, choice.first_central, choice.second_central,
        ite_eq_right hx, ite_eq_right hfirst, ite_eq_left hsecond]
      norm_num
    · simp only [LocalChargePacket.weight, choice.first_central, choice.second_central,
        ite_eq_right hx, ite_eq_right hfirst, ite_eq_right hsecond]
      norm_num

end Erdos957
