import DonorCases

/-! Certified choices for a center having a unique diameter endpoint neighbor.
The supplied score selects a maximum among common neighbors in the five-degree
branch. No assertion identifies this restricted maximum with the paper's
highest neighbor among all neighbors of the center. -/

namespace Erdos957

/-- A central packet retaining its rule, actual sites, unique-endpoint
condition and direct donor adjacency. In degree six the two sites are sorted
by the supplied score; this ordering alone does not assert a geometric side. -/
structure CertifiedCentralPacket {n : ℕ} (p : Fin n → Point)
    (u q : Fin n) (height : Fin n → ℝ) where
  packet : LocalChargePacket p u
  unique : UniqueD p u q
  central_adj : (nearestGraph p).Adj u q
  rule :
    ((nearestGraph p).degree q ≤ 4 ∧ packet.left = q ∧ packet.right = q) ∨
    ((nearestGraph p).degree q = 5 ∧ packet.left = q ∧
      (nearestGraph p).Adj u packet.right ∧
      (nearestGraph p).Adj q packet.right ∧
      ∀ a, (nearestGraph p).Adj u a → (nearestGraph p).Adj q a →
        height a ≤ height packet.right) ∨
    ((nearestGraph p).degree q = 6 ∧ packet.left ≠ packet.right ∧
      (nearestGraph p).Adj u packet.left ∧
      (nearestGraph p).Adj q packet.left ∧
      (nearestGraph p).Adj u packet.right ∧
      (nearestGraph p).Adj q packet.right ∧
      height packet.left ≤ height packet.right)
  positive_adj : ∀ x, 0 < packet.weight x → (nearestGraph p).Adj u x

private theorem positive_packet_eq_site {n : ℕ} {p : Fin n → Point}
    {u x : Fin n} (packet : LocalChargePacket p u)
    (hx : 0 < packet.weight x) : x = packet.left ∨ x = packet.right := by
  by_cases hl : x = packet.left
  · exact Or.inl hl
  by_cases hr : x = packet.right
  · exact Or.inr hr
  simp [LocalChargePacket.weight, hl, hr] at hx

/-- Every actual donor context with a unique diameter endpoint at its center
has a certified choice. Classical choice returns the full certified structure. -/
noncomputable def certifiedCentralPacket_of_uniqueD {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u : Fin n}
    (ctx : DonorContext p bad u) (hunique : UniqueD p u ctx.q)
    (height : Fin n → ℝ) : CertifiedCentralPacket p u ctx.q height := by
  classical
  apply Classical.choice
  have hout (a : Fin n) (hua : (nearestGraph p).Adj u a)
      (hqa : (nearestGraph p).Adj ctx.q a) : a ∉ diameterEndpoints p := by
    intro haD
    exact hua.ne (hunique a hqa haD).symm
  by_cases hlow : (nearestGraph p).degree ctx.q ≤ 4
  · let packet := localChargePacket_of_low_degree_neighbor p
      ctx.central_adj ctx.central_outside hlow
    refine ⟨{
      packet := packet
      unique := hunique
      central_adj := ctx.central_adj
      rule := Or.inl ⟨hlow, rfl, rfl⟩
      positive_adj := ?_
    }⟩
    intro x hx
    rcases positive_packet_eq_site packet hx with hx | hx
    all_goals simpa only [hx, packet, localChargePacket_of_low_degree_neighbor]
      using ctx.central_adj
  by_cases hfive : (nearestGraph p).degree ctx.q = 5
  · let S := (nearestGraph p).neighborFinset u ∩ (nearestGraph p).neighborFinset ctx.q
    have hSne : S.Nonempty := by
      obtain ⟨a, hua, hqa⟩ := degree_five_central_neighbor_has_common_neighbor
        p hn hp ctx.diameter_adj ctx.degree_three ctx.central_adj
        ctx.central_lo ctx.central_hi hfive
      exact ⟨a, Finset.mem_inter.mpr
        ⟨((nearestGraph p).mem_neighborFinset u a).mpr hua,
          ((nearestGraph p).mem_neighborFinset ctx.q a).mpr hqa⟩⟩
    obtain ⟨a, ha, hmax⟩ := S.exists_max_image height hSne
    have hua := ((nearestGraph p).mem_neighborFinset u a).mp (Finset.mem_inter.mp ha).1
    have hqa := ((nearestGraph p).mem_neighborFinset ctx.q a).mp (Finset.mem_inter.mp ha).2
    have hadeg := common_neighbor_degree_le_five_of_central p hn hp
      ctx.diameter_adj ctx.central_adj ctx.central_lo ctx.central_hi hua hqa
    let packet : LocalChargePacket p u := {
      left := ctx.q
      right := a
      left_outside := ctx.central_outside
      right_outside := hout a hua hqa
      left_degree := hfive.le
      right_degree := hadeg
      repeated_degree := fun heq => False.elim (hqa.ne heq)
      left_reachable := Or.inl ctx.central_adj
      right_reachable := Or.inl hua
    }
    refine ⟨{
      packet := packet
      unique := hunique
      central_adj := ctx.central_adj
      rule := Or.inr (Or.inl ⟨hfive, rfl, hua, hqa, ?_⟩)
      positive_adj := ?_
    }⟩
    · intro b hub hqb
      exact hmax b (Finset.mem_inter.mpr
        ⟨((nearestGraph p).mem_neighborFinset u b).mpr hub,
          ((nearestGraph p).mem_neighborFinset ctx.q b).mpr hqb⟩)
    · intro x hx
      rcases positive_packet_eq_site packet hx with hx | hx
      · simpa only [hx] using ctx.central_adj
      · simpa only [hx] using hua
  have hsix : (nearestGraph p).degree ctx.q = 6 := by
    have := ctx.central_degree_le_six
    omega
  obtain ⟨a, b, hab, hua, hqa, hadeg, hub, hqb, hbdeg⟩ :=
    diameterEndpoint_six_neighbor_common_degree_bounds
      p hn hp ctx.endpoint ctx.central_adj hsix
  have make (a b : Fin n) (hab : a ≠ b)
      (hua : (nearestGraph p).Adj u a) (hqa : (nearestGraph p).Adj ctx.q a)
      (hadeg : (nearestGraph p).degree a ≤ 5)
      (hub : (nearestGraph p).Adj u b) (hqb : (nearestGraph p).Adj ctx.q b)
      (hbdeg : (nearestGraph p).degree b ≤ 5) (horder : height a ≤ height b) :
      Nonempty (CertifiedCentralPacket p u ctx.q height) := by
    let packet : LocalChargePacket p u := {
      left := a
      right := b
      left_outside := hout a hua hqa
      right_outside := hout b hub hqb
      left_degree := hadeg
      right_degree := hbdeg
      repeated_degree := fun heq => False.elim (hab heq)
      left_reachable := Or.inl hua
      right_reachable := Or.inl hub
    }
    refine ⟨{
      packet := packet
      unique := hunique
      central_adj := ctx.central_adj
      rule := Or.inr (Or.inr ⟨hsix, hab, hua, hqa, hub, hqb, horder⟩)
      positive_adj := ?_
    }⟩
    intro x hx
    rcases positive_packet_eq_site packet hx with hx | hx
    · simpa only [hx] using hua
    · simpa only [hx] using hub
  rcases le_total (height a) (height b) with haborder | hbaorder
  · exact make a b hab hua hqa hadeg hub hqb hbdeg haborder
  · exact make b a hab.symm hub hqb hbdeg hua hqa hadeg hbaorder

/-- A positive transfer of a certified central packet travels exactly one
minimum distance, since each retained site is directly donor-adjacent. -/
theorem CertifiedCentralPacket.positive_dist_eq_min {n : ℕ}
    {p : Fin n → Point} {u q x : Fin n} {height : Fin n → ℝ}
    (choice : CertifiedCentralPacket p u q height)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    (hx : 0 < choice.packet.weight x) :
    dist (p u) (p x) = pairDist p ij :=
  nearestGraph_adj_dist_eq p hmin (choice.positive_adj x hx)

/-- In coordinates normalized by the central nearest edge, every positive
receiver is on the unit circle. This frame is the central edge's frame. -/
theorem CertifiedCentralPacket.positive_central_coordinate_norm {n : ℕ}
    {p : Fin n → Point} (hn : 2 ≤ n) (hp : Function.Injective p)
    {u q x : Fin n} {height : Fin n → ℝ}
    (choice : CertifiedCentralPacket p u q height)
    (hx : 0 < choice.packet.weight x) :
    ‖edgeCoordinate (p u) (p q) (p x)‖ = 1 := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  rw [edgeCoordinate_norm _ _ _ (hp.ne choice.central_adj.ne),
    choice.positive_dist_eq_min hmin hx,
    nearestGraph_adj_dist_eq p hmin choice.central_adj, div_self hr.ne']

/-- The retained donor adjacency gives a coordinate square without assuming
an unproved supporting-frame or receiver-locality property. -/
theorem CertifiedCentralPacket.positive_central_coordinate_square {n : ℕ}
    {p : Fin n → Point} (hn : 2 ≤ n) (hp : Function.Injective p)
    {u q x : Fin n} {height : Fin n → ℝ}
    (choice : CertifiedCentralPacket p u q height)
    (hx : 0 < choice.packet.weight x) :
    |(edgeCoordinate (p u) (p q) (p x)).re| ≤ 1 ∧
      |(edgeCoordinate (p u) (p q) (p x)).im| ≤ 1 := by
  have hnorm := choice.positive_central_coordinate_norm hn hp hx
  constructor
  · simpa only [hnorm] using Complex.abs_re_le_norm (edgeCoordinate (p u) (p q) (p x))
  · simpa only [hnorm] using Complex.abs_im_le_norm (edgeCoordinate (p u) (p q) (p x))

end Erdos957
