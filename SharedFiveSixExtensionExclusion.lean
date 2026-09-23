import ReflectedSharedSixLowerExclusion
import FlatCentralProjection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Coordinate lemmas for the shared-five bottom and shared-six second
extension receiver. All bounds retain their geometric hypotheses. -/

namespace Erdos957

open scoped ComplexConjugate

private theorem extension_norm_sq (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z


/-- Affine change of normalized edge coordinates.  The point `x` is first
written in the frame based at `a → b`, and then transported to the frame
based at `u → v`. -/
private theorem edgeCoordinate_affine_base_change (u v a b x : Point)
    (huv : u ≠ v) (hab : a ≠ b) :
    edgeCoordinate u v x =
      edgeCoordinate u v a + edgeCoordinate a b x *
        (edgeCoordinate u v b - edgeCoordinate u v a) := by
  have huvC : pointToComplex (v - u) ≠ 0 := by
    intro hz
    have hsub : v - u = 0 := pointToComplex.injective (by simpa using hz)
    exact huv (sub_eq_zero.mp hsub).symm
  have habC : pointToComplex (b - a) ≠ 0 := by
    intro hz
    have hsub : b - a = 0 := pointToComplex.injective (by simpa using hz)
    exact hab (sub_eq_zero.mp hsub).symm
  have hdiff :
      edgeCoordinate u v x - edgeCoordinate u v a =
        edgeCoordinate a b x *
          (edgeCoordinate u v b - edgeCoordinate u v a) := by
    rw [edgeCoordinate_sub, edgeCoordinate_sub]
    simp only [edgeCoordinate]
    field_simp [huvC, habC]
  calc
    edgeCoordinate u v x = edgeCoordinate u v a +
        (edgeCoordinate u v x - edgeCoordinate u v a) := by ring
    _ = edgeCoordinate u v a + edgeCoordinate a b x *
        (edgeCoordinate u v b - edgeCoordinate u v a) := by rw [hdiff]

/-- A supported shared-five center has the same lower equilateral coordinate
as any other supported unit triangle, with a prescribed positive algebraic
height satisfying `h² = 3/4`.  This is the frame-conversion ingredient needed
to feed an actual shared-five configuration into the scalar extension
obstruction. -/
theorem SharedFiveCenterChoice.center_coordinate_with_height {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q : Fin n} (five : SharedFiveCenterChoice p q)
    (h : ℝ) (hh : 0 < h) (hsq : h ^ 2 = 3 / 4) :
    edgeCoordinate (p five.left) (p five.right) (p q) =
      (1 / 2 : ℂ) - (h : ℂ) * Complex.I := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hne : p five.left ≠ p five.right := hp.ne five.base.ne
  let z := edgeCoordinate (p five.left) (p five.right) (p q)
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [edgeCoordinate_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p hmin five.center_left.symm,
      nearestGraph_adj_dist_eq p hmin five.base, div_self hδ.ne']
  have hz1 : ‖z - 1‖ = 1 := by
    dsimp [z]
    rw [edgeCoordinate_sub_one_norm _ _ _ hne,
      nearestGraph_adj_dist_eq p hmin five.center_right.symm,
      nearestGraph_adj_dist_eq p hmin five.base, div_self hδ.ne']
  have hbelow : z.im ≤ 0 := by
    dsimp [z]
    exact edgeCoordinate_im_nonpos_of_support _ _ _ hne (five.support q)
  obtain ⟨h', hh', hsq', hzcoord⟩ :=
    unit_triangle_below_real_axis z hz hz1 hbelow
  have heq : h' = h := by
    nlinarith only [hh, hh', hsq, hsq']
  simpa only [heq] using hzcoord

/-- If a retained shared-six packet sends its second unit to a degree-five
receiver that is not the first lower site, then that receiver is exactly the
second extension `t₂`, with all of the actual rule witnesses retained. -/
theorem SharedSixPacketChoice.degree_five_right_second_extension_data {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : SharedSixPacketChoice p u w q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower) :
    ∃ t₂ : Fin n,
      choice.packet.right = t₂ ∧
        (nearestGraph p).degree choice.lower = 6 ∧
        (nearestGraph p).Adj choice.lower t₂ ∧
        (nearestGraph p).Adj choice.outer t₂ ∧
        p q + p t₂ = p choice.lower + p choice.outer ∧
        edgeCoordinate (p u) (p w) (p t₂) =
          (2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I ∧
        (nearestGraph p).degree t₂ ≤ 5 := by
  rcases choice.branch with ⟨_, hright⟩ | ⟨hlower, t₂, hlt₂, hot₂, hsum, hcoord, hcases⟩
  · exact False.elim (hnot_lower hright)
  rcases hcases with ⟨ht₂low, hright⟩ | ⟨_, _, _, _, hfour⟩
  · exact ⟨t₂, hright, hlower, hlt₂, hot₂, hsum, hcoord, ht₂low⟩
  · omega

/-- Reflected version of `degree_five_right_second_extension_data`, stated in
the original coordinates of the retained reflected shared-six packet. -/
theorem ReflectedSharedSixPacketChoice.degree_five_right_second_extension_data {n : ℕ}
    {p : Fin n → Point} {u w q : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.reflected.lower) :
    ∃ t₂ : Fin n,
      choice.packet.right = t₂ ∧
        (nearestGraph p).degree choice.reflected.lower = 6 ∧
        (nearestGraph p).Adj choice.reflected.lower t₂ ∧
        (nearestGraph p).Adj choice.reflected.outer t₂ ∧
        p q + p t₂ = p choice.reflected.lower + p choice.reflected.outer ∧
        edgeCoordinate (p u) (p w) (p t₂) =
          (2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I ∧
        (nearestGraph p).degree t₂ ≤ 5 := by
  rcases choice.receiver_rule with ⟨_, hright⟩ |
    ⟨hlower, t₂, hlt₂, hot₂, hsum, hcoord, hcases⟩
  · exact False.elim (hnot_lower hright)
  rcases hcases with ⟨ht₂low, hright⟩ | ⟨_, _, _, _, hfour⟩
  · exact ⟨t₂, hright, hlower, hlt₂, hot₂, hsum, hcoord, ht₂low⟩
  · omega

/-- In the actual oriented hull, a forward shared-six certificate based at a
diameter partner of `v i` necessarily uses the successor `v (i+1)`, not the
predecessor.  The predecessor alternative would put the certified lower
equilateral center strictly below a hull edge whose support inequality puts
all configuration points on the opposite side. -/
theorem SharedSixPacketChoice.partner_eq_successor {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q) :
    partner = v (i + 1) := by
  have hwhere := nearest_diameter_endpoints_cyclic_adjacent_of_large_card
    p hp hn v hv hh hrange hsupport i partner ctx.endpoint choice.partner_diameter
      choice.base.symm
  rcases hwhere with hnext | hprev
  · exact hnext
  · subst partner
    have hind : v (i - 1) ≠ v i := hv.ne (by
      simpa only [sub_add_cancel] using (cyclic_three_distinct hh (i - 1)).1)
    have hne : p (v (i - 1)) ≠ p (v i) := hp.ne hind
    have him := edgeCoordinate_im_mul_dist_sq
      (p (v (i - 1))) (p (v i)) (p ctx.q) hne
    rw [choice.center_coordinate] at him
    norm_num [Complex.mul_im] at him
    have hs : 0 ≤ turn (p (v (i - 1))) (p (v i)) (p ctx.q) := by
      simpa only [sub_add_cancel] using hsupport (i - 1) ctx.q
    have hsq : 0 < dist (p (v (i - 1))) (p (v i)) ^ 2 :=
      sq_pos_of_pos (dist_pos.mpr hne)
    nlinarith only [him, hs, hsq, choice.height_pos]


/-- The supporting orientation of a retained shared-five pair fixes its order
in the actual hull cycle: once the right endpoint is `v j`, the left endpoint
is exactly the successor. -/
theorem SharedFiveCenterChoice.left_eq_cyclic_successor_of_right {n h : ℕ}
    [NeZero h] (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    {q : Fin n} (five : SharedFiveCenterChoice p q) (j : Fin h)
    (hright : five.right = v j) :
    five.left = v (j + 1) := by
  have hleftHull : five.left ∈ hullVertexIndices p :=
    diameterEndpoints_subset_hullVertexIndices p hp five.left_diameter
  have hleftne : five.left ≠ v j := by
    intro heq
    exact five.base.ne (heq.trans hright.symm)
  apply supporting_hull_chord_eq_successor p hp v hv hh hrange hsupport
    j five.left hleftHull hleftne
  intro k
  simpa only [← hright] using five.support k


/-- The degree-three shared-six source has exactly the three retained nearest
neighbors: its diameter partner, the common center, and the outer site.  This
packages a repeatedly needed consequence of the source degree certificate. -/
theorem SharedSixPacketChoice.source_neighbor_cases_of_context {n h : ℕ}
    [NeZero h] (p : Fin n → Point) (hp : Function.Injective p)
    (i : Fin h) (v : Fin h → Fin n)
    (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner : Fin n) (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (k : Fin n) (hk : (nearestGraph p).Adj (v i) k) :
    k = partner ∨ k = ctx.q ∨ k = choice.outer := by
  classical
  have hn : 2 ≤ n := by
    have hlt := mem_pairs_iff.mp ctx.minPair_spec.1
    have hbound := ctx.minPair.2.isLt
    omega
  have hpq : partner ≠ ctx.q :=
    (choice.center_adj_partner hn hp).ne.symm
  have hqo : ctx.q ≠ choice.outer := choice.outer_adj_center.ne
  have hpo : partner ≠ choice.outer := by
    intro heq
    have hc := congrArg Complex.re choice.outer_coordinate
    rw [← heq, edgeCoordinate_self] at hc
    norm_num [Complex.mul_re] at hc
  have hsub : ({partner, ctx.q, choice.outer} : Finset (Fin n)) ⊆
      (nearestGraph p).neighborFinset (v i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x
      exact ((nearestGraph p).mem_neighborFinset (v i) partner).mpr choice.base.symm
    · subst x
      exact ((nearestGraph p).mem_neighborFinset (v i) ctx.q).mpr ctx.central_adj
    · subst x
      exact ((nearestGraph p).mem_neighborFinset (v i) choice.outer).mpr
        choice.outer_adj_source
  have hcard : ({partner, ctx.q, choice.outer} : Finset (Fin n)).card = 3 := by
    simp [hpq, hpo, hqo]
  have hseteq : ({partner, ctx.q, choice.outer} : Finset (Fin n)) =
      (nearestGraph p).neighborFinset (v i) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [(nearestGraph p).card_neighborFinset_eq_degree, ctx.degree_three, hcard]
  have hmem : k ∈ ({partner, ctx.q, choice.outer} : Finset (Fin n)) := by
    rw [hseteq]
    exact ((nearestGraph p).mem_neighborFinset (v i) k).mpr hk
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- A retained shared-five left endpoint is strictly farther than one minimum
edge from the shared-six source.  The only three nearest neighbors of the
source are already occupied by the shared-six partner, center and outer site;
the partner alternative would force the same supported unit base and hence
identify the degree-five and degree-six centers. -/
theorem SharedSixPacketChoice.sharedFive_left_strict_source_distance
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n)
    (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (five : SharedFiveCenterChoice p qfive) :
    1 < ‖edgeCoordinate (p partner) (p (v i)) (p five.left) - 1‖ := by
  have hpartner : partner = v (i + 1) :=
    choice.partner_eq_successor p hp hn v hv hh hrange hsupport i ctx
  subst partner
  have hne : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have houterD : choice.outer ∉ diameterEndpoints p := by
    simpa only [choice.packet_left] using choice.packet.left_outside

  have hleftNotAdj : ¬ (nearestGraph p).Adj (v i) five.left := by
    intro hadj
    rcases choice.source_neighbor_cases_of_context p hp i v ctx (v (i + 1))
      five.left hadj with hleftPartner | hleftCenter | hleftOuter
    · have hleftNext : five.left = v (i + 1) := hleftPartner
      have hrightHull : five.right ∈ hullVertexIndices p :=
        diameterEndpoints_subset_hullVertexIndices p hp five.right_diameter
      have hrightne : five.right ≠ v (i + 1) := by
        intro heq
        exact five.base.ne (hleftNext.trans heq.symm)
      have hpred := supporting_hull_chord_eq_predecessor p hp v hv hh hrange hsupport
        (i + 1) five.right hrightHull hrightne (by
          intro k
          simpa only [hleftNext] using five.support k)
      have hrightSource : five.right = v i := by
        have hi : (i + 1) - 1 = i := by abel
        simpa only [hi] using hpred
      have hfcoord := SharedFiveCenterChoice.center_coordinate_with_height
        p (by omega) hp five choice.height choice.height_pos choice.height_sq
      rw [hleftNext, hrightSource] at hfcoord
      have hpoint : p qfive = p ctx.q := by
        apply edgeCoordinate_injective (p (v (i + 1))) (p (v i)) hne.symm
        rw [hfcoord, choice.center_coordinate]
      have hqeq : qfive = ctx.q := hp hpoint
      have hdeg := five.center_degree
      rw [hqeq, choice.center_degree] at hdeg
      omega
    · exact ctx.central_outside (hleftCenter ▸ five.left_diameter)
    · exact houterD (hleftOuter ▸ five.left_diameter)

  have hleftNeSource : five.left ≠ v i := by
    intro hleftSource
    have hadjRight : (nearestGraph p).Adj (v i) five.right := by
      simpa only [hleftSource] using five.base
    rcases choice.source_neighbor_cases_of_context p hp i v ctx (v (i + 1))
      five.right hadjRight with hrightPartner | hrightCenter | hrightOuter
    · have hMcoord :
          edgeCoordinate (p (v i)) (p (v (i + 1))) (p ctx.q) =
            (1 / 2 : ℂ) + (choice.height : ℂ) * Complex.I := by
        rw [edgeCoordinate_swap_base _ _ _ hne.symm, choice.center_coordinate]
        ring
      have hprod := edgeCoordinate_im_mul_dist_sq
        (p (v i)) (p (v (i + 1))) (p ctx.q) hne
      rw [hMcoord] at hprod
      norm_num [Complex.mul_im] at hprod
      have hsq : 0 < dist (p (v i)) (p (v (i + 1))) ^ 2 :=
        sq_pos_of_pos (dist_pos.mpr hne)
      have hturnpos : 0 < turn (p (v i)) (p (v (i + 1))) (p ctx.q) := by
        nlinarith only [hprod, hsq, choice.height_pos]
      have hs := five.support ctx.q
      rw [hleftSource, hrightPartner, turn_reverse] at hs
      linarith
    · exact ctx.central_outside (hrightCenter ▸ five.right_diameter)
    · exact houterD (hrightOuter ▸ five.right_diameter)

  have hminle : pairDist p ctx.minPair ≤ dist (p (v i)) (p five.left) :=
    isMinPair_le_dist p ctx.minPair_spec hleftNeSource.symm
  have hdistne : dist (p (v i)) (p five.left) ≠ pairDist p ctx.minPair := by
    intro heq
    exact hleftNotAdj
      ((nearestGraph_adj_iff_dist_eq p hp ctx.minPair_spec (v i) five.left).mpr heq)
  have hdist : pairDist p ctx.minPair < dist (p (v i)) (p five.left) :=
    lt_of_le_of_ne hminle (Ne.symm hdistne)
  have hδ : 0 < pairDist p ctx.minPair := pairDist_pos p hp ctx.minPair_spec.1
  rw [edgeCoordinate_sub_one_norm _ _ _ hne.symm,
    nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base]
  exact (lt_div_iff₀ hδ).2 (by simpa only [one_mul] using hdist)

/-- In the actual tight-flat hull, if a degree-five shared-six right receiver
is also a retained shared-five bottom, then the two shared-five endpoints
already satisfy the narrow strip hypotheses used by the scalar second-
extension obstruction.  The first endpoint lies in the lower one-eighth
strip, while the oriented shared-five unit edge has vertical component at
most one eighth in the shared-six frame. -/
theorem SharedSixPacketChoice.second_extension_sharedFive_endpoint_strip
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n)
    (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (five : SharedFiveCenterChoice p qfive)
    (hbottom : five.selection.bottom = choice.packet.right) :
    let a := edgeCoordinate (p partner) (p (v i)) (p five.left)
    let b := edgeCoordinate (p partner) (p (v i)) (p five.right) - a
    (-(1 / 8 : ℝ) ≤ a.im ∧ a.im ≤ 0) ∧ |b.im| ≤ 1 / 8 := by
  dsimp only
  have hpartner : partner = v (i + 1) :=
    choice.partner_eq_successor p hp hn v hv hh hrange hsupport i ctx
  subst partner
  have hne : p (v i) ≠ p (v (i + 1)) :=
    hp.ne (hv.ne (cyclic_three_distinct hh i).1)
  have houtbase : (nearestGraph p).Adj (v i) (v (i + 1)) := choice.base.symm
  have hδ : 0 < pairDist p ctx.minPair := pairDist_pos p hp ctx.minPair_spec.1
  have hscale : pairDist p ctx.minPair /
      dist (p (v i)) (p (v (i + 1))) = 1 := by
    rw [nearestGraph_adj_dist_eq p ctx.minPair_spec houtbase, div_self hδ.ne']
  have hlow : (nearestGraph p).degree five.selection.bottom ≤ 5 ∧
      five.selection.first.right = five.selection.bottom ∧
      five.selection.second.right = five.selection.bottom := by
    rcases five.selection.branch with hlow | hhigh
    · exact hlow
    · have hsix : (nearestGraph p).degree choice.packet.right = 6 := by
        rw [← hbottom]
        exact hhigh.1
      omega
  have hfirst : five.selection.first.right = choice.packet.right :=
    hlow.2.1.trans hbottom
  have hsecond : five.selection.second.right = choice.packet.right :=
    hlow.2.2.trans hbottom
  have hchoicepos : 0 < choice.packet.weight choice.packet.right := by
    rw [choice.site_weights.2]
    omega
  have hfirstpos : 0 < five.selection.first.weight choice.packet.right := by
    simp [LocalChargePacket.weight, hfirst]
  have hsecondpos : 0 < five.selection.second.weight choice.packet.right := by
    simp [LocalChargePacket.weight, hsecond]
  let rule : CertifiedDonorRule p (v i) ctx.q (fun _ => 0) := .sharedSix choice
  have hrulepos : 0 < rule.packet.weight choice.packet.right := by
    simpa only [rule, CertifiedDonorRule.packet] using hchoicepos
  have hrect := certifiedDonorRule_supporting_rectangle p hp hn v hv hh hrange
    hsupport hpos i ctx (fun _ => 0) rule choice.packet.right hrulepos
  have hleftLocal := certified_rule_common_receiver_source_local p hp hn v hv hh
    hrange hsupport hpos i ctx (fun _ => 0) rule five.left five.left_diameter
    five.selection.first choice.packet.right hrulepos hfirstpos
  have hrightLocal := certified_rule_common_receiver_source_local p hp hn v hv hh
    hrange hsupport hpos i ctx (fun _ => 0) rule five.right five.right_diameter
    five.selection.second choice.packet.right hrulepos hsecondpos
  have hleftSlope := tight_flat_seven_vertex_im_bound p hp v hv hh hpos i
    ctx.outside_bad five.left
      ((mem_hullSourceNeighborhood_iff v i five.left).mp hleftLocal)
  have hleftRe := packet_source_horizontal_bound p (v i) (v (i + 1)) five.left
    choice.packet.right hne ctx.minPair ctx.minPair_spec five.selection.first
    hfirstpos hrect.1
  change |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p five.left)).im| ≤
      |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p five.left)).re| / 30
    at hleftSlope
  change |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p five.left)).re| ≤
      (15 / 4 : ℝ) *
        (pairDist p ctx.minPair / dist (p (v i)) (p (v (i + 1)))) at hleftRe
  rw [hscale, mul_one] at hleftRe
  have hleftIm :
      |(edgeCoordinate (p (v i)) (p (v (i + 1))) (p five.left)).im| ≤ 1 / 8 := by
    linarith only [hleftSlope, hleftRe]
  have hswapLeft := edgeCoordinate_swap_base
    (p (v i)) (p (v (i + 1))) (p five.left) hne
  have haabs :
      |(edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).im| ≤ 1 / 8 := by
    rw [hswapLeft]
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    exact hleftIm
  have hale :
      (edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support _ _ _ hne.symm (hsupport i five.left)
  have halo : -(1 / 8 : ℝ) ≤
      (edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).im :=
    (abs_le.mp haabs).1

  have hrightHull : five.right ∈ hullVertexIndices p :=
    diameterEndpoints_subset_hullVertexIndices p hp five.right_diameter
  have hrightRange : five.right ∈ Set.range v := by
    rw [hrange]
    exact hrightHull
  obtain ⟨j, hj⟩ := hrightRange
  have hleftSucc : five.left = v (j + 1) :=
    five.left_eq_cyclic_successor_of_right p hp v hv hh hrange hsupport j hj.symm
  have hjlocal :
      j = i ∨ j = i + 1 ∨ j = i - 1 ∨ j = (i + 1) + 1 ∨
      j = (i - 1) - 1 ∨ j = ((i + 1) + 1) + 1 ∨
      j = ((i - 1) - 1) - 1 := by
    rcases (mem_hullSourceNeighborhood_iff v i five.right).mp hrightLocal with
      h0 | h1 | hm1 | h2 | hm2 | h3 | hm3
    · exact Or.inl (hv (hj.trans h0))
    · exact Or.inr (Or.inl (hv (hj.trans h1)))
    · exact Or.inr (Or.inr (Or.inl (hv (hj.trans hm1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hv (hj.trans h2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hv (hj.trans hm2))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hv (hj.trans h3)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hv (hj.trans hm3)))))))
  have hj8 :
      j = (((i - 1) - 1) - 1) - 1 ∨ j = ((i - 1) - 1) - 1 ∨
      j = (i - 1) - 1 ∨ j = i - 1 ∨ j = i ∨ j = i + 1 ∨
      j = (i + 1) + 1 ∨ j = ((i + 1) + 1) + 1 := by
    rcases hjlocal with h0 | h1 | hm1 | h2 | hm2 | h3 | hm3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
    · exact Or.inr (Or.inr (Or.inl hm2))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3))))))
    · exact Or.inr (Or.inl hm3)
  have harg := tight_hull_eight_edge_args p hp v hv hh i hpos ctx.outside_bad j hj8
  have hbdir :
      edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
          edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left) =
        hullEdgeDirection p v j / hullEdgeDirection p v i := by
    rw [← hj, hleftSucc]
    calc
      edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v j)) -
          edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v (j + 1))) =
          edgeCoordinate (p (v i)) (p (v (i + 1))) (p (v (j + 1))) -
            edgeCoordinate (p (v i)) (p (v (i + 1))) (p (v j)) := by
              rw [edgeCoordinate_swap_base _ _ _ hne,
                edgeCoordinate_swap_base _ _ _ hne]
              ring
      _ = hullEdgeDirection p v j / hullEdgeDirection p v i := by
        rw [edgeCoordinate_sub]
        rfl
  have hproj :
      |(edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).im| ≤
      (edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).re / 30 := by
    rw [hbdir]
    exact (extended_small_arg_projection _ harg).2
  have hbnorm :
      ‖edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)‖ = 1 := by
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hne.symm,
      nearestGraph_adj_dist_eq p ctx.minPair_spec five.base.symm,
      nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base,
      div_self hδ.ne']
  have hbre :
      (edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).re ≤ 1 := by
    simpa only [hbnorm] using Complex.re_le_norm
      (edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left))
  have hbim :
      |(edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.right) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p five.left)).im| ≤ 1 / 8 := by
    linarith only [hproj, hbre]
  exact ⟨⟨halo, hale⟩, hbim⟩

/-- When the actual second extension is also a shared-five bottom, its
shared-five center is a unit neighbor of that extension and is at least one
unit away from the outer site in the shared-six frame. The latter separation
uses the actual hull endpoint to exclude the outer site as a five-center. -/
theorem SharedSixPacketChoice.second_extension_sharedFive_center_distances {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hbottom : five.selection.bottom = choice.packet.right) :
    ‖edgeCoordinate (p u) (p w) (p qfive) -
        ((2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)‖ = 1 ∧
      1 ≤ ‖edgeCoordinate (p u) (p w) (p qfive) -
        ((3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ := by
  obtain ⟨t₂, hright, _, _, _, _, ht₂coord, _⟩ :=
    choice.degree_five_right_second_extension_data hdegree hnot_lower
  have hne : p u ≠ p w := hp.ne choice.base.ne
  have hqbottom : (nearestGraph p).Adj qfive t₂ := by
    simpa only [hbottom, hright] using five.selection.bottom_adj
  have hqouter : qfive ≠ choice.outer := by
    intro heq
    subst qfive
    exact choice.outer_not_sharedFive_center p hn hp hw hqw ⟨five⟩
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hbase : dist (p u) (p w) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin choice.base
  constructor
  · rw [← ht₂coord]
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hne, hbase,
      nearestGraph_adj_dist_eq p hmin hqbottom, div_self hδ.ne']
  · rw [← choice.outer_coordinate]
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hne, hbase]
    exact (le_div_iff₀ hδ).mpr (by
      simpa only [one_mul] using isMinPair_le_dist p hmin hqouter)

/-- Convert the actual second-extension/shared-five overlap into the scalar
frame used by the analytic obstruction.  In particular, this discharges four
of the geometric hypotheses of `extension_shared_five_third_neighbor_impossible`:
the shared-five edge has unit normalized length, its center has the required
affine coordinate, the center is one unit from `t₂` and separated from the
outer site, and the supporting orientation becomes the scalar support
inequality. -/
theorem SharedSixPacketChoice.second_extension_sharedFive_scalar_core {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : SharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hbottom : five.selection.bottom = choice.packet.right) :
    let a := edgeCoordinate (p u) (p w) (p five.left)
    let b := edgeCoordinate (p u) (p w) (p five.right) - a
    ‖b‖ = 1 ∧
      edgeCoordinate (p u) (p w) (p qfive) =
        a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b ∧
      ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
          ((2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)‖ = 1 ∧
      1 ≤ ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
          ((3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ ∧
      (conj b * (1 - a)).im ≤ 0 := by
  dsimp only
  have hne : p u ≠ p w := hp.ne choice.base.ne
  have hfive_ne : p five.left ≠ p five.right := hp.ne five.base.ne
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hδ : 0 < pairDist p ij := pairDist_pos p hp hmin.1
  have hbase : dist (p u) (p w) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin choice.base
  have hfive_base : dist (p five.left) (p five.right) = pairDist p ij :=
    nearestGraph_adj_dist_eq p hmin five.base
  have hbnorm :
      ‖edgeCoordinate (p u) (p w) (p five.right) -
        edgeCoordinate (p u) (p w) (p five.left)‖ = 1 := by
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hne,
      dist_comm (p five.right) (p five.left), hfive_base, hbase, div_self hδ.ne']
  have hfive_center := SharedFiveCenterChoice.center_coordinate_with_height
    p hn hp five choice.height choice.height_pos choice.height_sq
  have hcenter :
      edgeCoordinate (p u) (p w) (p qfive) =
        edgeCoordinate (p u) (p w) (p five.left) +
          ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) *
            (edgeCoordinate (p u) (p w) (p five.right) -
              edgeCoordinate (p u) (p w) (p five.left)) := by
    rw [edgeCoordinate_affine_base_change _ _ _ _ _ hne hfive_ne,
      hfive_center]
  have hd := choice.second_extension_sharedFive_center_distances p hn hp hw hqw
    hdegree hnot_lower five hbottom
  rw [hcenter] at hd
  have hturn : turn (p five.left) (p five.right) (p w) ≤ 0 := by
    have hrev : turn (p five.left) (p five.right) (p w) =
        -turn (p five.right) (p five.left) (p w) := by
      unfold turn
      ring
    rw [hrev]
    exact neg_nonpos.mpr (five.support w)
  have hct := edgeCoordinate_complexTurn_mul_dist_sq
    (p u) (p w) (p five.left) (p five.right) (p w) hne
  have hdist_sq : 0 < dist (p u) (p w) ^ 2 :=
    sq_pos_of_pos (dist_pos.mpr hne)
  have hcomplex :
      complexTurn (edgeCoordinate (p u) (p w) (p five.left))
        (edgeCoordinate (p u) (p w) (p five.right))
        (edgeCoordinate (p u) (p w) (p w)) ≤ 0 := by
    nlinarith only [hct, hturn, hdist_sq]
  rw [complexTurn, edgeCoordinate_axis _ _ hne] at hcomplex
  exact ⟨hbnorm, hcenter, hd.1, hd.2, hcomplex⟩

/-- The same two actual center distances in the mirrored shared-six frame. -/
theorem ReflectedSharedSixPacketChoice.second_extension_sharedFive_center_distances
    {n : ℕ} (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w q qfive : Fin n} (choice : ReflectedSharedSixPacketChoice p u w q)
    (hw : w ∈ diameterEndpoints p) (hqw : (nearestGraph p).Adj q w)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.reflected.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hbottom : five.selection.bottom = choice.packet.right) :
    ‖edgeCoordinate (p u) (p w) (p qfive) -
        ((2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I)‖ = 1 ∧
      1 ≤ ‖edgeCoordinate (p u) (p w) (p qfive) -
        ((3 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I)‖ := by
  let pR : Fin n → Point := fun i => planeReflection (p i)
  have hpR : Function.Injective pR := planeReflection.injective.comp hp
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hwR : w ∈ diameterEndpoints pR := by simpa only [hD] using hw
  have hqwR : (nearestGraph pR).Adj q w := by simpa only [hG] using hqw
  have hdegreeR : (nearestGraph pR).degree choice.reflected.packet.right = 5 := by
    rw [← choice.packet_sites.2]
    exact (nearestGraph_degree_eq_of_dist_eq p pR hdist choice.packet.right).trans hdegree
  have hbottomR : (five.reflection_swap hp).selection.bottom =
      choice.reflected.packet.right := by
    simpa only [SharedFiveCenterChoice.reflection_swap_bottom, choice.packet_sites.2]
      using hbottom
  have h := choice.reflected.second_extension_sharedFive_center_distances pR hn hpR
    hwR hqwR hdegreeR (by simpa only [choice.packet_sites.2] using hnot_lower)
    (five.reflection_swap hp) hbottomR
  have hc₂ : ((2 : ℂ) - ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I) =
      conj ((2 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hc₃ : ((3 / 2 : ℂ) - (choice.reflected.height : ℂ) * Complex.I) =
      conj ((3 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I) := by
    simp only [map_add, map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  simpa only [pR, edgeCoordinate_planeReflection, hc₂, hc₃,
    ← map_sub, Complex.norm_conj] using h

/-- The third neighbor of the left endpoint of a supported unit triangle
must point at least half a unit to the left. -/
theorem supported_triangle_third_neighbor_re_le (z : ℂ) (h : ℝ)
    (hh : 0 < h) (hsq : h ^ 2 = 3 / 4) (hz : ‖z‖ = 1)
    (hzi : z.im ≤ 0) (hsep1 : 1 ≤ ‖z - 1‖)
    (hsepq : 1 ≤ ‖z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I)‖) :
    z.re ≤ -1 / 2 := by
  have hzsq := extension_norm_sq z
  rw [hz] at hzsq
  have hs1 := extension_norm_sq (z - 1)
  have hsq1 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr hsep1
  norm_num at hs1
  have hx : z.re ≤ 1 / 2 := by nlinarith only [hzsq, hs1, hsq1]
  have hsqn := extension_norm_sq (z - ((1 / 2 : ℂ) - (h : ℂ) * Complex.I))
  have hsepqn := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr hsepq
  norm_num [Complex.mul_re, Complex.mul_im] at hsqn
  have hcone : z.re - 2 * h * z.im ≤ 1 := by
    nlinarith only [hzsq, hsqn, hsepqn, hsq]
  have hprod := mul_nonneg
    (show 0 ≤ 1 - z.re + 2 * h * z.im by linarith)
    (show 0 ≤ 1 - z.re - 2 * h * z.im by nlinarith only [hx, hh, hzi])
  have hsqmul := congrArg (fun a : ℝ => a * z.im ^ 2) hsq
  by_contra hn
  have hxn : -1 / 2 < z.re := lt_of_not_ge hn
  have hbad := mul_neg_of_pos_of_neg
    (show 0 < 2 * z.re + 1 by linarith)
    (show z.re - 1 < 0 by linarith)
  nlinarith only [hprod, hsqmul, hzsq, hbad]

/-- A fixed small rectangle lies in the two open unit disks that block the
third neighbor in the second-extension configuration. -/
theorem extension_third_neighbor_in_blocking_disks (z : ℂ) (h : ℝ)
    (hhlo : (4 / 5 : ℝ) ≤ h) (hhhi : h ≤ 7 / 8)
    (hxlo : (99 / 100 : ℝ) ≤ z.re) (hxhi : z.re ≤ 99 / 50)
    (hylo : -(9 / 8 : ℝ) ≤ z.im) (hyhi : z.im ≤ 0) :
    ‖z - 1‖ < 1 ∨ ‖z - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ < 1 := by
  by_cases hy : -(1 / 10 : ℝ) ≤ z.im
  · left
    have hs := extension_norm_sq (z - 1)
    norm_num at hs
    have hxprod := mul_nonneg (show 0 ≤ z.re - 99 / 100 by linarith)
      (show 0 ≤ 99 / 50 - z.re by linarith)
    have hyprod := mul_nonneg (show 0 ≤ z.im + 1 / 10 by linarith)
      (show 0 ≤ -z.im by linarith)
    nlinarith [norm_nonneg (z - 1)]
  · right
    have hs := extension_norm_sq (z - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I))
    norm_num [Complex.mul_re, Complex.mul_im] at hs
    have hxprod := mul_nonneg (show 0 ≤ z.re - 99 / 100 by linarith)
      (show 0 ≤ 99 / 50 - z.re by linarith)
    have hdlo : -(13 / 40 : ℝ) ≤ z.im + h := by linarith
    have hdhi : z.im + h ≤ 31 / 40 := by linarith
    have hdprod := mul_nonneg (sub_nonneg.mpr hdlo) (sub_nonneg.mpr hdhi)
    nlinarith [norm_nonneg (z - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I))]

/-- Two shallow endpoints of the shared-five triangle meeting the retained
second extension force the endpoint nearest the six triangle into a narrow
horizontal interval. -/
theorem extension_shared_five_left_bounds (a b : ℂ) (h : ℝ)
    (hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (haim : -(1 / 8 : ℝ) ≤ a.im ∧ a.im ≤ 0)
    (hbim : |b.im| ≤ 1 / 8) (hbnorm : ‖b‖ = 1)
    (hqa : ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I)‖ = 1)
    (hqb : 1 ≤ ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖)
    (haw : 1 ≤ ‖a - 1‖) :
    (99 / 100 : ℝ) ≤ b.re ∧ (199 / 100 : ℝ) ≤ a.re ∧ a.re ≤ 47 / 20 := by
  have hhlo : (433 / 500 : ℝ) ≤ h := by nlinarith
  have hhhi : h ≤ 7 / 8 := by nlinarith
  have hbre : |b.re| ≤ 1 := by simpa [hbnorm] using Complex.abs_re_le_norm b
  have hbsq := extension_norm_sq b
  rw [hbnorm] at hbsq
  have hbimsq : b.im ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr hbim
    simpa only [sq_abs] using ht
  let q := a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b
  let z := q - ((2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I)
  have hz : ‖z‖ = 1 := hqa
  have hzsq := extension_norm_sq z
  rw [hz] at hzsq
  have hzre : |z.re| ≤ 1 := by simpa only [hz] using Complex.abs_re_le_norm z
  have hzim : |z.im| ≤ 1 := by simpa only [hz] using Complex.abs_im_le_norm z
  have hzre_eq : z.re = a.re + b.re / 2 + h * b.im - 2 := by
    dsimp [z, q]; norm_num [Complex.mul_re]; ring
  have hzim_eq : z.im = a.im + b.im / 2 - h * b.re + 2 * h := by
    dsimp [z, q]; norm_num [Complex.mul_im]; ring
  have hbpos : 0 < b.re := by
    by_contra hn
    have hle : b.re ≤ 0 := le_of_not_gt hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos hh.le hle
    have himlo := (abs_le.mp hbim).1
    have himhi := (abs_le.mp hzim).2
    linarith [haim.1]
  have hbr : (99 / 100 : ℝ) ≤ b.re := by
    nlinarith only [hbsq, hbimsq, hbpos]
  have hzilo : (1357 / 2000 : ℝ) ≤ z.im := by
    have hbrhi := (abs_le.mp hbre).2
    have hm := mul_le_mul_of_nonneg_left hbrhi hh.le
    have hbilo := (abs_le.mp hbim).1
    linarith [haim.1]
  have hzxhi : z.re ≤ 147 / 200 := by
    have hisq : (1357 / 2000 : ℝ) ^ 2 ≤ z.im ^ 2 :=
      (sq_le_sq₀ (by norm_num) (by linarith)).mpr hzilo
    nlinarith only [hzsq, hisq]
  have hqbsq := extension_norm_sq
    (q - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I))
  have hqb2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr hqb
  have heq : q - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I) =
      z + (1 / 2 : ℂ) - (h : ℂ) * Complex.I := by dsimp [z]; push_cast; ring
  change (1 : ℝ) ^ 2 ≤ ‖q - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ ^ 2 at hqb2
  rw [heq] at hqbsq hqb2
  norm_num [Complex.mul_re, Complex.mul_im] at hqbsq
  have hzcone : 2 * h * z.im - 1 ≤ z.re := by
    nlinarith only [hqbsq, hqb2, hzsq, hsq]
  have hzxlo : (17 / 100 : ℝ) ≤ z.re := by
    have hm := mul_le_mul hhlo hzilo (by norm_num) hh.le
    nlinarith only [hm, hzcone]
  have hbprod : |h * b.im| ≤ 7 / 64 := by
    rw [abs_mul, abs_of_pos hh]
    exact (mul_le_mul hhhi hbim (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have halarge : 3 / 2 < a.re := by
    have hbrhi := (abs_le.mp hbre).2
    have hprodhi := (abs_le.mp hbprod).2
    linarith only [hzre_eq, hzxlo, hbrhi, hprodhi]
  have hasq := extension_norm_sq (a - 1)
  norm_num at hasq
  have haw2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mpr haw
  have hai2 : a.im ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ a.im + 1 / 8 by linarith [haim.1])
      (show 0 ≤ -a.im by linarith [haim.2])]
  have halo : (199 / 100 : ℝ) ≤ a.re := by
    nlinarith only [hasq, haw2, hai2, halarge]
  refine ⟨hbr, halo, ?_⟩
  have hprodlo := (abs_le.mp hbprod).1
  linarith only [hzre_eq, hzxhi, hbr, hprodlo]

open scoped ComplexConjugate

/-- If the third neighbor is the six packet's outer site, the unit
quadrilateral forces the five base to be horizontal. Support then places
its first endpoint exactly one unit beyond the six source. -/
theorem extension_outer_third_neighbor_forces_unit_source_distance
    (a b : ℂ) (h : ℝ) (hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (haim : -(1 / 8 : ℝ) ≤ a.im ∧ a.im ≤ 0)
    (hbim : |b.im| ≤ 1 / 8) (hbnorm : ‖b‖ = 1)
    (hbr : (99 / 100 : ℝ) ≤ b.re) (hare : (199 / 100 : ℝ) ≤ a.re)
    (hqa : ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I)‖ = 1)
    (hqb : 1 ≤ ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖)
    (hab : ‖a - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1)
    (hsupport : (conj b * (1 - a)).im ≤ 0) : ‖a - 1‖ = 1 := by
  let α : ℂ := (1 / 2 : ℂ) - (h : ℂ) * Complex.I
  let B : ℂ := (3 / 2 : ℂ) - (h : ℂ) * Complex.I
  let X : ℂ := (2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I
  let Q := a + α * b
  let c := B + Q - a
  have hhlo : (4 / 5 : ℝ) ≤ h := by nlinarith
  have hαnorm : ‖α‖ = 1 := by
    have ht := extension_norm_sq α
    dsimp [α] at ht
    norm_num [Complex.mul_re, Complex.mul_im] at ht
    nlinarith [norm_nonneg α]
  have hαne : α ≠ 0 := by intro heq; simp [heq] at hαnorm
  have hXB : X - B = α := by dsimp [X, B, α]; push_cast; ring
  have hQane : Q ≠ B := by
    intro heq
    change 1 ≤ ‖Q - B‖ at hqb
    simp only [heq, sub_self, norm_zero] at hqb
    norm_num at hqb
  have haX : a ≠ X := by
    intro heq
    have him := congrArg Complex.im heq
    dsimp [X] at him
    norm_num [Complex.mul_im] at him
    linarith [haim.1]
  have hca : c ≠ a := by
    intro heq
    have him := congrArg Complex.im heq
    dsimp [c, B, Q, α] at him
    norm_num [Complex.mul_im, Complex.mul_re] at him
    have hm := mul_le_mul_of_nonneg_left hbr hh.le
    have himhi := (abs_le.mp hbim).2
    nlinarith only [him, hm, hhlo, himhi, haim.1]
  have hQa : ‖Q - a‖ = 1 := by
    simp only [Q, add_sub_cancel_left, norm_mul, hαnorm, hbnorm, one_mul]
  have hcB : ‖c - B‖ = 1 := by
    rw [show c - B = Q - a by dsimp [c]; ring]
    exact hQa
  have hcQ : ‖c - Q‖ = 1 := by
    rw [show c - Q = B - a by dsimp [c]; ring, norm_sub_rev]
    exact hab
  have hc : c = X := by
    have hor := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      Complex.finrank_real_complex hQane.symm haX
      (by simpa only [dist_eq_norm] using hab)
      (by simpa only [dist_eq_norm, hXB] using hαnorm)
      (by simpa only [dist_eq_norm] using hcB)
      (by simpa only [dist_eq_norm, norm_sub_rev] using hQa)
      (by simpa only [dist_eq_norm, norm_sub_rev] using hqa)
      (by simpa only [dist_eq_norm] using hcQ)
    exact hor.resolve_left hca
  have hαb : α * b = α := by
    calc
      α * b = c - B := by dsimp [c, Q]; ring
      _ = α := by rw [hc, hXB]
  have hb : b = 1 := mul_left_cancel₀ hαne (by simpa using hαb)
  rw [hb] at hsupport
  simp only [map_one, one_mul, Complex.sub_im, Complex.one_im, zero_sub] at hsupport
  have hai : a.im = 0 := by linarith [haim.2]
  have hs := extension_norm_sq (a - B)
  change ‖a - B‖ = 1 at hab
  rw [hab] at hs
  dsimp [B] at hs
  norm_num [Complex.mul_re, Complex.mul_im, hai] at hs
  have har : a.re = 2 := by nlinarith only [hs, hsq, hare]
  have ha : a = 2 := by apply Complex.ext <;> simp [har, hai]
  norm_num [ha]

/-- The geometric core of the two-donor exclusion. A third neighbor of the
near endpoint cannot avoid the existing source and outer site. The two
possible identifications also contradict the strict source separation. -/
theorem extension_shared_five_third_neighbor_impossible
    (a b z : ℂ) (h : ℝ) (hh : 0 < h) (hsq : h ^ 2 = 3 / 4)
    (haim : -(1 / 8 : ℝ) ≤ a.im ∧ a.im ≤ 0)
    (hbim : |b.im| ≤ 1 / 8) (hbnorm : ‖b‖ = 1)
    (hqa : ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I)‖ = 1)
    (hqb : 1 ≤ ‖a + ((1 / 2 : ℂ) - (h : ℂ) * Complex.I) * b -
      ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖)
    (haw : 1 < ‖a - 1‖)
    (hsupport : (conj b * (1 - a)).im ≤ 0)
    (hz : ‖z‖ = 1) (hzre : z.re ≤ -1 / 2)
    (hcim : (a + z * b).im ≤ 0)
    (hcW : a + z * b = 1 ∨ 1 ≤ ‖a + z * b - 1‖)
    (hcB : a + z * b = (3 / 2 : ℂ) - (h : ℂ) * Complex.I ∨
      1 ≤ ‖a + z * b - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖) : False := by
  obtain ⟨hbr, halo, hahi⟩ := extension_shared_five_left_bounds a b h hh hsq
    haim hbim hbnorm hqa hqb haw.le
  let c := a + z * b
  have hca : ‖c - a‖ = 1 := by
    simp only [c, add_sub_cancel_left, norm_mul, hz, hbnorm, one_mul]
  have hcWne : c ≠ 1 := by
    intro heq
    rw [heq, norm_sub_rev] at hca
    linarith
  have hcBne : c ≠ (3 / 2 : ℂ) - (h : ℂ) * Complex.I := by
    intro heq
    have hab : ‖a - ((3 / 2 : ℂ) - (h : ℂ) * Complex.I)‖ = 1 := by
      rw [heq, norm_sub_rev] at hca
      exact hca
    have ht := extension_outer_third_neighbor_forces_unit_source_distance
      a b h hh hsq haim hbim hbnorm hbr halo hqa hqb hab hsupport
    linarith
  have hcWfar := hcW.resolve_left hcWne
  have hcBfar := hcB.resolve_left hcBne
  have hcdx : |c.re - a.re| ≤ 1 := by
    simpa only [Complex.sub_re, hca] using Complex.abs_re_le_norm (c - a)
  have hcdy : |c.im - a.im| ≤ 1 := by
    simpa only [Complex.sub_im, hca] using Complex.abs_im_le_norm (c - a)
  have hclo : (99 / 100 : ℝ) ≤ c.re := by linarith [(abs_le.mp hcdx).1]
  have hcylo : -(9 / 8 : ℝ) ≤ c.im := by linarith [haim.1, (abs_le.mp hcdy).1]
  have hzim : |z.im| ≤ 1 := by simpa only [hz] using Complex.abs_im_le_norm z
  have herr : |z.im * b.im| ≤ 1 / 8 := by
    rw [abs_mul]
    exact (mul_le_mul hzim hbim (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hmul : z.re * b.re ≤ -(99 / 200 : ℝ) := by
    have ht := mul_le_mul_of_nonneg_right hzre (by linarith : 0 ≤ b.re)
    nlinarith only [ht, hbr]
  have hchi : c.re ≤ 99 / 50 := by
    have hcre : c.re = a.re + z.re * b.re - z.im * b.im := by
      dsimp [c]; simp only [Complex.mul_re]; ring
    linarith [hcre, (abs_le.mp herr).1]
  rcases extension_third_neighbor_in_blocking_disks c h
    (by nlinarith : (4 / 5 : ℝ) ≤ h) (by nlinarith : h ≤ 7 / 8)
    hclo hchi hcylo hcim with hs | hs
  · linarith
  · linarith


/-- The actual forward shared-six second extension cannot simultaneously be a
retained shared-five bottom once the shared-five left endpoint is an actual
charge donor.  This is the full bridge from the certified geometry to the
scalar third-neighbor obstruction: endpoint strips, source separation, the
third nearest neighbor of the degree-three endpoint, and all minimum-distance
separations are derived rather than assumed. -/
theorem tight_flat_sharedSix_second_extension_ne_sharedFive_bottom_of_left_donor
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ j k, 0 ≤ turn (p (v j)) (p (v (j + 1))) (p k))
    (hpos : ∀ j, 0 < hullExteriorAngle p v j)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (partner qfive : Fin n)
    (choice : SharedSixPacketChoice p partner (v i) ctx.q)
    (hdegree : (nearestGraph p).degree choice.packet.right = 5)
    (hnot_lower : choice.packet.right ≠ choice.lower)
    (five : SharedFiveCenterChoice p qfive)
    (hleftDonor : five.left ∈ chargeDonors p (tightHullBadVertices p v)) :
    five.selection.bottom ≠ choice.packet.right := by
  intro hbottom
  let a := edgeCoordinate (p partner) (p (v i)) (p five.left)
  let b := edgeCoordinate (p partner) (p (v i)) (p five.right) - a
  have hstrip := choice.second_extension_sharedFive_endpoint_strip p hp hn v hv hh
    hrange hsupport hpos i ctx partner qfive hdegree five hbottom
  change (-(1 / 8 : ℝ) ≤ a.im ∧ a.im ≤ 0) ∧ |b.im| ≤ 1 / 8 at hstrip
  have hcore := choice.second_extension_sharedFive_scalar_core p (by omega) hp
    ctx.endpoint ctx.central_adj.symm hdegree hnot_lower five hbottom
  change ‖b‖ = 1 ∧
      edgeCoordinate (p partner) (p (v i)) (p qfive) =
        a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b ∧
      ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
          ((2 : ℂ) - ((2 * choice.height : ℝ) : ℂ) * Complex.I)‖ = 1 ∧
      1 ≤ ‖a + ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I) * b -
          ((3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ ∧
      (conj b * (1 - a)).im ≤ 0 at hcore
  have haw := choice.sharedFive_left_strict_source_distance p hp hn v hv hh hrange
    hsupport i ctx partner qfive five
  change 1 < ‖a - 1‖ at haw

  have hleftDegree : (nearestGraph p).degree five.left = 3 :=
    (Finset.mem_filter.mp hleftDonor).2.2
  have hqrne : qfive ≠ five.right := five.center_right.ne
  have hcard : ({five.right, qfive} : Finset (Fin n)).card <
      ((nearestGraph p).neighborFinset five.left).card := by
    rw [(nearestGraph p).card_neighborFinset_eq_degree, hleftDegree]
    simp [hqrne.symm]
  obtain ⟨c, hcMem, hcNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcAdj : (nearestGraph p).Adj five.left c :=
    ((nearestGraph p).mem_neighborFinset five.left c).mp hcMem
  have hcne : c ≠ five.right ∧ c ≠ qfive := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hcNot

  let z := edgeCoordinate (p five.left) (p five.right) (p c)
  have hfiveNe : p five.left ≠ p five.right := hp.ne five.base.ne
  have hbaseNe : p partner ≠ p (v i) := hp.ne choice.base.ne
  have hδ : 0 < pairDist p ctx.minPair := pairDist_pos p hp ctx.minPair_spec.1
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [edgeCoordinate_norm _ _ _ hfiveNe,
      nearestGraph_adj_dist_eq p ctx.minPair_spec hcAdj,
      nearestGraph_adj_dist_eq p ctx.minPair_spec five.base,
      div_self hδ.ne']
  have hzi : z.im ≤ 0 := by
    dsimp [z]
    exact edgeCoordinate_im_nonpos_of_support _ _ _ hfiveNe (five.support c)
  have hsep1 : 1 ≤ ‖z - 1‖ := by
    dsimp [z]
    rw [edgeCoordinate_sub_one_norm _ _ _ hfiveNe,
      nearestGraph_adj_dist_eq p ctx.minPair_spec five.base]
    apply (le_div_iff₀ hδ).2
    simpa only [one_mul] using
      (isMinPair_le_dist p ctx.minPair_spec hcne.1.symm)
  have hqcoord := SharedFiveCenterChoice.center_coordinate_with_height
    p (by omega) hp five choice.height choice.height_pos choice.height_sq
  have hsepq :
      1 ≤ ‖z - ((1 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ := by
    rw [← hqcoord]
    dsimp [z]
    rw [← dist_eq_norm, edgeCoordinate_dist _ _ _ _ hfiveNe,
      nearestGraph_adj_dist_eq p ctx.minPair_spec five.base]
    apply (le_div_iff₀ hδ).2
    simpa only [one_mul] using
      (isMinPair_le_dist p ctx.minPair_spec hcne.2)
  have hzre := supported_triangle_third_neighbor_re_le z choice.height
    choice.height_pos choice.height_sq hz hzi hsep1 hsepq

  have hcframe :
      edgeCoordinate (p partner) (p (v i)) (p c) = a + z * b := by
    dsimp [a, b, z]
    exact edgeCoordinate_affine_base_change _ _ _ _ _ hbaseNe hfiveNe
  have hpartner : partner = v (i + 1) :=
    choice.partner_eq_successor p hp hn v hv hh hrange hsupport i ctx
  have hcsupport : 0 ≤ turn (p (v i)) (p partner) (p c) := by
    rw [hpartner]
    exact hsupport i c
  have hcim : (a + z * b).im ≤ 0 := by
    have ht := edgeCoordinate_im_nonpos_of_support
      (p partner) (p (v i)) (p c) hbaseNe hcsupport
    rw [hcframe] at ht
    exact ht
  have hcW : a + z * b = 1 ∨ 1 ≤ ‖a + z * b - 1‖ := by
    by_cases heq : c = v i
    · left
      calc
        a + z * b = edgeCoordinate (p partner) (p (v i)) (p c) := hcframe.symm
        _ = 1 := by rw [heq, edgeCoordinate_axis _ _ hbaseNe]
    · right
      rw [← hcframe, edgeCoordinate_sub_one_norm _ _ _ hbaseNe,
        nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base]
      apply (le_div_iff₀ hδ).2
      simpa only [one_mul] using
        (isMinPair_le_dist p ctx.minPair_spec (Ne.symm heq))
  have hcB :
      a + z * b = (3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I ∨
        1 ≤ ‖a + z * b -
          ((3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I)‖ := by
    by_cases heq : c = choice.outer
    · left
      calc
        a + z * b = edgeCoordinate (p partner) (p (v i)) (p c) := hcframe.symm
        _ = (3 / 2 : ℂ) - (choice.height : ℂ) * Complex.I := by
          rw [heq, choice.outer_coordinate]
    · right
      rw [← hcframe, ← choice.outer_coordinate, ← dist_eq_norm,
        edgeCoordinate_dist _ _ _ _ hbaseNe,
        nearestGraph_adj_dist_eq p ctx.minPair_spec choice.base]
      apply (le_div_iff₀ hδ).2
      simpa only [one_mul] using
        (isMinPair_le_dist p ctx.minPair_spec heq)

  exact extension_shared_five_third_neighbor_impossible a b z choice.height
    choice.height_pos choice.height_sq hstrip.1 hstrip.2 hcore.1
    hcore.2.2.1 hcore.2.2.2.1 haw hcore.2.2.2.2 hz hzre hcim hcW hcB

end Erdos957
