import CertifiedSharedSix
import SharedFivePairReflection

/-! Refined predecessor-side shared-six certificates. The complete reflected
choice is retained, and its packet, branch rules and geometry are explicitly
interpreted in the original configuration. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Reflection preserves actual interior membership in a finite hull. -/
theorem mem_interior_convexHull_planeReflection_iff {n : ℕ}
    (p : Fin n → Point) (x : Point) :
    planeReflection x ∈ interior (convexHull ℝ (Set.range (fun i => planeReflection (p i)))) ↔
      x ∈ interior (convexHull ℝ (Set.range p)) := by
  have hrange : Set.range (fun i => planeReflection (p i)) =
      planeReflection '' Set.range p := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    aesop
  have hhull : convexHull ℝ (Set.range (fun i => planeReflection (p i))) =
      planeReflection '' convexHull ℝ (Set.range p) := by
    rw [hrange]
    exact (planeReflection.toLinearEquiv.toLinearMap.image_convexHull (Set.range p)).symm
  have hinterior : planeReflection '' interior (convexHull ℝ (Set.range p)) =
      interior (planeReflection '' convexHull ℝ (Set.range p)) :=
    planeReflection.toHomeomorph.image_interior _
  rw [hhull, ← hinterior]
  exact planeReflection.injective.mem_set_image

private theorem reflected_edge_coordinate_eq (u w x : Point) (z : ℂ)
    (hc : edgeCoordinate (planeReflection u) (planeReflection w) (planeReflection x) =
      z) :
    edgeCoordinate u w x = conj z := by
  rw [edgeCoordinate_planeReflection] at hc
  have h := congrArg (fun z : ℂ => conj z) hc
  simpa using h

/-- The mirrored rule records the same degree tests and actual witnesses,
with the imaginary coordinates interpreted in the original upper half-plane. -/
def ReflectedSharedSixReceiverRule {n : ℕ} (p : Fin n → Point)
    (u w v b t : Fin n) (h : ℝ) (k : Fin n) : Prop :=
  ((nearestGraph p).degree t ≤ 5 ∧ k = t) ∨
    ((nearestGraph p).degree t = 6 ∧ ∃ t₂ : Fin n,
      (nearestGraph p).Adj t t₂ ∧ (nearestGraph p).Adj b t₂ ∧
      p v + p t₂ = p t + p b ∧
      edgeCoordinate (p u) (p w) (p t₂) =
        (2 : ℂ) + ((2 * h : ℝ) : ℂ) * Complex.I ∧
      (((nearestGraph p).degree t₂ ≤ 5 ∧ k = t₂) ∨
        ((nearestGraph p).degree t₂ = 6 ∧ (nearestGraph p).Adj t₂ k ∧
          p k = 2 • p b - p v ∧
          edgeCoordinate (p u) (p w) (p k) =
            (5 / 2 : ℂ) + (h : ℂ) * Complex.I ∧
          (nearestGraph p).degree k ≤ 4)))

/-- The entire reflected certificate remains available after choosing it.
The original packet is obtained through the `packet` projection below. -/
structure ReflectedSharedSixPacketChoice {n : ℕ} (p : Fin n → Point)
    (u w v : Fin n) where
  reflected : SharedSixPacketChoice (fun i => planeReflection (p i)) u w v

namespace ReflectedSharedSixPacketChoice

noncomputable def packet {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) : LocalChargePacket p w :=
  choice.reflected.packet.of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))

theorem packet_sites {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    choice.packet.left = choice.reflected.outer ∧
      choice.packet.right = choice.reflected.packet.right := by
  exact ⟨choice.reflected.packet_left, rfl⟩

theorem packet_weight {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) (k : Fin n) :
    choice.packet.weight k = choice.reflected.packet.weight k := rfl

theorem original_neighbors {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    (nearestGraph p).degree v = 6 ∧
      (nearestGraph p).Adj v choice.reflected.outer ∧
      (nearestGraph p).Adj w choice.reflected.outer ∧
      (nearestGraph p).Adj v choice.reflected.lower ∧
      (nearestGraph p).Adj choice.reflected.outer choice.reflected.lower ∧
      (nearestGraph p).Adj choice.packet.left choice.packet.right ∧
      choice.packet.left ≠ choice.packet.right := by
  have hG := nearestGraph_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))
  have hdeg := nearestGraph_degree_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j)) v
  refine ⟨hdeg.symm.trans choice.reflected.center_degree,
    ?_, ?_, ?_, ?_, ?_, choice.reflected.sites_distinct⟩
  · simpa only [hG] using choice.reflected.outer_adj_center
  · simpa only [hG] using choice.reflected.outer_adj_source
  · simpa only [hG] using choice.reflected.lower_adj_center
  · simpa only [hG] using choice.reflected.outer_adj_lower
  · simpa only [packet, LocalChargePacket.of_dist_eq, hG] using choice.reflected.sites_adjacent

theorem original_identities {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    p u + p choice.reflected.outer = p v + p w ∧
      p w + p choice.reflected.lower = p v + p choice.reflected.outer := by
  constructor
  · have h := congrArg planeReflection choice.reflected.outer_identity
    simpa only [map_add, planeReflection_planeReflection] using h
  · have h := congrArg planeReflection choice.reflected.lower_identity
    simpa only [map_add, planeReflection_planeReflection] using h

theorem original_coordinates {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    edgeCoordinate (p u) (p w) (p v) =
        (1 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I ∧
      edgeCoordinate (p u) (p w) (p choice.reflected.outer) =
        (3 / 2 : ℂ) + (choice.reflected.height : ℂ) * Complex.I ∧
      edgeCoordinate (p u) (p w) (p choice.reflected.lower) =
        (1 : ℂ) + ((2 * choice.reflected.height : ℝ) : ℂ) * Complex.I := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [map_ofNat] using reflected_edge_coordinate_eq _ _ _ _ choice.reflected.center_coordinate
  · simpa [map_ofNat] using reflected_edge_coordinate_eq _ _ _ _ choice.reflected.outer_coordinate
  · simpa [map_ofNat] using reflected_edge_coordinate_eq _ _ _ _ choice.reflected.lower_coordinate

/-- All three selection branches hold for the original points, including
the earlier degree-six tests and the final degree-four bound. -/
theorem receiver_rule {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    ReflectedSharedSixReceiverRule p u w v choice.reflected.outer
      choice.reflected.lower choice.reflected.height choice.packet.right := by
  have hG := nearestGraph_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))
  have hdeg := nearestGraph_degree_eq_of_dist_eq p (fun i => planeReflection (p i))
    (fun i j => planeReflection.dist_map (p i) (p j))
  rcases choice.reflected.branch with hlow | ⟨htdeg, t₂, htt₂, hbt₂, hsum, hcoord, hcases⟩
  · exact Or.inl ⟨by simpa only [hdeg] using hlow.1, hlow.2⟩
  apply Or.inr
  refine ⟨by simpa only [hdeg] using htdeg, t₂,
    by simpa only [hG] using htt₂, by simpa only [hG] using hbt₂, ?_, ?_, ?_⟩
  · have h := congrArg planeReflection hsum
    simpa only [map_add, planeReflection_planeReflection] using h
  · simpa [map_ofNat] using reflected_edge_coordinate_eq _ _ _ _ hcoord
  · rcases hcases with hlow | ⟨hsix, htk, hid, hsite, hfour⟩
    · exact Or.inl ⟨by simpa only [hdeg] using hlow.1, hlow.2⟩
    · apply Or.inr
      refine ⟨by simpa only [hdeg] using hsix,
        by simpa only [packet, LocalChargePacket.of_dist_eq, hG] using htk,
        ?_, ?_, ?_⟩
      · have h := congrArg planeReflection hid
        simpa only [packet, LocalChargePacket.of_dist_eq, map_sub, two_smul, map_add,
          planeReflection_planeReflection] using h
      · simpa [map_ofNat, packet, LocalChargePacket.of_dist_eq] using
          reflected_edge_coordinate_eq _ _ _ _ hsite
      · exact (hdeg choice.reflected.packet.right).symm.le.trans hfour

/-- The actual original coordinates lie in the upper mirrored receiving
region, rather than the lower region of the reflected certificate. -/
theorem receivers_in_original_region {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) (k : Fin n)
    (hk : 0 < choice.packet.weight k) :
    let z := edgeCoordinate (p u) (p w) (p k);
    0 ≤ z.re ∧ z.re ≤ 5 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ 2 ∧
      (z.re ≤ 2 ∨ z.im ≤ 1) := by
  have hr := choice.reflected.receivers_in_region k hk
  simp only [edgeCoordinate_planeReflection, sharedReceiverRegion,
    Complex.conj_re, Complex.conj_im] at hr
  obtain ⟨hxlo, hxhi, hylo, hyhi, hshape⟩ := hr
  refine ⟨hxlo, hxhi, by linarith, by linarith, ?_⟩
  rcases hshape with hx | hy
  · exact Or.inl hx
  · exact Or.inr (by linarith)

/-- Every positive receiver is interior in the original hull. -/
theorem receivers_in_original_interior {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) (k : Fin n)
    (hk : 0 < choice.packet.weight k) :
    p k ∈ interior (convexHull ℝ (Set.range p)) :=
  (mem_interior_convexHull_planeReflection_iff p (p k)).mp
    (choice.reflected.receivers_interior k hk)

theorem site_weights {n : ℕ} {p : Fin n → Point} {u w v : Fin n}
    (choice : ReflectedSharedSixPacketChoice p u w v) :
    choice.packet.weight choice.packet.left = 1 ∧
      choice.packet.weight choice.packet.right = 1 :=
  choice.reflected.site_weights

end ReflectedSharedSixPacketChoice

/-- The actual predecessor configuration yields a full refined certificate,
using the original donor's own tight-flat neighborhood. -/
noncomputable def reflectedSharedSixPacketChoice_of_tight_flat_hull
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
      dist (p (v (i - 1))) (p j)) :
    ReflectedSharedSixPacketChoice p (v (i - 1)) (v i) q := by
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
  let choiceR := sharedSixPacketChoice_of_tight_flat_hull pR hn hpR
    (reversedHullCycle v) hvR hh hrangeR hsupportR hposR (-i) q j
    (by simpa only [hG, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hbase)
    (by simpa only [hG, reversedHullCycle_neg_successor] using hqu)
    (by simpa only [hG, reversedHullCycle_neg] using hqw)
    (hdeg.trans hqdeg) hgoodR
    (by simpa only [hD, reversedHullCycle_neg_successor] using hdiam)
    (by simpa only [hdist, reversedHullCycle_neg, reversedHullCycle_neg_successor] using hscale)
  have choice : SharedSixPacketChoice pR (v (i - 1)) (v i) q := by
    simpa only [reversedHullCycle_neg, reversedHullCycle_neg_successor] using choiceR
  exact ⟨choice⟩

/-- Actual diameter membership supplies a partner and the existing large
cardinality bound supplies the required scale. No new exception is introduced. -/
noncomputable def reflectedSharedSixPacketChoice_of_large_card
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
    (hu : v (i - 1) ∈ diameterEndpoints p) :
    ReflectedSharedSixPacketChoice p (v (i - 1)) (v i) q := by
  apply Classical.choice
  obtain ⟨j, hdiam⟩ := (mem_diameterEndpoints_iff_exists_adj p (v (i - 1))).mp hu
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega : 2 ≤ n)
  have hscale : 10 * dist (p (v (i - 1))) (p (v i)) <
      dist (p (v (i - 1))) (p j) := by
    rw [nearestGraph_adj_dist_eq p hmin hbase.symm,
      (diameterGraph_adj_iff_dist_eq p hp hmax _ _).mp hdiam]
    exact ten_mul_min_lt_max_of_large_card p hp hn hmin hmax
  exact ⟨reflectedSharedSixPacketChoice_of_tight_flat_hull p (by omega) hp
    v hv hh hrange hsupport hpos i q j hbase hqu hqw hqdeg hgood hdiam hscale⟩

end Erdos957
