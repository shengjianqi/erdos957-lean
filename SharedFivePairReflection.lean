import SharedFivePairSelection
import ConfigurationCongruence
import ReflectedHull

/-! Reflection with endpoint reversal preserves a coordinated shared-five
selection, including the depth, coordinate rectangle, and receiver order. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Reversing the base edge changes its normalized coordinate to `1-z`. -/
theorem edgeCoordinate_swap_base (u w x : Point) (hne : u ≠ w) :
    edgeCoordinate w u x = 1 - edgeCoordinate u w x := by
  have hd : pointToComplex (w - u) ≠ 0 := by
    intro hzero
    have hsub : w - u = 0 := pointToComplex.injective (by simpa using hzero)
    exact hne (sub_eq_zero.mp hsub).symm
  have hnum : pointToComplex (x - w) =
      pointToComplex (x - u) - pointToComplex (w - u) := by
    rw [← map_sub]
    congr 1
    abel
  have hden : pointToComplex (u - w) = -pointToComplex (w - u) := by
    rw [← map_neg]
    congr 1
    abel
  simp only [edgeCoordinate, hnum, hden]
  field_simp
  ring

/-- Plane reflection conjugates normalized complex coordinates. -/
theorem edgeCoordinate_planeReflection (u w x : Point) :
    edgeCoordinate (planeReflection u) (planeReflection w) (planeReflection x) =
      conj (edgeCoordinate u w x) := by
  simp only [edgeCoordinate, ← map_sub, pointToComplex_planeReflection, map_div₀]

/-- Simultaneously reflecting the plane and reversing the edge preserves
height and sends the horizontal coordinate to `1-x`. -/
theorem edgeCoordinate_planeReflection_swap (u w x : Point) (hne : u ≠ w) :
    edgeCoordinate (planeReflection w) (planeReflection u) (planeReflection x) =
      1 - conj (edgeCoordinate u w x) := by
  rw [edgeCoordinate_planeReflection, edgeCoordinate_swap_base u w x hne]
  simp only [map_sub, map_one]

/-- Transport both coordinated packets from reflected coordinates while
swapping their source roles. All selection evidence survives the transport. -/
noncomputable def SharedFivePairSelection.of_reflection_swap {n : ℕ}
    (p : Fin n → Point) {u w q : Fin n} (hne : p u ≠ p w)
    (choice : SharedFivePairSelection (fun i => planeReflection (p i)) w u q) :
    SharedFivePairSelection p u w q := by
  let pR : Fin n → Point := fun i => planeReflection (p i)
  change SharedFivePairSelection pR w u q at choice
  have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
    planeReflection.dist_map _ _
  have hG := nearestGraph_eq_of_dist_eq p pR hdist
  have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
  have hdeg := nearestGraph_degree_eq_of_dist_eq p pR hdist
  have him (a : Fin n) : (edgeCoordinate (pR w) (pR u) (pR a)).im =
      (edgeCoordinate (p u) (p w) (p a)).im := by
    dsimp [pR]
    rw [edgeCoordinate_planeReflection_swap _ _ _ hne]
    simp
  have hre (a : Fin n) : (edgeCoordinate (pR w) (pR u) (pR a)).re =
      1 - (edgeCoordinate (p u) (p w) (p a)).re := by
    dsimp [pR]
    rw [edgeCoordinate_planeReflection_swap _ _ _ hne]
    simp
  refine {
    bottom := choice.bottom
    bottom_adj := by simpa only [hG] using choice.bottom_adj
    bottom_ne_left := choice.bottom_ne_right
    bottom_ne_right := choice.bottom_ne_left
    bottom_minimal := ?_
    bottom_depth := ?_
    diameter_neighbors := ?_
    first := choice.second.of_dist_eq p pR hdist
    second := choice.first.of_dist_eq p pR hdist
    first_central := choice.second_central
    second_central := choice.first_central
    first_secondary := ?_
    second_secondary := ?_
    branch := ?_
    receivers_in_rectangle := ?_
  }
  · intro a hqa hau haw
    have ht := choice.bottom_minimal a (by simpa only [hG] using hqa) haw hau
    simpa only [him] using ht
  · simpa only [him] using choice.bottom_depth
  · intro a hqa haD
    exact (choice.diameter_neighbors a (by simpa only [hG] using hqa)
      (by simpa only [hD] using haD)).symm
  · exact ⟨by simpa only [LocalChargePacket.of_dist_eq, hG] using choice.second_secondary.1,
      choice.second_secondary.2.2, choice.second_secondary.2.1⟩
  · exact ⟨by simpa only [LocalChargePacket.of_dist_eq, hG] using choice.first_secondary.1,
      choice.first_secondary.2.2, choice.first_secondary.2.1⟩
  · rcases choice.branch with hlow | hhigh
    · exact Or.inl ⟨by simpa only [hdeg] using hlow.1, hlow.2.2, hlow.2.1⟩
    · apply Or.inr
      refine ⟨by simpa only [hdeg] using hhigh.1, hhigh.2.1.symm,
        by simpa only [LocalChargePacket.of_dist_eq, hG] using hhigh.2.2.2.1,
        by simpa only [LocalChargePacket.of_dist_eq, hG] using hhigh.2.2.1, ?_⟩
      have hs := hhigh.2.2.2.2
      rw [hre, hre] at hs
      change (edgeCoordinate (p u) (p w) (p choice.second.right)).re ≤
        (edgeCoordinate (p u) (p w) (p choice.first.right)).re
      linarith
  · intro a ha
    change 0 < choice.second.weight a ∨ 0 < choice.first.weight a at ha
    obtain ⟨hxlo, hxhi, hylo, hyhi⟩ := choice.receivers_in_rectangle a ha.symm
    rw [hre] at hxlo hxhi
    rw [him] at hylo hyhi
    exact ⟨by linarith, by linarith, hylo, hyhi⟩

/-- One good endpoint suffices to construct a joint selection in the fixed
original orientation. The reflected branch retains all coordinated fields. -/
noncomputable def sharedFivePairSelection_of_either_tight_flat_endpoint
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
    (hgood : v i ∉ tightHullBadVertices p v ∨
      v (i + 1) ∉ tightHullBadVertices p v)
    (hu : v (i + 1) ∈ diameterEndpoints p) (hw : v i ∈ diameterEndpoints p) :
    SharedFivePairSelection p (v (i + 1)) (v i) q := by
  apply Classical.choice
  rcases hgood with hgood | hgood
  · exact ⟨sharedFivePairSelection_of_tight_flat_hull p hp hn v hv hh
      hsupport hpos i q hbase hqu hqw hqdeg hgood hu hw⟩
  · let pR : Fin n → Point := fun k => planeReflection (p k)
    let vR := reversedHullCycle v
    let jR : Fin h := -(i + 1)
    have hpR : Function.Injective pR := planeReflection.injective.comp hp
    have hvR : Function.Injective vR := reversedHullCycle_injective v hv
    have hdist (a b : Fin n) : dist (pR a) (pR b) = dist (p a) (p b) :=
      planeReflection.dist_map _ _
    have hG := nearestGraph_eq_of_dist_eq p pR hdist
    have hD := diameterEndpoints_eq_of_dist_eq p pR hdist
    have hdeg := nearestGraph_degree_eq_of_dist_eq p pR hdist q
    have hcurrent : vR jR = v (i + 1) := reversedHullCycle_neg v (i + 1)
    have hnext : vR (jR + 1) = v i := by
      have hj : jR + 1 = -i := by dsimp [jR]; abel
      rw [hj]
      exact reversedHullCycle_neg v i
    have hsupportR : ∀ a k, 0 ≤ turn (pR (vR a)) (pR (vR (a + 1))) (pR k) :=
      reflectedHull_support p v hsupport
    have hposR : ∀ a, 0 < hullExteriorAngle pR vR a := by
      intro a
      simpa only [pR, vR, hullExteriorAngle_planeReflection_reversed] using hpos (-a)
    have hgoodR : vR jR ∉ tightHullBadVertices pR vR := by
      apply tightHull_not_bad_planeReflection_reversed p v hv jR
      simpa only [jR, neg_neg] using hgood
    let choiceR := sharedFivePairSelection_of_tight_flat_hull pR hpR hn vR hvR hh
      hsupportR hposR jR q
      (by simpa only [hG, hcurrent, hnext] using hbase.symm)
      (by simpa only [hG, hnext] using hqw)
      (by simpa only [hG, hcurrent] using hqu)
      (hdeg.trans hqdeg) hgoodR
      (by simpa only [hD, hnext] using hw)
      (by simpa only [hD, hcurrent] using hu)
    have choice : SharedFivePairSelection pR (v i) (v (i + 1)) q := by
      simpa only [hcurrent, hnext] using choiceR
    exact ⟨choice.of_reflection_swap p (hp.ne hbase.ne.symm)⟩

end Erdos957
