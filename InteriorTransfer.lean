import SixNeighborStructure
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! An interior criterion for centrally symmetric full-dimensional convex hulls. -/

namespace Erdos957

open scoped EuclideanGeometry

/-- If a planar set spans the plane and is invariant under reflection through
`x`, then `x` is an interior point of its convex hull. -/
theorem mem_interior_convexHull_of_reflection (s : Set Point) (x : Point)
    (hspan : affineSpan ℝ s = ⊤)
    (hsym : ∀ y ∈ s, AffineEquiv.pointReflection ℝ x y ∈ s) :
    x ∈ interior (convexHull ℝ s) := by
  let R := AffineEquiv.pointReflection ℝ x
  have hRsub : R '' s ⊆ s := by
    rintro y ⟨z, hz, rfl⟩
    exact hsym z hz
  have hCsub : R '' convexHull ℝ s ⊆ convexHull ℝ s := by
    rw [show R '' convexHull ℝ s = convexHull ℝ (R '' s) from
      R.toAffineMap.image_convexHull s]
    exact convexHull_mono hRsub
  obtain ⟨q, hq⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hRq : R q ∈ convexHull ℝ s := hCsub ⟨q, interior_subset hq, rfl⟩
  have hmid : (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • R q = x := by
    change (1 / 2 : ℝ) • q + (1 / 2 : ℝ) •
      (AffineEquiv.pointReflection ℝ x q) = x
    rw [AffineEquiv.pointReflection_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hinside := (convex_convexHull ℝ s).combo_interior_self_mem_interior
    hq hRq (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [hmid] using hinside

/-- An equilateral triangle of positive side length is noncollinear. -/
private theorem equilateral_not_collinear (x y z : Point) (r : ℝ)
    (hr : 0 < r) (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : dist y z = r) :
    ¬ Collinear ℝ ({y, x, z} : Set Point) := by
  intro hcol
  rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcol with
    hyx | hzx | hzero | hpi
  · simp [hyx] at hxy
    linarith
  · simp [hzx] at hxz
    linarith
  · have hlaw := EuclideanGeometry.law_cos y x z
    rw [hyz, dist_comm y x, hxy, dist_comm z x, hxz, hzero, Real.cos_zero] at hlaw
    nlinarith [sq_pos_of_pos hr]
  · have hlaw := EuclideanGeometry.law_cos y x z
    rw [hyz, dist_comm y x, hxy, dist_comm z x, hxz, hpi, Real.cos_pi] at hlaw
    nlinarith [sq_pos_of_pos hr]

/-- A point with six nearest neighbors lies in the topological interior of
the convex hull of the entire configuration. The six neighbors form a regular
hexagon around the point; two adjacent neighbors witness full dimension and
every neighbor has its reflection through the center in the same set. -/
theorem degree_six_mem_interior_convexHull {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) (u : Fin n)
    (hdegree : (nearestGraph p).degree u = 6) :
    p u ∈ interior (convexHull ℝ (Set.range p)) := by
  classical
  let G := nearestGraph p
  let N : Finset Point := (G.neighborFinset u).image p
  obtain ⟨v, _hvinj, hcover, hcycle, _hargs⟩ :=
    nearestGraph_degree_six_regular p hn hp u hdegree
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hadj0 : G.Adj u (v 0) := (hcover _).mpr ⟨0, rfl⟩
  have hadj1 : G.Adj u (v 1) := (hcover _).mpr ⟨1, rfl⟩
  have hadj01 : G.Adj (v 0) (v 1) := by simpa using hcycle 0
  have hr0 : dist (p u) (p (v 0)) = r := nearestGraph_adj_dist_eq p hmin hadj0
  have hr1 : dist (p u) (p (v 1)) = r := nearestGraph_adj_dist_eq p hmin hadj1
  have hr01 : dist (p (v 0)) (p (v 1)) = r :=
    nearestGraph_adj_dist_eq p hmin hadj01
  have hnotcol : ¬ Collinear ℝ ({p (v 0), p u, p (v 1)} : Set Point) :=
    equilateral_not_collinear (p u) (p (v 0)) (p (v 1)) r hr hr0 hr1 hr01
  have hInd : AffineIndependent ℝ ![p (v 0), p u, p (v 1)] :=
    affineIndependent_iff_not_collinear_set.mpr hnotcol
  have hspanTri : affineSpan ℝ (Set.range ![p (v 0), p u, p (v 1)]) = ⊤ :=
    hInd.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Point])
  have hmemN (j : Fin n) (huj : G.Adj u j) : p j ∈ N :=
    Finset.mem_image.mpr ⟨j, (G.mem_neighborFinset u j).mpr huj, rfl⟩
  obtain ⟨k, hk, _hkj, hpair⟩ :=
    degree_six_neighbor_has_antipode p hn hp hdegree hadj0
  have hmid : (1 / 2 : ℝ) • p (v 0) + (1 / 2 : ℝ) • p k = p u := by
    calc
      (1 / 2 : ℝ) • p (v 0) + (1 / 2 : ℝ) • p k =
          (1 / 2 : ℝ) • (p (v 0) + p k) := by module
      _ = (1 / 2 : ℝ) • (2 • p u) := by rw [hpair]
      _ = p u := by module
  have huC : p u ∈ convexHull ℝ (N : Set Point) := by
    have h := (convex_convexHull ℝ (N : Set Point))
      (subset_convexHull ℝ (N : Set Point) (hmemN (v 0) hadj0))
      (subset_convexHull ℝ (N : Set Point) (hmemN k hk))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simpa only [hmid] using h
  have huSpan : p u ∈ affineSpan ℝ (N : Set Point) :=
    convexHull_subset_affineSpan (N : Set Point) huC
  have hspanN : affineSpan ℝ (N : Set Point) = ⊤ := by
    have hsub : Set.range ![p (v 0), p u, p (v 1)] ⊆
        (affineSpan ℝ (N : Set Point) : Set Point) := by
      rintro q ⟨i, rfl⟩
      fin_cases i
      · exact subset_affineSpan ℝ (N : Set Point) (hmemN (v 0) hadj0)
      · exact huSpan
      · exact subset_affineSpan ℝ (N : Set Point) (hmemN (v 1) hadj1)
    have hle : affineSpan ℝ (Set.range ![p (v 0), p u, p (v 1)]) ≤
        affineSpan ℝ (N : Set Point) := affineSpan_le.mpr hsub
    rw [hspanTri] at hle
    exact top_unique hle
  have hsym : ∀ y ∈ (N : Set Point),
      AffineEquiv.pointReflection ℝ (p u) y ∈ (N : Set Point) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have huj : G.Adj u j := (G.mem_neighborFinset u j).mp hj
    obtain ⟨j', hj', _hne, hsum⟩ :=
      degree_six_neighbor_has_antipode p hn hp hdegree huj
    have href : AffineEquiv.pointReflection ℝ (p u) (p j) = p j' := by
      rw [AffineEquiv.pointReflection_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      have hh : p u + p u = p j + p j' := by simpa [two_smul] using hsum.symm
      calc
        p u - p j + p u = p u + p u - p j := by abel
        _ = (p j + p j') - p j := by rw [hh]
        _ = p j' := by abel
    rw [href]
    exact hmemN j' hj'
  have huInterior : p u ∈ interior (convexHull ℝ (N : Set Point)) :=
    mem_interior_convexHull_of_reflection (N : Set Point) (p u) hspanN hsym
  have hNsub : (N : Set Point) ⊆ Set.range p := by
    intro y hy
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨j, rfl⟩
  exact interior_mono (convexHull_mono hNsub) huInterior

end Erdos957
