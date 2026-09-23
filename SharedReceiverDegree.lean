import HullEdgeBeyond
import TruncatedCirclePacking
import NormalizedEdgeGeometry
import NearestBound
import Mathlib.Tactic.Linarith

/-! A normalized shared-receiver pattern forces degree at most four. -/

namespace Erdos957

open scoped ComplexConjugate

/-- The two named neighbors of `d` forbid two arcs of its unit neighbor
circle. Every remaining neighbor is strictly below the supporting line at
the extreme vertex `w`, so the truncated-circle packing bound applies. -/
theorem normalized_shared_receiver_degree_le_four {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w b t2 d : Fin n}
    (huw : (nearestGraph p).Adj u w)
    (hw : w ∈ hullVertexIndices p)
    (hsupp : ∀ k : Fin n, 0 ≤ turn (p w) (p u) (p k))
    (h : ℝ) (hh : 0 < h) (hh_sq : h ^ 2 = 3 / 4)
    (hb : edgeCoordinate (p u) (p w) (p b) =
      (3 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (ht : edgeCoordinate (p u) (p w) (p t2) =
      (2 : ℂ) - (2 * h : ℝ) * Complex.I)
    (hd : edgeCoordinate (p u) (p w) (p d) =
      (5 / 2 : ℂ) - (h : ℂ) * Complex.I)
    (hdb : (nearestGraph p).Adj d b)
    (hdt : (nearestGraph p).Adj d t2) :
    (nearestGraph p).degree d ≤ 4 := by
  classical
  let G := nearestGraph p
  let C : Point → ℂ := edgeCoordinate (p u) (p w)
  let f : Fin n → ℂ := fun k => C (p k) - C (p d)
  have huwne : u ≠ w := G.ne_of_adj huw
  have hpne : p u ≠ p w := hp.ne huwne
  have hCdRe : (C (p d)).re = 5 / 2 := by
    have heq := congrArg Complex.re hd
    norm_num at heq ⊢
    exact heq
  have hCdIm : (C (p d)).im = -h := by
    have heq := congrArg Complex.im hd
    simpa [C] using heq
  have hfB : f b = -1 := by
    dsimp [f, C]
    rw [hb, hd]
    ring
  have hfT : f t2 = (-1 / 2 : ℂ) - (h : ℂ) * Complex.I := by
    dsimp [f, C]
    rw [ht, hd]
    push_cast
    ring
  have hbt : b ≠ t2 := by
    intro hbeq
    have heq := congrArg f hbeq
    rw [hfB, hfT] at heq
    have hre := congrArg Complex.re heq
    norm_num at hre
  let M : Finset (Fin n) := G.neighborFinset d
  let N : Finset (Fin n) := (M.erase b).erase t2
  let S : Finset ℂ := N.image f
  have hbmem : b ∈ M := (G.mem_neighborFinset d b).mpr hdb
  have htmem : t2 ∈ M := (G.mem_neighborFinset d t2).mpr hdt
  have htmem' : t2 ∈ M.erase b := Finset.mem_erase.mpr ⟨hbt.symm, htmem⟩
  have hcardN : N.card + 2 = G.degree d := by
    have h1 := Finset.card_erase_add_one hbmem
    have h2 := Finset.card_erase_add_one htmem'
    have h3 := G.card_neighborFinset_eq_degree d
    change (M.erase b).card + 1 = M.card at h1
    change N.card + 1 = (M.erase b).card at h2
    change M.card = G.degree d at h3
    omega
  have hfinj : Function.Injective f := by
    intro k l heq
    apply hp
    apply edgeCoordinate_injective (p u) (p w) hpne
    have h := congrArg (fun z : ℂ => z + C (p d)) heq
    simpa [f] using h
  have hcardS : S.card = N.card := Finset.card_image_of_injective N hfinj
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have huwdist : dist (p u) (p w) = r := nearestGraph_adj_dist_eq p hmin huw
  have hunit_of_adj (k : Fin n) (hdk : G.Adj d k) : ‖f k‖ = 1 := by
    have hdist : dist (p k) (p d) = r := by
      simpa only [dist_comm] using (nearestGraph_adj_dist_eq p hmin hdk)
    dsimp [f, C]
    rw [← dist_eq_norm, edgeCoordinate_dist (p u) (p w) (p k) (p d) hpne]
    rw [hdist, huwdist]
    exact div_self hr.ne'
  have hdist_of_ne (k l : Fin n) (hkl : k ≠ l) :
      (1 : ℝ) ≤ dist (f k) (f l) := by
    have hsep := isMinPair_le_dist p hmin hkl
    have hden : 0 < dist (p u) (p w) := dist_pos.mpr hpne
    have hquot : (1 : ℝ) ≤ dist (p k) (p l) / dist (p u) (p w) := by
      apply (le_div_iff₀ hden).mpr
      rw [one_mul, huwdist]
      exact hsep
    dsimp [f, C]
    simpa only [dist_sub_right, edgeCoordinate_dist (p u) (p w) (p k) (p l) hpne]
      using hquot
  have hNmem (k : Fin n) (hk : k ∈ N) :
      k ≠ b ∧ k ≠ t2 ∧ G.Adj d k := by
    have ⟨hkt, hkbM⟩ := Finset.mem_erase.mp hk
    have ⟨hkb, hkM⟩ := Finset.mem_erase.mp hkbM
    exact ⟨hkb, hkt, (G.mem_neighborFinset d k).mp hkM⟩
  have hunit : ∀ z ∈ S, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hunit_of_adj k (hNmem k hk).2.2
  have hB : ∀ z ∈ S, (1 : ℝ) ≤ dist z (-1) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have h := hdist_of_ne k b (hNmem k hk).1
    rwa [hfB] at h
  have hT : ∀ z ∈ S, (1 : ℝ) ≤
      dist z ((-1 / 2 : ℂ) - (h : ℂ) * Complex.I) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have h' := hdist_of_ne k t2 (hNmem k hk).2.1
    rwa [hfT] at h'
  have hbelow : ∀ z ∈ S, z.im < h := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hknorm := hunit_of_adj k (hNmem k hk).2.2
    have hrelo : -1 ≤ (f k).re := by
      have habs := Complex.abs_re_le_norm (f k)
      rw [hknorm] at habs
      exact (abs_le.mp habs).1
    have hfre : (f k).re = (C (p k)).re - 5 / 2 := by
      dsimp [f]
      rw [hCdRe]
    have hkre : 1 < (C (p k)).re := by linarith
    have hkim : (C (p k)).im ≤ 0 :=
      edgeCoordinate_im_nonpos_of_support (p u) (p w) (p k) hpne (hsupp k)
    have hkim' : (C (p k)).im < 0 :=
      hull_extreme_normalized_beyond_im_neg p hp huwne hw hkre hkim
    dsimp [f]
    rw [hCdIm]
    linarith
  have hsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → (1 : ℝ) ≤ dist z z' := by
    intro z hz z' hz' hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz'
    have hkl : k ≠ l := by
      intro heq
      exact hne (congrArg f heq)
    exact hdist_of_ne k l hkl
  have hS : S.card ≤ 2 :=
    truncated_circle_card_le_two S h hh hh_sq hunit hB hT hbelow hsep
  change N.card + 2 = (nearestGraph p).degree d at hcardN
  omega

end Erdos957
