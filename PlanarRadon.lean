import ExtremeSubsets
import Mathlib.Analysis.Convex.Radon

/-!
Radon partitions of four planar points. The affine-dependence step uses that
the Euclidean plane has real dimension two.
-/

namespace Erdos957

/-- Any four plane points have a Radon partition. -/
theorem four_point_radon_partition (p : Fin 4 → Point) :
    ∃ I : Set (Fin 4),
      (convexHull ℝ (p '' I) ∩ convexHull ℝ (p '' Iᶜ)).Nonempty := by
  have hdep : ¬ AffineIndependent ℝ p := by
    apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ p
      (n := 2) (by decide)).mp
    calc
      Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ Module.finrank ℝ Point :=
        Submodule.finrank_le _
      _ = 2 := by simp [Point]
  exact Convex.radon_partition hdep

private theorem two_element_subsets_fin_four :
    ∀ I : Finset (Fin 4), I.card = 2 →
      I = {0, 1} ∨ I = {0, 2} ∨ I = {0, 3} ∨
      I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3} := by
  decide

/-- A Radon partition of four distinct extreme points of their hull must
split the indices two against two. -/
theorem extreme_radon_partition_card_two (q : Fin 4 → Point)
    (hq : Function.Injective q)
    (hext : ∀ i, q i ∈ (convexHull ℝ (Set.range q)).extremePoints ℝ)
    (I : Set (Fin 4))
    (hinter : (convexHull ℝ (q '' I) ∩ convexHull ℝ (q '' Iᶜ)).Nonempty) :
    I.ncard = 2 := by
  classical
  obtain ⟨x, hxI, hxIc⟩ := hinter
  have hn0 : I.ncard ≠ 0 := by
    intro hn
    have hI : I = ∅ := (Set.ncard_eq_zero (s := I)).mp hn
    simp [hI] at hxI
  have hn1 : I.ncard ≠ 1 := by
    intro hn
    obtain ⟨i, hI⟩ := Set.ncard_eq_one.mp hn
    have hxi : x = q i := by simpa [hI, convexHull_singleton] using hxI
    have hqi : q i ∈ convexHull ℝ (q '' ({i} : Set (Fin 4))ᶜ) := by
      simpa [hI, hxi] using hxIc
    exact (extreme_not_mem_convexHull_image q hq i (hext i)
      ({i} : Set (Fin 4))ᶜ (by simp)) hqi
  have hcn0 : Iᶜ.ncard ≠ 0 := by
    intro hn
    have hIc : Iᶜ = ∅ := (Set.ncard_eq_zero (s := Iᶜ)).mp hn
    simp [hIc] at hxIc
  have hcn1 : Iᶜ.ncard ≠ 1 := by
    intro hn
    obtain ⟨i, hIc⟩ := Set.ncard_eq_one.mp hn
    have hxi : x = q i := by simpa [hIc, convexHull_singleton] using hxIc
    have hI : I = ({i} : Set (Fin 4))ᶜ := by
      calc
        I = Iᶜᶜ := by simp
        _ = ({i} : Set (Fin 4))ᶜ := congrArg (fun S : Set (Fin 4) => Sᶜ) hIc
    have hqi : q i ∈ convexHull ℝ (q '' ({i} : Set (Fin 4))ᶜ) := by
      simpa [hxi, hI] using hxI
    exact (extreme_not_mem_convexHull_image q hq i (hext i)
      ({i} : Set (Fin 4))ᶜ (by simp)) hqi
  have hsum : I.ncard + Iᶜ.ncard = 4 := by
    simpa using (Set.ncard_add_ncard_compl I)
  omega

/-- Among four distinct extreme points of their planar convex hull, one of
the three pairings into two segments has an intersection. -/
theorem four_extreme_points_have_crossing (q : Fin 4 → Point)
    (hq : Function.Injective q)
    (hext : ∀ i, q i ∈ (convexHull ℝ (Set.range q)).extremePoints ℝ) :
    (segment ℝ (q 0) (q 1) ∩ segment ℝ (q 2) (q 3)).Nonempty ∨
    (segment ℝ (q 0) (q 2) ∩ segment ℝ (q 1) (q 3)).Nonempty ∨
    (segment ℝ (q 0) (q 3) ∩ segment ℝ (q 1) (q 2)).Nonempty := by
  classical
  obtain ⟨I, hradon⟩ := four_point_radon_partition q
  have hcard := extreme_radon_partition_card_two q hq hext I hradon
  have hfinCard : I.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card' I]
    exact hcard
  have hcases := two_element_subsets_fin_four I.toFinset hfinCard
  have hco : ((I.toFinset : Finset (Fin 4)) : Set (Fin 4)) = I := by simp
  have hpair (a b c d : Fin 4)
      (hI : I = ({a, b} : Set (Fin 4)))
      (hIc : Iᶜ = ({c, d} : Set (Fin 4))) :
      (segment ℝ (q a) (q b) ∩ segment ℝ (q c) (q d)).Nonempty := by
    have hradon' := hradon
    rw [hIc] at hradon'
    rw [hI] at hradon'
    simpa only [Set.image_pair, convexHull_pair] using hradon'
  rcases hcases with h | h | h | h | h | h
  · have hI : I = ({0, 1} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    left
    apply hpair 0 1 2 3 hI
    rw [hI]
    ext i
    fin_cases i <;> simp
  · have hI : I = ({0, 2} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    right; left
    apply hpair 0 2 1 3 hI
    rw [hI]
    ext i
    fin_cases i <;> simp
  · have hI : I = ({0, 3} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    right; right
    apply hpair 0 3 1 2 hI
    rw [hI]
    ext i
    fin_cases i <;> simp
  · have hI : I = ({1, 2} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    right; right
    have h := hpair 1 2 0 3 hI (by
      rw [hI]
      ext i
      fin_cases i <;> simp)
    simpa only [Set.inter_comm] using h
  · have hI : I = ({1, 3} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    right; left
    have h := hpair 1 3 0 2 hI (by
      rw [hI]
      ext i
      fin_cases i <;> simp)
    simpa only [Set.inter_comm] using h
  · have hI : I = ({2, 3} : Set (Fin 4)) := by
      rw [h] at hco
      simpa only [Finset.coe_insert, Finset.coe_singleton] using hco.symm
    left
    have h := hpair 2 3 0 1 hI (by
      rw [hI]
      ext i
      fin_cases i <;> simp)
    simpa only [Set.inter_comm] using h

end Erdos957
