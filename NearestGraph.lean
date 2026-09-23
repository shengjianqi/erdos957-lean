import Foundations
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The nearest-neighbor graph for Erdős problem 957

An edge joins two indices exactly when their points realize the minimum
pairwise distance.  The graph is built from the canonical `i < j`
representation in `Foundations`.
-/

namespace Erdos957

/-- The simple graph whose edges are minimum-distance pairs. -/
def nearestGraph {n : ℕ} (p : Fin n → Point) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => isMinPair p (i, j))

noncomputable instance nearestGraphAdjDecidable {n : ℕ} (p : Fin n → Point) :
    DecidableRel (nearestGraph p).Adj := Classical.decRel _

theorem nearestGraph_adj_iff {n : ℕ} (p : Fin n → Point) (i j : Fin n) :
    (nearestGraph p).Adj i j ↔
      isMinPair p (i, j) ∨ isMinPair p (j, i) := by
  simp only [nearestGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    constructor
    · rcases h with h | h
      · exact ne_of_lt (mem_pairs_iff.mp h.1)
      · exact (ne_of_lt (mem_pairs_iff.mp h.1)).symm
    · exact h

/-- A minimum-distance pair is no longer than any other distinct ordered pair. -/
theorem isMinPair_le_dist {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hij : isMinPair p ij)
    {k l : Fin n} (hkl : k ≠ l) :
    pairDist p ij ≤ dist (p k) (p l) := by
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact hij.2 (k, l) (mem_pairs_iff.mpr hlt)
  · have h := hij.2 (l, k) (mem_pairs_iff.mpr hgt)
    simpa [pairDist, dist_comm] using h

/-- The graph edges are exactly the pairs counted by `sMin`. -/
theorem sMin_eq_card_edgeFinset {n : ℕ} (p : Fin n → Point) :
    sMin p = (nearestGraph p).edgeFinset.card := by
  classical
  unfold sMin
  refine Finset.card_bij
    (s := (pairs n).filter (isMinPair p))
    (t := (nearestGraph p).edgeFinset)
    (fun (ij : Fin n × Fin n) _ => Sym2.mk ij.1 ij.2) ?_ ?_ ?_
  · intro ij hij
    have hmin : isMinPair p ij := (Finset.mem_filter.mp hij).2
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
      (nearestGraph_adj_iff p ij.1 ij.2).mpr (Or.inl hmin)
  · intro a ha b hb heq
    have ha' : a.1 < a.2 := mem_pairs_iff.mp (Finset.mem_filter.mp ha).1
    have hb' : b.1 < b.2 := mem_pairs_iff.mp (Finset.mem_filter.mp hb).1
    rcases Sym2.mk_eq_mk_iff.mp heq with h | h
    · exact h
    · have hba : b.2 < b.1 := by simpa [h] using ha'
      exact False.elim (lt_asymm hba hb')
  · intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
      have hadj : (nearestGraph p).Adj i j := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rcases (nearestGraph_adj_iff p i j).mp hadj with hij | hji
      · exact ⟨(i, j), Finset.mem_filter.mpr ⟨hij.1, hij⟩, rfl⟩
      · exact ⟨(j, i), Finset.mem_filter.mpr ⟨hji.1, hji⟩, Sym2.eq_swap⟩

/-- Handshaking for the minimum-distance graph, with its edges counted by `sMin`. -/
theorem nearestGraph_handshake {n : ℕ} (p : Fin n → Point) :
    ∑ i : Fin n, (nearestGraph p).degree i = 2 * sMin p := by
  rw [sMin_eq_card_edgeFinset]
  exact (nearestGraph p).sum_degrees_eq_twice_card_edges

/-- The familiar `3n` bound, conditional on the geometric degree bound `6`. -/
theorem sMin_le_three_mul_of_degree_le_six {n : ℕ} (p : Fin n → Point)
    (hdeg : ∀ i : Fin n, (nearestGraph p).degree i ≤ 6) :
    sMin p ≤ 3 * n := by
  have hsum : (∑ i : Fin n, (nearestGraph p).degree i) ≤
      ∑ _i : Fin n, (6 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    exact hdeg i
  have hconst : (∑ _i : Fin n, (6 : ℕ)) = n * 6 := by simp
  rw [nearestGraph_handshake p, hconst] at hsum
  omega

end Erdos957
