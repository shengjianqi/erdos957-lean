import Reduction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The diameter graph for Erdős problem 957

Its vertices are the indices of the point configuration. Two vertices are
adjacent exactly when their points form a maximum-distance pair.
-/

namespace Erdos957

/-- The simple graph of maximum-distance pairs. -/
def diameterGraph {n : ℕ} (p : Fin n → Point) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => isMaxPair p (i, j))

noncomputable instance diameterGraphAdjDecidable {n : ℕ} (p : Fin n → Point) :
    DecidableRel (diameterGraph p).Adj := Classical.decRel _

theorem diameterGraph_adj_iff {n : ℕ} (p : Fin n → Point) (i j : Fin n) :
    (diameterGraph p).Adj i j ↔
      isMaxPair p (i, j) ∨ isMaxPair p (j, i) := by
  simp only [diameterGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    constructor
    · rcases h with h | h
      · exact ne_of_lt (mem_pairs_iff.mp h.1)
      · exact (ne_of_lt (mem_pairs_iff.mp h.1)).symm
    · exact h

/-- A maximum-distance pair is no shorter than any ordered pair, including a
diagonal pair. -/
theorem isMaxPair_dist_le {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hij : isMaxPair p ij) (k l : Fin n) :
    dist (p k) (p l) ≤ pairDist p ij := by
  by_cases hkl : k = l
  · subst l
    simpa only [dist_self, pairDist] using
      (dist_nonneg : 0 ≤ dist (p ij.1) (p ij.2))
  · rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact hij.2 (k, l) (mem_pairs_iff.mpr hlt)
    · have h := hij.2 (l, k) (mem_pairs_iff.mpr hgt)
      simpa [pairDist, dist_comm] using h

/-- All maximum-distance pairs have the same distance. -/
theorem isMaxPair_pairDist_eq {n : ℕ} (p : Fin n → Point)
    {ij kl : Fin n × Fin n} (hij : isMaxPair p ij) (hkl : isMaxPair p kl) :
    pairDist p ij = pairDist p kl := by
  exact le_antisymm (hkl.2 ij hij.1) (hij.2 kl hkl.1)

/-- A pair with the maximum distance, oriented by increasing index, satisfies
`isMaxPair`. -/
theorem isMaxPair_of_dist_eq {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hij : isMaxPair p ij)
    {k l : Fin n} (hkl : k < l)
    (heq : dist (p k) (p l) = pairDist p ij) :
    isMaxPair p (k, l) := by
  constructor
  · exact mem_pairs_iff.mpr hkl
  · intro ab hab
    have hle := hij.2 ab hab
    change pairDist p ab ≤ dist (p k) (p l)
    exact hle.trans_eq heq.symm

/-- With distinct points, adjacency is equivalent to attaining the distance
of any fixed maximum-distance pair. -/
theorem diameterGraph_adj_iff_dist_eq {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p)
    {ij : Fin n × Fin n} (hij : isMaxPair p ij) (i j : Fin n) :
    (diameterGraph p).Adj i j ↔
      dist (p i) (p j) = pairDist p ij := by
  constructor
  · intro h
    rcases (diameterGraph_adj_iff p i j).mp h with hmax | hmax
    · change pairDist p (i, j) = pairDist p ij
      exact isMaxPair_pairDist_eq p hmax hij
    · calc
        dist (p i) (p j) = pairDist p (j, i) := by simp [pairDist, dist_comm]
        _ = pairDist p ij := isMaxPair_pairDist_eq p hmax hij
  · intro heq
    have hne : i ≠ j := by
      intro h
      subst j
      have hpos := pairDist_pos p hp hij.1
      simp only [dist_self] at heq
      exact (ne_of_gt hpos) heq.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (diameterGraph_adj_iff p i j).mpr
        (Or.inl (isMaxPair_of_dist_eq p hij hlt heq))
    · have heq' : dist (p j) (p i) = pairDist p ij := by
        simpa only [dist_comm] using heq
      exact (diameterGraph_adj_iff p i j).mpr
        (Or.inr (isMaxPair_of_dist_eq p hij hgt heq'))

/-- The graph edges are exactly the pairs counted by `sMax`. -/
theorem sMax_eq_card_edgeFinset {n : ℕ} (p : Fin n → Point) :
    sMax p = (diameterGraph p).edgeFinset.card := by
  classical
  unfold sMax
  refine Finset.card_bij
    (s := (pairs n).filter (isMaxPair p))
    (t := (diameterGraph p).edgeFinset)
    (fun (ij : Fin n × Fin n) _ => Sym2.mk ij.1 ij.2) ?_ ?_ ?_
  · intro ij hij
    have hmax : isMaxPair p ij := (Finset.mem_filter.mp hij).2
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
      (diameterGraph_adj_iff p ij.1 ij.2).mpr (Or.inl hmax)
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
      have hadj : (diameterGraph p).Adj i j := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rcases (diameterGraph_adj_iff p i j).mp hadj with hij | hji
      · exact ⟨(i, j), Finset.mem_filter.mpr ⟨hij.1, hij⟩, rfl⟩
      · exact ⟨(j, i), Finset.mem_filter.mpr ⟨hji.1, hji⟩, Sym2.eq_swap⟩

/-- A diameter endpoint is exactly a vertex incident to a diameter edge. -/
theorem mem_diameterEndpoints_iff_exists_adj {n : ℕ} (p : Fin n → Point)
    (i : Fin n) :
    i ∈ diameterEndpoints p ↔ ∃ j, (diameterGraph p).Adj i j := by
  simp only [diameterEndpoints, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ij, hmax, hi⟩
    rcases hi with hi | hi
    · subst i
      exact ⟨ij.2, (diameterGraph_adj_iff p ij.1 ij.2).mpr (Or.inl hmax)⟩
    · subst i
      exact ⟨ij.1, (diameterGraph_adj_iff p ij.2 ij.1).mpr (Or.inr hmax)⟩
  · rintro ⟨j, hadj⟩
    rcases (diameterGraph_adj_iff p i j).mp hadj with hij | hji
    · exact ⟨(i, j), hij, Or.inl rfl⟩
    · exact ⟨(j, i), hji, Or.inr rfl⟩

theorem mem_diameterEndpoints_iff_not_isIsolated {n : ℕ} (p : Fin n → Point)
    (i : Fin n) :
    i ∈ diameterEndpoints p ↔ ¬(diameterGraph p).IsIsolated i := by
  rw [mem_diameterEndpoints_iff_exists_adj]
  exact (diameterGraph p).exists_adj_iff_not_isIsolated

theorem mem_diameterEndpoints_iff_degree_pos {n : ℕ} (p : Fin n → Point)
    (i : Fin n) :
    i ∈ diameterEndpoints p ↔ 0 < (diameterGraph p).degree i := by
  rw [mem_diameterEndpoints_iff_not_isIsolated]
  exact ((diameterGraph p).degree_pos i).symm

end Erdos957
