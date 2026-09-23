import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Erdős problem 957: finite configurations and extremal distance counts

The point set is represented by an injective map from `Fin n` to the Euclidean
plane.  Pairs of indices are stored with the smaller index first, so each
unordered pair of distinct points is counted exactly once.
-/

namespace Erdos957

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The unordered pairs of distinct indices, in canonical order. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter (fun ij => ij.1 < ij.2)

/-- Membership in `pairs` is precisely the strict ordering of the indices. -/
theorem mem_pairs_iff {n : ℕ} {ij : Fin n × Fin n} :
    ij ∈ pairs n ↔ ij.1 < ij.2 := by
  simp [pairs]

/-- A configuration with at least two indices has at least one pair. -/
theorem pairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (pairs n).Nonempty := by
  have h0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have h1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  refine ⟨(⟨0, h0⟩, ⟨1, h1⟩), ?_⟩
  apply mem_pairs_iff.mpr
  change (0 : ℕ) < 1
  decide

/-- Distance between the two points indexed by a pair. -/
noncomputable def pairDist {n : ℕ} (p : Fin n → Point) (ij : Fin n × Fin n) : ℝ :=
  dist (p ij.1) (p ij.2)

/-- Distinct indices have positive distance when the configuration is injective. -/
theorem pairDist_pos {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {ij : Fin n × Fin n}
    (hij : ij ∈ pairs n) : 0 < pairDist p ij := by
  have hne : ij.1 ≠ ij.2 := ne_of_lt (mem_pairs_iff.mp hij)
  have hpeq : p ij.1 ≠ p ij.2 := fun heq => hne (hp heq)
  exact (dist_pos.mpr hpeq)

/-- A pair realizes the minimum pairwise distance of the configuration. -/
def isMinPair {n : ℕ} (p : Fin n → Point) (ij : Fin n × Fin n) : Prop :=
  ij ∈ pairs n ∧ ∀ kl ∈ pairs n, pairDist p ij ≤ pairDist p kl

/-- A pair realizes the maximum pairwise distance of the configuration. -/
def isMaxPair {n : ℕ} (p : Fin n → Point) (ij : Fin n × Fin n) : Prop :=
  ij ∈ pairs n ∧ ∀ kl ∈ pairs n, pairDist p kl ≤ pairDist p ij

/-- Every configuration with at least two indices has a shortest pair. -/
theorem exists_min_pair {n : ℕ} (p : Fin n → Point) (hn : 2 ≤ n) :
    ∃ ij, isMinPair p ij := by
  obtain ⟨ij, hij, hmin⟩ := (pairs n).exists_min_image (pairDist p) (pairs_nonempty hn)
  exact ⟨ij, hij, hmin⟩

/-- Every configuration with at least two indices has a longest pair. -/
theorem exists_max_pair {n : ℕ} (p : Fin n → Point) (hn : 2 ≤ n) :
    ∃ ij, isMaxPair p ij := by
  obtain ⟨ij, hij, hmax⟩ := (pairs n).exists_max_image (pairDist p) (pairs_nonempty hn)
  exact ⟨ij, hij, hmax⟩

/-- Number of unordered pairs at the minimum pairwise distance. -/
noncomputable def sMin {n : ℕ} (p : Fin n → Point) : ℕ := by
  classical
  exact ((pairs n).filter (isMinPair p)).card

/-- Number of unordered pairs at the maximum pairwise distance. -/
noncomputable def sMax {n : ℕ} (p : Fin n → Point) : ℕ := by
  classical
  exact ((pairs n).filter (isMaxPair p)).card

/-- The paper's quantitative strengthening, stated without a proof. -/
def QuantitativeBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) (p : Fin n → Point),
      2 ≤ n → Function.Injective p →
        (sMin p : ℝ) * (sMax p : ℝ) ≤
          (9 / 8 : ℝ) * (n : ℝ) ^ 2 + C * (n : ℝ)

end Erdos957
