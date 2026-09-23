import BoundaryNeighborOrder
import NormalizedEdge
import TwoCircleSeparation
import Mathlib.Tactic.Linarith

/-! A degree-five neighbor in the middle direction of a diameter endpoint
shares another nearest-distance neighbor with that endpoint. -/

namespace Erdos957

open scoped ComplexConjugate

theorem degree_five_central_neighbor_has_common_neighbor {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v : Fin n}
    (hdiam : (diameterGraph p).Adj u j)
    (hdegreeu : (nearestGraph p).degree u = 3)
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hvdegree : (nearestGraph p).degree v = 5) :
    ∃ a : Fin n, (nearestGraph p).Adj u a ∧ (nearestGraph p).Adj v a := by
  classical
  by_contra hnone
  obtain ⟨q, hqinj, _hqrange, hqadj, hqmono, _hqgap01, _hqgap12,
    hqlo, hqhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp hdiam hdegreeu
  obtain ⟨m, _hm, hmuniq⟩ :=
    degree_three_middle_neighbor_unique p hn hp hdiam hdegreeu
  have hqmiddle : q 1 = v := by
    have hqm : q 1 = m := hmuniq (q 1) ⟨hqadj 1, hqlo, hqhi⟩
    have hvm : v = m := hmuniq v ⟨huv, hvlo, hvhi⟩
    exact hqm.trans hvm.symm
  let a := q 0
  let c := q 2
  have haadj : (nearestGraph p).Adj u a := hqadj 0
  have hcadj : (nearestGraph p).Adj u c := hqadj 2
  have hane : ¬ (nearestGraph p).Adj v a := by
    intro hva
    exact hnone ⟨a, haadj, hva⟩
  have hcne : ¬ (nearestGraph p).Adj v c := by
    intro hvc
    exact hnone ⟨c, hcadj, hvc⟩
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hrv : dist (p u) (p v) = r := nearestGraph_adj_dist_eq p hmin huv
  have hrua : dist (p u) (p a) = r := nearestGraph_adj_dist_eq p hmin haadj
  have hruc : dist (p u) (p c) = r := nearestGraph_adj_dist_eq p hmin hcadj
  have huvne : p u ≠ p v := hp.ne ((nearestGraph p).ne_of_adj huv)
  have haxis (i : Fin 3) :
      0 < inner ℝ (p j - p u) (p (q i) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj (hqadj i))
  have hmono01 := hqmono 0 1 (by decide)
  have hmono12 := hqmono 1 2 (by decide)
  have hspan : halfplaneArg (p u) (p j - p u) (p c) -
      halfplaneArg (p u) (p j - p u) (p a) < Real.pi := by
    have hlo := (halfplaneArg_mem_Ioo (haxis 0)).1
    have hhi := (halfplaneArg_mem_Ioo (haxis 2)).2
    dsimp [a, c]
    linarith
  let A := edgeCoordinate (p u) (p v) (p a)
  let C := edgeCoordinate (p u) (p v) (p c)
  have hAarg : A.arg = halfplaneArg (p u) (p j - p u) (p a) -
      halfplaneArg (p u) (p j - p u) (p v) :=
    edgeCoordinate_arg (p u) (p v) (p a) (p j - p u)
      (by simpa only [← hqmiddle] using haxis 1) (haxis 0)
  have hCarg : C.arg = halfplaneArg (p u) (p j - p u) (p c) -
      halfplaneArg (p u) (p j - p u) (p v) :=
    edgeCoordinate_arg (p u) (p v) (p c) (p j - p u)
      (by simpa only [← hqmiddle] using haxis 1) (haxis 2)
  have hAunit : ‖A‖ = 1 := by
    rw [show A = edgeCoordinate (p u) (p v) (p a) by rfl,
      edgeCoordinate_norm (p u) (p v) (p a) huvne, hrua, hrv]
    exact div_self (ne_of_gt hr)
  have hCunit : ‖C‖ = 1 := by
    rw [show C = edgeCoordinate (p u) (p v) (p c) by rfl,
      edgeCoordinate_norm (p u) (p v) (p c) huvne, hruc, hrv]
    exact div_self (ne_of_gt hr)
  have hAinterval : -Real.pi < A.arg ∧ A.arg < 0 := by
    rw [hAarg]
    dsimp [a, c] at hspan
    rw [← hqmiddle] at *
    constructor <;> linarith
  have hCinterval : 0 < C.arg ∧ C.arg < Real.pi := by
    rw [hCarg]
    dsimp [a, c] at hspan
    rw [← hqmiddle] at *
    constructor <;> linarith
  have hACspan : C.arg - A.arg < Real.pi := by
    rw [hAarg, hCarg]
    linarith
  let N := ((nearestGraph p).neighborFinset v).erase u
  let f : Fin n → ℂ := fun k => edgeCoordinate (p u) (p v) (p k) - 1
  let S : Finset ℂ := N.image f
  have hfadd (k : Fin n) : 1 + f k = edgeCoordinate (p u) (p v) (p k) := by
    dsimp [f]
    ring
  have hmemu : u ∈ (nearestGraph p).neighborFinset v :=
    ((nearestGraph p).mem_neighborFinset v u).mpr huv.symm
  have hNcard : N.card = 4 := by
    dsimp [N]
    rw [Finset.card_erase_of_mem hmemu,
      (nearestGraph p).card_neighborFinset_eq_degree v, hvdegree]
  have hf_inj : Function.Injective f := by
    intro k l hkl
    have hcoord : edgeCoordinate (p u) (p v) (p k) =
        edgeCoordinate (p u) (p v) (p l) := by
      calc
        edgeCoordinate (p u) (p v) (p k) = 1 + f k := (hfadd k).symm
        _ = 1 + f l := by rw [hkl]
        _ = edgeCoordinate (p u) (p v) (p l) := hfadd l
    have hzero : dist (p k) (p l) / dist (p u) (p v) = 0 := by
      rw [← edgeCoordinate_dist (p u) (p v) (p k) (p l) huvne,
        hcoord, dist_self]
    have hdistzero : dist (p k) (p l) = 0 := by
      by_contra hnzero
      exact (div_ne_zero hnzero (ne_of_gt (by rw [hrv]; exact hr))) hzero
    exact hp (dist_eq_zero.mp hdistzero)
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_image_of_injective N hf_inj, hNcard]
  have hNadj {k : Fin n} (hk : k ∈ N) : (nearestGraph p).Adj v k :=
    ((nearestGraph p).mem_neighborFinset v k).mp (Finset.mem_erase.mp hk).2
  have hNne {k : Fin n} (hk : k ∈ N) : k ≠ u := (Finset.mem_erase.mp hk).1
  have hminle {k l : Fin n} (hkl : k ≠ l) : r ≤ dist (p k) (p l) :=
    isMinPair_le_dist p hmin hkl
  have hSunit : ∀ z ∈ S, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hrvk : dist (p v) (p k) = r :=
      nearestGraph_adj_dist_eq p hmin (hNadj hk)
    change ‖edgeCoordinate (p u) (p v) (p k) - 1‖ = 1
    rw [edgeCoordinate_sub_one_norm (p u) (p v) (p k) huvne,
      hrvk, hrv]
    exact div_self (ne_of_gt hr)
  have hSorigin : ∀ z ∈ S, 1 ≤ ‖1 + z‖ := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have huk : u ≠ k := (hNne hk).symm
    have hle : r ≤ dist (p u) (p k) := hminle huk
    rw [hfadd]
    rw [edgeCoordinate_norm (p u) (p v) (p k) huvne, hrv]
    exact (le_div_iff₀ hr).2 (by simpa using hle)
  have hSa : ∀ z ∈ S, 1 ≤ dist A (1 + z) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hka : k ≠ a := by
      intro hka
      subst k
      exact hane (hNadj hk)
    have hle : r ≤ dist (p a) (p k) := hminle hka.symm
    rw [hfadd]
    change 1 ≤ dist (edgeCoordinate (p u) (p v) (p a))
      (edgeCoordinate (p u) (p v) (p k))
    rw [edgeCoordinate_dist (p u) (p v) (p a) (p k) huvne, hrv]
    exact (le_div_iff₀ hr).2 (by simpa using hle)
  have hSc : ∀ z ∈ S, 1 ≤ dist C (1 + z) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hkc : k ≠ c := by
      intro hkc
      subst k
      exact hcne (hNadj hk)
    have hle : r ≤ dist (p c) (p k) := hminle hkc.symm
    rw [hfadd]
    change 1 ≤ dist (edgeCoordinate (p u) (p v) (p c))
      (edgeCoordinate (p u) (p v) (p k))
    rw [edgeCoordinate_dist (p u) (p v) (p c) (p k) huvne, hrv]
    exact (le_div_iff₀ hr).2 (by simpa using hle)
  have hSsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → 1 ≤ dist z w := by
    intro z hz w hw hzw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hzw rfl
    have hle : r ≤ dist (p k) (p l) := hminle hkl
    change 1 ≤ dist (edgeCoordinate (p u) (p v) (p k) - 1)
      (edgeCoordinate (p u) (p v) (p l) - 1)
    rw [dist_sub_right, edgeCoordinate_dist (p u) (p v) (p k) (p l) huvne, hrv]
    exact (le_div_iff₀ hr).2 (by simpa using hle)
  have hcardle : S.card ≤ 3 :=
    unit_two_circle_neighbors_card_le_three S A C hAunit hCunit
      hAinterval hCinterval hACspan hSunit hSorigin hSa hSc hSsep
  omega

end Erdos957
