import BoundaryDegree
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-! Angular order of the three closest neighbors of a diameter endpoint. -/

namespace Erdos957

/-- Three same-radius separated points in a strict half-plane can be indexed
by strictly increasing rotated arguments. Both adjacent gaps are at least
sixty degrees, while the total span is strictly less than a half-turn. -/
theorem circle_three_order_in_halfplane
    (N : Finset Point) (x axis : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hhalf : ∀ y ∈ N, 0 < inner ℝ axis (y - x))
    (hcard : N.card = 3) :
    ∃ v : Fin 3 → Point, Function.Injective v ∧
      Set.range v = (N : Set Point) ∧
      (∀ i j : Fin 3, i < j →
        halfplaneArg x axis (v i) < halfplaneArg x axis (v j)) ∧
      Real.pi / 3 ≤ halfplaneArg x axis (v 1) - halfplaneArg x axis (v 0) ∧
      Real.pi / 3 ≤ halfplaneArg x axis (v 2) - halfplaneArg x axis (v 1) ∧
      halfplaneArg x axis (v 2) - halfplaneArg x axis (v 0) < Real.pi := by
  classical
  let angles : Finset ℝ := N.image (halfplaneArg x axis)
  have hanginj : Set.InjOn (halfplaneArg x axis) (N : Set Point) := by
    intro y hy z hz heq
    by_contra hne
    have hgap := halfplaneArg_gap x axis y z r hr (hradius y hy)
      (hradius z hz) (hsep y hy z hz hne) (hhalf y hy)
    rw [heq, sub_self, abs_zero] at hgap
    linarith [Real.pi_pos]
  have hanglecard : angles.card = 3 := by
    calc
      angles.card = N.card := Finset.card_image_of_injOn hanginj
      _ = 3 := hcard
  let a := angles.orderEmbOfFin hanglecard
  have hpre (i : Fin 3) : ∃ y ∈ N, halfplaneArg x axis y = a i := by
    have hai : a i ∈ angles := angles.orderEmbOfFin_mem hanglecard i
    exact Finset.mem_image.mp hai
  choose v hvN hvArg using hpre
  have hvinj : Function.Injective v := by
    intro i j hij
    apply a.injective
    calc
      a i = halfplaneArg x axis (v i) := (hvArg i).symm
      _ = halfplaneArg x axis (v j) := congrArg (halfplaneArg x axis) hij
      _ = a j := hvArg j
  have hrange : Set.range v = (N : Set Point) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact hvN i
    · intro hy
      have hyangle : halfplaneArg x axis y ∈ angles :=
        Finset.mem_image.mpr ⟨y, hy, rfl⟩
      have hyarange : halfplaneArg x axis y ∈ Set.range a := by
        rw [Finset.range_orderEmbOfFin]
        exact hyangle
      obtain ⟨i, hi⟩ := hyarange
      refine ⟨i, ?_⟩
      apply hanginj (hvN i) hy
      rw [hvArg i, hi]
  have hmono : ∀ i j : Fin 3, i < j →
      halfplaneArg x axis (v i) < halfplaneArg x axis (v j) := by
    intro i j hij
    rw [hvArg i, hvArg j]
    exact a.strictMono hij
  have hgap01 : Real.pi / 3 ≤
      halfplaneArg x axis (v 1) - halfplaneArg x axis (v 0) := by
    have hgap := halfplaneArg_gap x axis (v 0) (v 1) r hr
      (hradius (v 0) (hvN 0)) (hradius (v 1) (hvN 1))
      (hsep (v 0) (hvN 0) (v 1) (hvN 1)
        (fun h => (by decide : (0 : Fin 3) ≠ 1) (hvinj h)))
      (hhalf (v 0) (hvN 0))
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hmono 0 1 (by decide)).le)] at hgap
    exact hgap
  have hgap12 : Real.pi / 3 ≤
      halfplaneArg x axis (v 2) - halfplaneArg x axis (v 1) := by
    have hgap := halfplaneArg_gap x axis (v 1) (v 2) r hr
      (hradius (v 1) (hvN 1)) (hradius (v 2) (hvN 2))
      (hsep (v 1) (hvN 1) (v 2) (hvN 2)
        (fun h => (by decide : (1 : Fin 3) ≠ 2) (hvinj h)))
      (hhalf (v 1) (hvN 1))
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hmono 1 2 (by decide)).le)] at hgap
    exact hgap
  have hspan : halfplaneArg x axis (v 2) - halfplaneArg x axis (v 0) < Real.pi := by
    have hlo := (halfplaneArg_mem_Ioo (hhalf (v 0) (hvN 0))).1
    have hhi := (halfplaneArg_mem_Ioo (hhalf (v 2) (hvN 2))).2
    linarith
  exact ⟨v, hvinj, hrange, hmono, hgap01, hgap12, hspan⟩

/-- The three nearest neighbors of a diameter endpoint, when there are
exactly three, have a canonical strict angular order in the supporting
half-plane given by a diameter partner. -/
theorem diameter_degree_three_neighbor_order {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3) :
    ∃ v : Fin 3 → Fin n, Function.Injective v ∧
      Set.range v = ((nearestGraph p).neighborFinset u : Set (Fin n)) ∧
      (∀ i k : Fin 3, i < k →
        halfplaneArg (p u) (p j - p u) (p (v i)) <
          halfplaneArg (p u) (p j - p u) (p (v k))) ∧
      Real.pi / 3 ≤
        halfplaneArg (p u) (p j - p u) (p (v 1)) -
          halfplaneArg (p u) (p j - p u) (p (v 0)) ∧
      Real.pi / 3 ≤
        halfplaneArg (p u) (p j - p u) (p (v 2)) -
          halfplaneArg (p u) (p j - p u) (p (v 1)) ∧
      halfplaneArg (p u) (p j - p u) (p (v 2)) -
        halfplaneArg (p u) (p j - p u) (p (v 0)) < Real.pi := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  let N := ((nearestGraph p).neighborFinset u).image p
  have hcard : N.card = 3 := by
    dsimp [N]
    rw [Finset.card_image_of_injective _ hp]
    exact ((nearestGraph p).card_neighborFinset_eq_degree u).trans hdeg
  have hradius : ∀ y ∈ N, dist (p u) y = r := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    exact nearestGraph_adj_dist_eq p hmin
      (((nearestGraph p).mem_neighborFinset u k).mp hk)
  have hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    exact isMinPair_le_dist p hmin (fun heq => hyz (congrArg p heq))
  have hhalf : ∀ y ∈ N, 0 < inner ℝ (p j - p u) (y - p u) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hadj : (nearestGraph p).Adj u k :=
      ((nearestGraph p).mem_neighborFinset u k).mp hk
    exact diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj hadj)
  obtain ⟨q, hqinj, hqrange, hqmono, hq01, hq12, hqspan⟩ :=
    circle_three_order_in_halfplane N (p u) (p j - p u) r hr
      hradius hsep hhalf hcard
  have hindices : ∀ i : Fin 3, ∃ k : Fin n,
      k ∈ (nearestGraph p).neighborFinset u ∧ p k = q i := by
    intro i
    have hqmem : q i ∈ N := by
      change q i ∈ (N : Set Point)
      rw [← hqrange]
      exact ⟨i, rfl⟩
    exact Finset.mem_image.mp hqmem
  choose v hv hvq using hindices
  have hvinj : Function.Injective v := by
    intro i k hik
    apply hqinj
    rw [← hvq i, ← hvq k, hik]
  have hrange : Set.range v =
      ((nearestGraph p).neighborFinset u : Set (Fin n)) := by
    ext k
    constructor
    · rintro ⟨i, rfl⟩
      exact hv i
    · intro hk
      have hpk : p k ∈ (N : Set Point) :=
        Finset.mem_image.mpr ⟨k, hk, rfl⟩
      rw [← hqrange] at hpk
      obtain ⟨i, hi⟩ := hpk
      exact ⟨i, hp ((hvq i).trans hi)⟩
  refine ⟨v, hvinj, hrange, ?_, ?_, ?_, ?_⟩
  · intro i k hik
    simpa only [hvq] using hqmono i k hik
  · simpa only [hvq] using hq01
  · simpa only [hvq] using hq12
  · simpa only [hvq] using hqspan

/-- Among the three nearest neighbors of a diameter endpoint, the middle
neighbor lies within thirty degrees of the diameter axis. The enumeration
also identifies its two distinct nearest neighbors on either side. -/
theorem degree_three_middle_neighbor_exists {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3) :
    ∃ v : Fin 3 → Fin n, Function.Injective v ∧
      Set.range v = ((nearestGraph p).neighborFinset u : Set (Fin n)) ∧
      (∀ i, (nearestGraph p).Adj u (v i)) ∧
      (∀ i k : Fin 3, i < k →
        halfplaneArg (p u) (p j - p u) (p (v i)) <
          halfplaneArg (p u) (p j - p u) (p (v k))) ∧
      Real.pi / 3 ≤
        halfplaneArg (p u) (p j - p u) (p (v 1)) -
          halfplaneArg (p u) (p j - p u) (p (v 0)) ∧
      Real.pi / 3 ≤
        halfplaneArg (p u) (p j - p u) (p (v 2)) -
          halfplaneArg (p u) (p j - p u) (p (v 1)) ∧
      -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p (v 1)) ∧
      halfplaneArg (p u) (p j - p u) (p (v 1)) < Real.pi / 6 := by
  obtain ⟨v, hvinj, hrange, hmono, hgap01, hgap12, _hspan⟩ :=
    diameter_degree_three_neighbor_order p hn hp hdiam hdeg
  have hadj (i : Fin 3) : (nearestGraph p).Adj u (v i) := by
    have hmem : v i ∈ (nearestGraph p).neighborFinset u := by
      change v i ∈ ((nearestGraph p).neighborFinset u : Set (Fin n))
      rw [← hrange]
      exact ⟨i, rfl⟩
    exact ((nearestGraph p).mem_neighborFinset u (v i)).mp hmem
  have hhalf (i : Fin 3) :
      0 < inner ℝ (p j - p u) (p (v i) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj (hadj i))
  have hlo := (halfplaneArg_mem_Ioo (hhalf 0)).1
  have hhi := (halfplaneArg_mem_Ioo (hhalf 2)).2
  refine ⟨v, hvinj, hrange, hadj, hmono, hgap01, hgap12, ?_, ?_⟩
  · linarith
  · linarith

/-- The narrow central cone contains exactly one nearest neighbor when the
diameter endpoint has degree three. -/
theorem degree_three_middle_neighbor_unique {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j : Fin n} (hdiam : (diameterGraph p).Adj u j)
    (hdeg : (nearestGraph p).degree u = 3) :
    ∃! k : Fin n, (nearestGraph p).Adj u k ∧
      -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p k) ∧
      halfplaneArg (p u) (p j - p u) (p k) < Real.pi / 6 := by
  obtain ⟨v, _hvinj, _hrange, hadj, _hmono, _hgap01, _hgap12, hlo, hhi⟩ :=
    degree_three_middle_neighbor_exists p hn hp hdiam hdeg
  refine ⟨v 1, ⟨hadj 1, hlo, hhi⟩, ?_⟩
  intro k ⟨hkadj, hklo, hkhi⟩
  by_contra hne
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hdist1 : dist (p u) (p (v 1)) = r :=
    nearestGraph_adj_dist_eq p hmin (hadj 1)
  have hdistk : dist (p u) (p k) = r :=
    nearestGraph_adj_dist_eq p hmin hkadj
  have hsep : r ≤ dist (p (v 1)) (p k) :=
    isMinPair_le_dist p hmin (fun h => hne h.symm)
  have hhalf : 0 < inner ℝ (p j - p u) (p (v 1) - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj (hadj 1))
  have hgap := halfplaneArg_gap (p u) (p j - p u) (p (v 1)) (p k)
    r hr hdist1 hdistk hsep hhalf
  have hsmall :
      |halfplaneArg (p u) (p j - p u) (p (v 1)) -
        halfplaneArg (p u) (p j - p u) (p k)| < Real.pi / 3 := by
    apply abs_lt.mpr
    constructor <;> linarith
  linarith

end Erdos957
