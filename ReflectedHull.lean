import PlaneReflection
import TightFlatVertices

/-! Reflection of the plane together with reversal of a hull cycle preserves
its exterior angles, supporting orientation, and the seven-position flatness
certificate. No flatness or branch-cut premise is assumed in these identities. -/

namespace Erdos957

open scoped ComplexConjugate
open Fin.NatCast

/-- Reverse the cyclic indexing while fixing the origin of the cycle. -/
def reversedHullCycle {n h : ℕ} [NeZero h] (v : Fin h → Fin n) : Fin h → Fin n :=
  fun j => v (-j)

theorem reversedHullCycle_injective {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (hv : Function.Injective v) :
    Function.Injective (reversedHullCycle v) := by
  intro i j hij
  exact neg_injective (hv hij)

@[simp] theorem reversedHullCycle_neg {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (i : Fin h) : reversedHullCycle v (-i) = v i := by
  simp [reversedHullCycle]

theorem reversedHullCycle_neg_successor {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (i : Fin h) :
    reversedHullCycle v (-i + 1) = v (i - 1) := by
  simp [reversedHullCycle, sub_eq_add_neg, add_comm]

theorem reversedHullCycle_range {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) : Set.range (reversedHullCycle v) = Set.range v := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨-j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨-j, by simp⟩

theorem reflectedHull_range {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n))) :
    Set.range (reversedHullCycle v) =
      (hullVertexIndices (fun i => planeReflection (p i)) : Set (Fin n)) := by
  rw [reversedHullCycle_range, hullVertexIndices_planeReflection, hrange]

theorem hullEdgeDirection_planeReflection_reversed {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (j : Fin h) :
    hullEdgeDirection (fun i => planeReflection (p i)) (reversedHullCycle v) j =
      -conj (hullEdgeDirection p v (-j - 1)) := by
  have hi : -j - 1 + 1 = -j := by abel
  have hj : -(j + 1) = -j - 1 := by abel
  simp only [hullEdgeDirection, reversedHullCycle, hj, hi]
  rw [← map_sub, pointToComplex_planeReflection, ← map_neg, ← map_neg]
  congr 2
  abel

/-- Conjugation and inversion cancel on principal arguments, including the
negative real axis and zero. -/
theorem complex_arg_conj_inv (z : ℂ) : (conj (z⁻¹)).arg = z.arg := by
  rw [Complex.arg_conj, Complex.arg_inv]
  by_cases hpi : z.arg = Real.pi
  · simp [hpi]
  · have hneg : -z.arg ≠ Real.pi := by
      have := Complex.neg_pi_lt_arg z
      linarith
    simp [hpi, hneg]

theorem hullExteriorAngle_planeReflection_reversed {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (j : Fin h) :
    hullExteriorAngle (fun i => planeReflection (p i)) (reversedHullCycle v) j =
      hullExteriorAngle p v (-j) := by
  have hi : -(j - 1) - 1 = -j := by abel
  simp only [hullExteriorAngle, hullEdgeDirection_planeReflection_reversed, hi]
  rw [neg_div_neg_eq, ← map_div₀, ← inv_div]
  exact complex_arg_conj_inv _

theorem reflectedHull_support {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k)) :
    ∀ j k, 0 ≤ turn (planeReflection (p (reversedHullCycle v j)))
      (planeReflection (p (reversedHullCycle v (j + 1))))
      (planeReflection (p k)) := by
  intro j k
  have hi : -j - 1 + 1 = -j := by abel
  have hj : -(j + 1) = -j - 1 := by abel
  have hs := hsupport (-j - 1) k
  simp only [reversedHullCycle, turn_planeReflection, hj]
  rw [turn_reverse, neg_neg]
  simpa only [hi] using hs

private theorem reversed_seven_offset {h : ℕ} [NeZero h]
    (j : Fin h) (k : Fin 7) :
    -(j + (Fin.ofNat h k.val - 3)) =
      -j + (Fin.ofNat h (6 - k.val) - 3) := by
  have hsum : Fin.ofNat h k.val + Fin.ofNat h (6 - k.val) =
      (3 : Fin h) + 3 := by
    rw [Fin.ofNat_eq_cast, Fin.ofNat_eq_cast]
    have hc : k.val + (6 - k.val) = 3 + 3 := by omega
    exact_mod_cast congrArg (fun x : ℕ => (x : Fin h)) hc
  have heq : Fin.ofNat h (6 - k.val) = 3 + 3 - Fin.ofNat h k.val := by
    rw [← hsum]
    abel
  rw [heq]
  abel

/-- The genuine seven-position flatness certificate survives reflected
coordinates and reversed indexing. -/
theorem tightHull_not_bad_planeReflection_reversed {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (hv : Function.Injective v)
    (j : Fin h) (hgood : v (-j) ∉ tightHullBadVertices p v) :
    reversedHullCycle v j ∉
      tightHullBadVertices (fun i => planeReflection (p i)) (reversedHullCycle v) := by
  apply (tight_hull_vertex_not_bad_iff_all_seven_flat _ _
    (reversedHullCycle_injective v hv) j).mpr
  intro k
  rw [hullExteriorAngle_planeReflection_reversed, reversed_seven_offset]
  exact (tight_hull_vertex_not_bad_iff_all_seven_flat p v hv (-j)).mp hgood
    ⟨6 - k.val, by omega⟩

end Erdos957
