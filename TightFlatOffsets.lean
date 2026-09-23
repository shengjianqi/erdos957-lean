import TightFlatVertices
import Mathlib.Tactic.Abel

/-! Extract the five immediately useful small exterior angles from the
seven-position exceptional-neighborhood certificate. -/

namespace Erdos957

open Fin.NatCast


theorem tight_hull_five_turns_of_not_bad {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n)
    (hv : Function.Injective v) (i : Fin h)
    (hgood : v i ∉ tightHullBadVertices p v) :
    hullExteriorAngle p v i < Real.pi / 1800 ∧
      hullExteriorAngle p v (i - 1) < Real.pi / 1800 ∧
      hullExteriorAngle p v ((i - 1) - 1) < Real.pi / 1800 ∧
      hullExteriorAngle p v (i + 1) < Real.pi / 1800 ∧
      hullExteriorAngle p v ((i + 1) + 1) < Real.pi / 1800 := by
  have hall := (tight_hull_vertex_not_bad_iff_all_seven_flat p v hv i).mp hgood
  have hofs (m : ℕ) : Fin.ofNat h m = (m : Fin h) :=
    Fin.ofNat_eq_cast h m
  have hc2 : (2 : Fin h) = 1 + 1 := by
    calc
      (2 : Fin h) = ((1 + 1 : ℕ) : Fin h) := by norm_num
      _ = (1 : Fin h) + 1 := by rw [Nat.cast_add]; norm_num
  have hc3 : (3 : Fin h) = 2 + 1 := by
    calc
      (3 : Fin h) = ((2 + 1 : ℕ) : Fin h) := by norm_num
      _ = (2 : Fin h) + 1 := by rw [Nat.cast_add]; norm_num
  have hc4 : (4 : Fin h) = 3 + 1 := by
    calc
      (4 : Fin h) = ((3 + 1 : ℕ) : Fin h) := by norm_num
      _ = (3 : Fin h) + 1 := by rw [Nat.cast_add]; norm_num
  have hc5 : (5 : Fin h) = 4 + 1 := by
    calc
      (5 : Fin h) = ((4 + 1 : ℕ) : Fin h) := by norm_num
      _ = (4 : Fin h) + 1 := by rw [Nat.cast_add]; norm_num
  have h3 : i + (Fin.ofNat h 3 - 3) = i := by
    rw [hofs]
    simp only [Nat.cast_ofNat]
    abel
  have h2 : i + (Fin.ofNat h 2 - 3) = i - 1 := by
    rw [hofs]
    simp only [Nat.cast_ofNat]
    rw [hc3]
    abel
  have h1 : i + (Fin.ofNat h 1 - 3) = (i - 1) - 1 := by
    rw [hofs]
    simp only [Nat.cast_one]
    rw [hc3, hc2]
    abel
  have h4 : i + (Fin.ofNat h 4 - 3) = i + 1 := by
    rw [hofs]
    simp only [Nat.cast_ofNat]
    rw [hc4]
    abel
  have h5 : i + (Fin.ofNat h 5 - 3) = (i + 1) + 1 := by
    rw [hofs]
    simp only [Nat.cast_ofNat]
    rw [hc5, hc4]
    abel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h3] using hall (⟨3, by decide⟩ : Fin 7)
  · simpa only [h2] using hall (⟨2, by decide⟩ : Fin 7)
  · simpa only [h1] using hall (⟨1, by decide⟩ : Fin 7)
  · simpa only [h4] using hall (⟨4, by decide⟩ : Fin 7)
  · simpa only [h5] using hall (⟨5, by decide⟩ : Fin 7)

end Erdos957
