import HexagonCompletion
import NearestBound
import Mathlib.Tactic.Abel

/-! Two successive equilateral completions through six-neighbor vertices. -/

namespace Erdos957

/-- Completing the triangle `v,b,t` around the degree-six vertex `t` gives
`t₂`. If `t₂` also has degree six, completing the triangle `t,b,t₂` gives
`d` on the translated lattice line, with `p d = 2 • p b - p v`. -/
theorem degree_six_double_extension {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p)
    {v b t : Fin n}
    (htb : (nearestGraph p).Adj t b)
    (htv : (nearestGraph p).Adj t v)
    (hbv : (nearestGraph p).Adj b v)
    (htdeg : (nearestGraph p).degree t = 6) :
    ∃ t₂ : Fin n, t₂ ≠ v ∧
      (nearestGraph p).Adj t t₂ ∧
      (nearestGraph p).Adj b t₂ ∧
      p v + p t₂ = p t + p b ∧
      ((nearestGraph p).degree t₂ = 6 →
        ∃ d : Fin n, d ≠ t ∧
          (nearestGraph p).Adj t₂ d ∧
          (nearestGraph p).Adj b d ∧
          p d = 2 • p b - p v) := by
  obtain ⟨t₂, ht₂ne, htt₂, hbt₂, hsum₁⟩ :=
    degree_six_triangle_completion p hn hp htdeg htb htv hbv
  refine ⟨t₂, ht₂ne, htt₂, hbt₂, hsum₁, ?_⟩
  intro ht₂deg
  obtain ⟨d, hdne, ht₂d, hbd, hsum₂⟩ :=
    degree_six_triangle_completion p hn hp ht₂deg hbt₂.symm htt₂.symm htb.symm
  refine ⟨d, hdne, ht₂d, hbd, ?_⟩
  have ht₂eq : p t₂ = p t + p b - p v := by
    calc
      p t₂ = (p v + p t₂) - p v := by abel_nf
      _ = (p t + p b) - p v := by rw [hsum₁]
  have hdeq : p d = p t₂ + p b - p t := by
    calc
      p d = (p t + p d) - p t := by abel_nf
      _ = (p t₂ + p b) - p t := by rw [hsum₂]
  rw [hdeq, ht₂eq, two_smul]
  abel_nf

/-- Either the first extension vertex already has degree slack, or a second
extension produces the translated point `d`. -/
theorem degree_six_extension_slack_or_double {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p)
    {v b t : Fin n}
    (htb : (nearestGraph p).Adj t b)
    (htv : (nearestGraph p).Adj t v)
    (hbv : (nearestGraph p).Adj b v)
    (htdeg : (nearestGraph p).degree t = 6) :
    ∃ t₂ : Fin n, t₂ ≠ v ∧
      (nearestGraph p).Adj t t₂ ∧
      (nearestGraph p).Adj b t₂ ∧
      p v + p t₂ = p t + p b ∧
      ((nearestGraph p).degree t₂ ≤ 5 ∨
        ∃ d : Fin n, d ≠ t ∧
          (nearestGraph p).Adj t₂ d ∧
          (nearestGraph p).Adj b d ∧
          p d = 2 • p b - p v) := by
  obtain ⟨t₂, ht₂ne, htt₂, hbt₂, hsum, hext⟩ :=
    degree_six_double_extension p hn hp htb htv hbv htdeg
  refine ⟨t₂, ht₂ne, htt₂, hbt₂, hsum, ?_⟩
  have hle := nearestGraph_degree_le_six p hn hp t₂
  by_cases hsmall : (nearestGraph p).degree t₂ ≤ 5
  · exact Or.inl hsmall
  · right
    apply hext
    omega

/-- Starting from an equilateral triangle at a degree-six vertex `v`, two
triangle completions produce the next two lattice sites `b` and `t`.
If `t` and then its extension `t₂` both have degree six, further completions
produce `d` with the translated position used in the charging argument. -/
theorem degree_six_shared_edge_extension {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v : Fin n}
    (hvu : (nearestGraph p).Adj v u)
    (hvw : (nearestGraph p).Adj v w)
    (huw : (nearestGraph p).Adj u w)
    (hvdeg : (nearestGraph p).degree v = 6) :
    ∃ b t : Fin n, b ≠ u ∧ t ≠ w ∧
      (nearestGraph p).Adj v b ∧
      (nearestGraph p).Adj w b ∧
      (nearestGraph p).Adj v t ∧
      (nearestGraph p).Adj b t ∧
      p u + p b = p v + p w ∧
      p w + p t = p v + p b ∧
      p t = 2 • p v - p u ∧
      ((nearestGraph p).degree t = 6 →
        ∃ t₂ : Fin n, t₂ ≠ v ∧
          (nearestGraph p).Adj t t₂ ∧
          (nearestGraph p).Adj b t₂ ∧
          p v + p t₂ = p t + p b ∧
          ((nearestGraph p).degree t₂ = 6 →
            ∃ d : Fin n, d ≠ t ∧
              (nearestGraph p).Adj t₂ d ∧
              (nearestGraph p).Adj b d ∧
              p d = 2 • p b - p v)) := by
  obtain ⟨b, hbne, hvb, hwb, hsum₁⟩ :=
    degree_six_triangle_completion p hn hp hvdeg hvw hvu huw.symm
  obtain ⟨t, htne, hvt, hbt, hsum₂⟩ :=
    degree_six_triangle_completion p hn hp hvdeg hvb hvw hwb.symm
  have hbeq : p b = p v + p w - p u := by
    calc
      p b = (p u + p b) - p u := by abel_nf
      _ = (p v + p w) - p u := by rw [hsum₁]
  have hteq : p t = 2 • p v - p u := by
    have ht : p t = p v + p b - p w := by
      calc
        p t = (p w + p t) - p w := by abel_nf
        _ = (p v + p b) - p w := by rw [hsum₂]
    rw [ht, hbeq, two_smul]
    abel_nf
  refine ⟨b, t, hbne, htne, hvb, hwb, hvt, hbt, hsum₁, hsum₂, hteq, ?_⟩
  intro htdeg
  exact degree_six_double_extension p hn hp hbt.symm hvt.symm hvb.symm htdeg

end Erdos957
