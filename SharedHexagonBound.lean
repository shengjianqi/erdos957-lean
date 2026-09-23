import HexagonExtension
import SharedReceiverDegree

/-! Low-degree alternatives along a hexagonal extension below an actual supporting edge. -/

namespace Erdos957

theorem degree_six_shared_edge_low_degree_extension {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v : Fin n}
    (hvu : (nearestGraph p).Adj v u)
    (hvw : (nearestGraph p).Adj v w)
    (huw : (nearestGraph p).Adj u w)
    (hvdeg : (nearestGraph p).degree v = 6)
    (hw : w ∈ hullVertexIndices p)
    (hsupport : ∀ k, 0 ≤ turn (p w) (p u) (p k)) :
    ∃ b t : Fin n,
      (nearestGraph p).Adj v b ∧ (nearestGraph p).Adj w b ∧
      (nearestGraph p).Adj v t ∧ (nearestGraph p).Adj b t ∧ t ≠ w ∧
      p u + p b = p v + p w ∧ p w + p t = p v + p b ∧
      ((nearestGraph p).degree t ≤ 5 ∨
        ∃ t₂ : Fin n, (nearestGraph p).Adj t t₂ ∧
          (nearestGraph p).Adj b t₂ ∧ p v + p t₂ = p t + p b ∧
          ((nearestGraph p).degree t₂ ≤ 5 ∨
            ∃ d : Fin n, (nearestGraph p).Adj t₂ d ∧
              (nearestGraph p).Adj b d ∧ p d = 2 • p b - p v ∧
              (nearestGraph p).degree d ≤ 4)) := by
  obtain ⟨b, t, _hbne, htne, hvb, hwb, hvt, hbt, hbsum, htsum, _hteq, hext⟩ :=
    degree_six_shared_edge_extension p hn hp hvu hvw huw hvdeg
  refine ⟨b, t, hvb, hwb, hvt, hbt, htne, hbsum, htsum, ?_⟩
  by_cases htlow : (nearestGraph p).degree t ≤ 5
  · exact Or.inl htlow
  have htdeg : (nearestGraph p).degree t = 6 := by
    have hle := nearestGraph_degree_le_six p hn hp t
    omega
  obtain ⟨t₂, _ht₂ne, htt₂, hbt₂, ht₂sum, hext₂⟩ := hext htdeg
  refine Or.inr ⟨t₂, htt₂, hbt₂, ht₂sum, ?_⟩
  by_cases ht₂low : (nearestGraph p).degree t₂ ≤ 5
  · exact Or.inl ht₂low
  have ht₂deg : (nearestGraph p).degree t₂ = 6 := by
    have hle := nearestGraph_degree_le_six p hn hp t₂
    omega
  obtain ⟨d, _hdne, ht₂d, hbd, hdeq⟩ := hext₂ ht₂deg
  refine Or.inr ⟨d, ht₂d, hbd, hdeq, ?_⟩
  have huwne : p u ≠ p w := hp.ne huw.ne
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have huwdist : dist (p u) (p w) = r := nearestGraph_adj_dist_eq p hmin huw
  have huvdist : dist (p u) (p v) = r := nearestGraph_adj_dist_eq p hmin hvu.symm
  have hwvdist : dist (p w) (p v) = r := nearestGraph_adj_dist_eq p hmin hvw.symm
  let M := edgeCoordinate (p u) (p w)
  have hMu : M (p u) = 0 := edgeCoordinate_self (p u) (p w)
  have hMw : M (p w) = 1 := edgeCoordinate_axis (p u) (p w) huwne
  have hMvunit : ‖M (p v)‖ = 1 := by
    rw [edgeCoordinate_norm (p u) (p w) (p v) huwne, huvdist, huwdist]
    exact div_self hr.ne'
  have hMvunit₁ : ‖M (p v) - 1‖ = 1 := by
    rw [edgeCoordinate_sub_one_norm (p u) (p w) (p v) huwne, hwvdist, huwdist]
    exact div_self hr.ne'
  have hMvbelow : (M (p v)).im ≤ 0 :=
    edgeCoordinate_im_nonpos_of_support (p u) (p w) (p v) huwne (hsupport v)
  obtain ⟨h, hh, hhsq, hMv⟩ := unit_triangle_below_real_axis (M (p v))
    hMvunit hMvunit₁ hMvbelow
  have hMb : M (p b) = (3 / 2 : ℂ) - (h : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p u) (p b) (p v) (p w) hbsum
    change M (p u) + M (p b) = M (p v) + M (p w) at hs
    rw [hMu, hMw, hMv] at hs
    simpa only [zero_add] using hs.trans (by ring)
  have hMt : M (p t) = (1 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p w) (p t) (p v) (p b) htsum
    change M (p w) + M (p t) = M (p v) + M (p b) at hs
    calc
      M (p t) = (M (p w) + M (p t)) - M (p w) := by ring
      _ = (M (p v) + M (p b)) - M (p w) := by rw [hs]
      _ = _ := by rw [hMv, hMb, hMw]; push_cast; ring
  have hMt₂ : M (p t₂) = (2 : ℂ) - ((2 * h : ℝ) : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p v) (p t₂) (p t) (p b) ht₂sum
    change M (p v) + M (p t₂) = M (p t) + M (p b) at hs
    calc
      M (p t₂) = (M (p v) + M (p t₂)) - M (p v) := by ring
      _ = (M (p t) + M (p b)) - M (p v) := by rw [hs]
      _ = _ := by rw [hMt, hMb, hMv]; push_cast; ring
  have hdadd : p v + p d = p b + p b := by
    rw [hdeq, two_smul]
    abel
  have hMd : M (p d) = (5 / 2 : ℂ) - (h : ℂ) * Complex.I := by
    have hs := edgeCoordinate_add_eq_of_add_eq (p u) (p w)
      (p v) (p d) (p b) (p b) hdadd
    change M (p v) + M (p d) = M (p b) + M (p b) at hs
    calc
      M (p d) = (M (p v) + M (p d)) - M (p v) := by ring
      _ = (M (p b) + M (p b)) - M (p v) := by rw [hs]
      _ = _ := by rw [hMb, hMv]; ring
  exact normalized_shared_receiver_degree_le_four p hn hp huw hw hsupport
    h hh hhsq hMb hMt₂ hMd hbd.symm ht₂d.symm

end Erdos957
