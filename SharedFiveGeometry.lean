import BoundarySixNeighbors
import LocalCharge
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Degree slack in the shared degree-five case. No supporting-line or
receiver-interiority assertion is implicit in these statements. -/

namespace Erdos957

private theorem common_equilateral_vertices_not_adjacent {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t a b : Fin n}
    (hqt : (nearestGraph p).Adj q t)
    (hqa : (nearestGraph p).Adj q a)
    (hqb : (nearestGraph p).Adj q b)
    (hsum : p a + p b = p q + p t) :
    ¬ (nearestGraph p).Adj a b := by
  intro hab
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have h1 : ‖p a - p q‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hqa
  have h2 : ‖p b - p q‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hqb
  have hplus : (p a - p q) + (p b - p q) = p t - p q := by
    calc
      (p a - p q) + (p b - p q) = (p a + p b) - p q - p q := by abel
      _ = p t - p q := by rw [hsum]; abel
  have hminus : (p a - p q) - (p b - p q) = p a - p b := by abel
  have h3 : ‖p t - p q‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hqt
  have h4 : ‖p a - p b‖ = pairDist p ij := by
    simpa only [dist_eq_norm] using nearestGraph_adj_dist_eq p hmin hab
  have hpar := parallelogram_law_with_norm ℝ (p a - p q) (p b - p q)
  rw [hplus, hminus, h1, h2, h3, h4] at hpar
  nlinarith

/-- If a degree-five vertex contains a nearest-distance triangle whose two
other vertices have degree at most five, every edge to a degree-six vertex
has a common neighbor of degree at most five. This is an unconditional
degree-slack reduction; the selected receiver need not yet be interior. -/
theorem shared_five_six_edge_has_low_common_neighbor {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w : Fin n}
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqt : (nearestGraph p).Adj q t)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hudeg : (nearestGraph p).degree u ≤ 5)
    (hwdeg : (nearestGraph p).degree w ≤ 5) :
    ∃ a : Fin n, (nearestGraph p).Adj q a ∧
      (nearestGraph p).Adj t a ∧ (nearestGraph p).degree a ≤ 5 := by
  classical
  obtain ⟨a, b, hab, hta, hqa, htb, hqb⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp htdeg hqt.symm
  by_cases halow : (nearestGraph p).degree a ≤ 5
  · exact ⟨a, hqa, hta, halow⟩
  by_cases hblow : (nearestGraph p).degree b ≤ 5
  · exact ⟨b, hqb, htb, hblow⟩
  have hadeg : (nearestGraph p).degree a = 6 := by
    have := nearestGraph_degree_le_six p hn hp a
    omega
  have hbdeg : (nearestGraph p).degree b = 6 := by
    have := nearestGraph_degree_le_six p hn hp b
    omega
  obtain ⟨c, hct, hac, hqc, hcsum⟩ :=
    degree_six_triangle_completion p hn hp hadeg hqa.symm hta.symm hqt
  obtain ⟨d, hdt, hbd, hqd, hdsum⟩ :=
    degree_six_triangle_completion p hn hp hbdeg hqb.symm htb.symm hqt
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have habsum : p a + p b = p q + p t :=
    equilateral_rhombus (p q) (p t) (p a) (p b) (pairDist p ij)
      (pairDist_pos p hp hmin.1) (nearestGraph_adj_dist_eq p hmin hqt)
      (nearestGraph_adj_dist_eq p hmin hqa) (nearestGraph_adj_dist_eq p hmin hta)
      (nearestGraph_adj_dist_eq p hmin hqb) (nearestGraph_adj_dist_eq p hmin htb)
      (hp.ne hab)
  have hcb : c ≠ b := by
    intro heq
    have hdouble : p b + p b = p q + p q := by
      calc
        p b + p b = (p t + p c) + (p a + p b) - p a - p t := by rw [heq]; abel
        _ = (p a + p q) + (p q + p t) - p a - p t := by rw [hcsum, habsum]
        _ = p q + p q := by abel
    have heq' : p b = p q := by
      have hh : (2 : ℝ) • p b = (2 : ℝ) • p q := by simpa only [two_smul] using hdouble
      exact (smul_right_injective Point (by norm_num : (2 : ℝ) ≠ 0)) hh
    exact hqb.ne (hp heq').symm
  have hda : d ≠ a := by
    intro heq
    have hdouble : p a + p a = p q + p q := by
      calc
        p a + p a = (p t + p d) + (p a + p b) - p b - p t := by rw [heq]; abel
        _ = (p b + p q) + (p q + p t) - p b - p t := by rw [hdsum, habsum]
        _ = p q + p q := by abel
    have heq' : p a = p q := by
      have hh : (2 : ℝ) • p a = (2 : ℝ) • p q := by simpa only [two_smul] using hdouble
      exact (smul_right_injective Point (by norm_num : (2 : ℝ) ≠ 0)) hh
    exact hqa.ne (hp heq').symm
  have hcd : c ≠ d := by
    intro heq
    have heq' : p a = p b := by
      calc
        p a = (p t + p c) - p q := by rw [hcsum]; abel
        _ = (p t + p d) - p q := by rw [heq]
        _ = p b := by rw [hdsum]; abel
    exact hab (hp heq')
  have hset : ({t, a, b, c, d} : Finset (Fin n)) =
      (nearestGraph p).neighborFinset q := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals apply ((nearestGraph p).mem_neighborFinset q _).mpr
      all_goals assumption
    · rw [(nearestGraph p).card_neighborFinset_eq_degree, hqdeg]
      simp [hta.ne, htb.ne, hct.symm, hdt.symm, hab, hac.ne,
        hda.symm, hcb.symm, hbd.ne, hcd]
  have hwhich (k : Fin n) (hqk : (nearestGraph p).Adj q k)
      (hkdeg : (nearestGraph p).degree k ≤ 5) : k = c ∨ k = d := by
    have hk := ((nearestGraph p).mem_neighborFinset q k).mpr hqk
    rw [← hset] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | hc | hd
    · omega
    · omega
    · omega
    · exact Or.inl hc
    · exact Or.inr hd
  have hcdadj : (nearestGraph p).Adj c d := by
    rcases hwhich u hqu hudeg with rfl | rfl <;>
      rcases hwhich w hqw hwdeg with rfl | rfl
    · exact False.elim (huw.ne rfl)
    · exact huw
    · exact huw.symm
    · exact False.elim (huw.ne rfl)
  have habadj : (nearestGraph p).Adj a b := by
    apply (nearestGraph_adj_iff_dist_eq p hp hmin a b).mpr
    have hvec : p a - p b = p c - p d := by
      calc
        p a - p b = ((p t + p c) - p q) - ((p t + p d) - p q) := by
          rw [hcsum, hdsum]; abel
        _ = p c - p d := by abel
    rw [dist_eq_norm, hvec]
    exact nearestGraph_adj_dist_eq p hmin hcdadj
  exact False.elim (common_equilateral_vertices_not_adjacent p hn hp hqt hqa hqb habsum habadj)

/-- In particular, the low-degree triangle condition follows from two
actual diameter endpoints. The common receiver's low degree is proved,
without assuming it in advance. -/
theorem shared_five_diameter_triangle_low_common_neighbor {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w : Fin n}
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqt : (nearestGraph p).Adj q t)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p) :
    ∃ a : Fin n, (nearestGraph p).Adj q a ∧
      (nearestGraph p).Adj t a ∧ (nearestGraph p).degree a ≤ 5 := by
  apply shared_five_six_edge_has_low_common_neighbor p hn hp hqdeg htdeg hqt hqu hqw huw
  · have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp u hu
    omega
  · have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp w hw
    omega

/-- Once the common candidates are known to lie outside the diameter set,
the shared-five degree-six subcase supplies a valid local packet. The
geometric exclusion of diameter endpoints remains an explicit obligation;
this does not assert a simultaneous global choice or capacity bound. -/
noncomputable def localChargePacket_of_shared_five_six_edge {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w : Fin n}
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqt : (nearestGraph p).Adj q t)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hcommonout : ∀ a, (nearestGraph p).Adj q a →
      (nearestGraph p).Adj t a → a ∉ diameterEndpoints p) :
    LocalChargePacket p u := by
  classical
  let hex := shared_five_diameter_triangle_low_common_neighbor
    p hn hp hqdeg htdeg hqt hqu hqw huw hu hw
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  have hqout : q ∉ diameterEndpoints p := by
    intro hq
    have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp q hq
    omega
  exact {
    left := q
    right := a
    left_outside := hqout
    right_outside := hcommonout a ha.1 ha.2.1
    left_degree := hqdeg.le
    right_degree := ha.2.2
    repeated_degree := fun heq => False.elim (ha.1.ne heq)
    left_reachable := Or.inl hqu.symm
    right_reachable := Or.inr ⟨q, hqu.symm, ha.1⟩
  }

end Erdos957
