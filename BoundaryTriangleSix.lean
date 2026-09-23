import BoundarySixNeighbors

/-! A low-degree nearest triangle at a diameter endpoint excludes any
degree-six nearest neighbor of that endpoint. -/

namespace Erdos957

/-- Distinct common neighbors of a closest-pair edge cannot themselves
form a closest pair: their two equilateral triangles form a rhombus. -/
theorem nearestGraph_common_neighbors_not_adjacent {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u t a b : Fin n}
    (hut : (nearestGraph p).Adj u t)
    (hua : (nearestGraph p).Adj u a)
    (hta : (nearestGraph p).Adj t a)
    (hub : (nearestGraph p).Adj u b)
    (htb : (nearestGraph p).Adj t b)
    (hab : a ≠ b) : ¬ (nearestGraph p).Adj a b := by
  intro hadj
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have hsum : p a + p b = p u + p t :=
    equilateral_rhombus (p u) (p t) (p a) (p b) (pairDist p ij) hr
      (nearestGraph_adj_dist_eq p hmin hut)
      (nearestGraph_adj_dist_eq p hmin hua)
      (nearestGraph_adj_dist_eq p hmin hta)
      (nearestGraph_adj_dist_eq p hmin hub)
      (nearestGraph_adj_dist_eq p hmin htb) (hp.ne hab)
  have h1 : ‖p a - p u‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hua
  have h2 : ‖p b - p u‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hub
  have hplus : (p a - p u) + (p b - p u) = p t - p u := by
    calc
      (p a - p u) + (p b - p u) = (p a + p b) - p u - p u := by abel
      _ = p t - p u := by rw [hsum]; abel
  have hminus : (p a - p u) - (p b - p u) = p a - p b := by abel
  have h3 : ‖p t - p u‖ = pairDist p ij := by
    simpa only [dist_eq_norm, norm_sub_rev] using nearestGraph_adj_dist_eq p hmin hut
  have h4 : ‖p a - p b‖ = pairDist p ij := by
    simpa only [dist_eq_norm] using nearestGraph_adj_dist_eq p hmin hadj
  have hpar := parallelogram_law_with_norm ℝ (p a - p u) (p b - p u)
  rw [hplus, hminus, h1, h2, h3, h4] at hpar
  nlinarith

/-- An endpoint in a closest-pair triangle whose other vertices have degree
at most five has no degree-six neighbor. No flatness or scale hypothesis
is needed. -/
theorem diameterEndpoint_triangle_neighbor_degree_le_five {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u q w t : Fin n}
    (hu : u ∈ diameterEndpoints p)
    (huq : (nearestGraph p).Adj u q)
    (huw : (nearestGraph p).Adj u w)
    (hqw : (nearestGraph p).Adj q w)
    (hqdeg : (nearestGraph p).degree q ≤ 5)
    (hwdeg : (nearestGraph p).degree w ≤ 5)
    (hut : (nearestGraph p).Adj u t) :
    (nearestGraph p).degree t ≤ 5 := by
  classical
  by_contra hnot
  have htdeg : (nearestGraph p).degree t = 6 := by
    have := nearestGraph_degree_le_six p hn hp t
    omega
  obtain ⟨a, b, hab, hta, hua, htb, hub⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp htdeg hut.symm
  have hset : ({t, a, b} : Finset (Fin n)) =
      (nearestGraph p).neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      all_goals apply ((nearestGraph p).mem_neighborFinset u _).mpr
      all_goals assumption
    · rw [(nearestGraph p).card_neighborFinset_eq_degree]
      simpa only [Finset.card_insert_of_notMem, Finset.mem_insert,
        Finset.mem_singleton, hta.ne, htb.ne, hab, or_self, not_false_eq_true,
        Finset.card_singleton] using
        nearestGraph_degree_le_three_of_diameterEndpoint p hn hp u hu
  have hwhich (k : Fin n) (huk : (nearestGraph p).Adj u k)
      (hkdeg : (nearestGraph p).degree k ≤ 5) : k = a ∨ k = b := by
    have hk := ((nearestGraph p).mem_neighborFinset u k).mpr huk
    rw [← hset] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | ha | hb
    · omega
    · exact Or.inl ha
    · exact Or.inr hb
  have hadj : (nearestGraph p).Adj a b := by
    rcases hwhich q huq hqdeg with rfl | rfl <;>
      rcases hwhich w huw hwdeg with rfl | rfl
    · exact False.elim (hqw.ne rfl)
    · exact hqw
    · exact hqw.symm
    · exact False.elim (hqw.ne rfl)
  exact nearestGraph_common_neighbors_not_adjacent p hn hp hut hua hta hub htb hab hadj

/-- In the shared-five triangle, a degree-six vertex cannot be adjacent to
either of the two diameter endpoints. -/
theorem shared_five_six_not_adjacent_diameter_triangle_endpoints {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w : Fin n}
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w) :
    ¬ (nearestGraph p).Adj t u ∧ ¬ (nearestGraph p).Adj t w := by
  have hudeg : (nearestGraph p).degree u ≤ 5 :=
    le_trans (nearestGraph_degree_le_three_of_diameterEndpoint p hn hp u hu) (by decide)
  have hwdeg : (nearestGraph p).degree w ≤ 5 :=
    le_trans (nearestGraph_degree_le_three_of_diameterEndpoint p hn hp w hw) (by decide)
  constructor
  · intro htu
    have := diameterEndpoint_triangle_neighbor_degree_le_five
      p hn hp hu hqu.symm huw hqw hqdeg.le hwdeg htu.symm
    omega
  · intro htw
    have := diameterEndpoint_triangle_neighbor_degree_le_five
      p hn hp hw hqw.symm huw.symm hqu hqdeg.le hudeg htw.symm
    omega

/-- Every closest-pair neighbor of a degree-six vertex avoids both boundary
endpoints of a shared-five triangle. In particular this applies to all
common neighbors of the five-six edge. -/
theorem shared_five_six_neighbor_ne_diameter_triangle_endpoints {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w a : Fin n}
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hta : (nearestGraph p).Adj t a) : a ≠ u ∧ a ≠ w := by
  have h := shared_five_six_not_adjacent_diameter_triangle_endpoints
    p hn hp hu hw hqdeg htdeg hqu hqw huw
  exact ⟨fun heq => h.1 (heq ▸ hta), fun heq => h.2 (heq ▸ hta)⟩

end Erdos957
