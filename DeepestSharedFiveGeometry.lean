import BoundaryTriangleSix

/-! The two common receivers in the shared-five/six case both have spare
degree. Actual diameter endpoints provide a stronger conclusion than the
low-degree endpoints used in `SharedFiveGeometry`: no deepest-neighbor
assumption is needed for this degree conclusion. The paper's deepest choice
remains a separate obligation for the later capacity argument. -/

namespace Erdos957

/-- With actual diameter endpoints in the shared nearest-distance triangle,
every common neighbor of a five-six edge has degree at most five.

If such a common neighbor had degree six, completing its equilateral
triangle creates a further neighbor of `q`. The five known neighbors of
`q` exhaust its degree. The new vertex cannot be a common receiver, and
identifying it with a diameter endpoint would put a degree-six vertex next
to that endpoint, which `BoundaryTriangleSix` excludes. -/
theorem shared_five_diameter_triangle_common_neighbor_degree_le_five {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w a : Fin n}
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqt : (nearestGraph p).Adj q t)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p)
    (hqa : (nearestGraph p).Adj q a)
    (hta : (nearestGraph p).Adj t a) :
    (nearestGraph p).degree a ≤ 5 := by
  classical
  by_contra hnot
  have hadeg : (nearestGraph p).degree a = 6 := by
    have := nearestGraph_degree_le_six p hn hp a
    omega
  obtain ⟨b, hba, htb, hqb, _⟩ :=
    degree_six_triangle_completion p hn hp htdeg hqt.symm hta hqa
  obtain ⟨c, hct, hac, hqc, _⟩ :=
    degree_six_triangle_completion p hn hp hadeg hqa.symm hta.symm hqt
  have hane := shared_five_six_neighbor_ne_diameter_triangle_endpoints
    p hn hp hu hw hqdeg htdeg hqu hqw huw hta
  have hbne := shared_five_six_neighbor_ne_diameter_triangle_endpoints
    p hn hp hu hw hqdeg htdeg hqu hqw huw htb
  have htne : t ≠ u ∧ t ≠ w := by
    constructor
    · intro heq
      have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp u hu
      rw [heq] at htdeg
      omega
    · intro heq
      have := nearestGraph_degree_le_three_of_diameterEndpoint p hn hp w hw
      rw [heq] at htdeg
      omega
  have hcb : c ≠ b := by
    intro heq
    exact nearestGraph_common_neighbors_not_adjacent p hn hp hqt hqa hta hqb htb
      hba.symm (heq ▸ hac)
  have hset : ({t, a, b, u, w} : Finset (Fin n)) =
      (nearestGraph p).neighborFinset q := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals apply ((nearestGraph p).mem_neighborFinset q _).mpr
      all_goals assumption
    · rw [(nearestGraph p).card_neighborFinset_eq_degree, hqdeg]
      simp [hta.ne, htb.ne, htne.1, htne.2, hba.symm,
        hane.1, hane.2, hbne.1, hbne.2, huw.ne]
  have hc := ((nearestGraph p).mem_neighborFinset q c).mpr hqc
  rw [← hset] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hanot := shared_five_six_not_adjacent_diameter_triangle_endpoints
    p hn hp hu hw hqdeg hadeg hqu hqw huw
  rcases hc with h | h | h | h | h
  · exact hct h
  · exact hac.ne h.symm
  · exact hcb h
  · exact hanot.1 (h ▸ hac)
  · exact hanot.2 (h ▸ hac)

/-- The degree-six subcase has two distinct common receivers, each of
degree at most five. Diameter membership is essential to this interface;
mere degree bounds of five on `u,w` are not substituted for it. -/
theorem shared_five_diameter_triangle_two_low_common_neighbors {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {q t u w : Fin n}
    (hqdeg : (nearestGraph p).degree q = 5)
    (htdeg : (nearestGraph p).degree t = 6)
    (hqt : (nearestGraph p).Adj q t)
    (hqu : (nearestGraph p).Adj q u)
    (hqw : (nearestGraph p).Adj q w)
    (huw : (nearestGraph p).Adj u w)
    (hu : u ∈ diameterEndpoints p) (hw : w ∈ diameterEndpoints p) :
    ∃ a b : Fin n, a ≠ b ∧
      (nearestGraph p).Adj q a ∧ (nearestGraph p).Adj t a ∧
      (nearestGraph p).degree a ≤ 5 ∧
      (nearestGraph p).Adj q b ∧ (nearestGraph p).Adj t b ∧
      (nearestGraph p).degree b ≤ 5 := by
  obtain ⟨a, b, hab, hta, hqa, htb, hqb⟩ :=
    degree_six_edge_has_two_common_neighbors p hn hp htdeg hqt.symm
  exact ⟨a, b, hab, hqa, hta,
    shared_five_diameter_triangle_common_neighbor_degree_le_five
      p hn hp hqdeg htdeg hqt hqu hqw huw hu hw hqa hta,
    hqb, htb, shared_five_diameter_triangle_common_neighbor_degree_le_five
      p hn hp hqdeg htdeg hqt hqu hqw huw hu hw hqb htb⟩

end Erdos957
