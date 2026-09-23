import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Counting graph edges by a choice of one incident edge at each active vertex. -/

namespace Erdos957

/-- If every edge is selected by one of its endpoints in `A`, then the graph
has at most `A.card` edges. No bound on individual vertex degrees is needed. -/
theorem card_edges_le_of_endpoint_selection {V : Type*}
    (G : SimpleGraph V) [Fintype G.edgeSet] (A : Finset V) (f : V → V)
    (hcover : ∀ u v, G.Adj u v →
      (u ∈ A ∧ f u = v) ∨ (v ∈ A ∧ f v = u)) :
    G.edgeFinset.card ≤ A.card := by
  classical
  have hsub : G.edgeFinset ⊆ A.image (fun u => Sym2.mk u (f u)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hadj : G.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rcases hcover u v hadj with hu | hv
      · exact Finset.mem_image.mpr ⟨u, hu.1, by rw [hu.2]⟩
      · exact Finset.mem_image.mpr ⟨v, hv.1, by rw [hv.2]; exact Sym2.eq_swap⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end Erdos957
