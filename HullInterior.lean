import Foundations
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! A finite noncollinear planar set has a convex hull with nonempty interior. -/

namespace Erdos957

theorem hull_interior_nonempty_of_not_collinear {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hnot : ¬ Collinear ℝ (Set.range p)) :
    (interior (convexHull ℝ (Set.range p))).Nonempty := by
  let S : Set Point := Set.range p
  have hfinrank : Module.finrank ℝ Point = 2 := by simp [Point]
  have hgt : 1 < Module.finrank ℝ (vectorSpan ℝ S) := by
    apply Nat.lt_of_not_ge
    intro hle
    exact hnot (collinear_iff_finrank_le_one.mpr hle)
  have hle : Module.finrank ℝ (vectorSpan ℝ S) ≤ Module.finrank ℝ Point :=
    (vectorSpan ℝ S).finrank_le
  have heq : Module.finrank ℝ (vectorSpan ℝ S) = Module.finrank ℝ Point := by
    omega
  have hvec : vectorSpan ℝ S = ⊤ := Submodule.eq_top_of_finrank_eq heq
  have hnonempty : S.Nonempty := by
    let i : Fin n := ⟨0, by omega⟩
    exact ⟨p i, ⟨i, rfl⟩⟩
  have hspan : affineSpan ℝ S = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
      ℝ Point Point hnonempty).mpr hvec
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan

end Erdos957
