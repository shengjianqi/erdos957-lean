import AngularPacking
import PlanarDirections

/-! The planar kissing-number bound needed by the closest-pair graph. -/

namespace Erdos957

/-- A circle of positive radius contains at most six points whose pairwise
distances are at least the radius. No general-position assumption is needed. -/
theorem circle_card_le_six
    (N : Finset Point) (x : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) :
    N.card ≤ 6 := by
  classical
  let directions := N.image (directionArg x)
  have hcard : directions.card = N.card :=
    Finset.card_image_of_injOn
      (neighbor_directionArg_injOn N x r hr hradius hsep)
  rw [← hcard]
  apply card_le_six_of_angles directions
  · intro θ hθ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    exact directionArg_mem_Ioc x y
  · intro θ hθ φ hφ hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hφ
    have hyz : y ≠ z := fun heq => hne (congrArg (directionArg x) heq)
    exact neighbor_directionArg_separated N x r hr hradius hsep hy hz hyz

end Erdos957
