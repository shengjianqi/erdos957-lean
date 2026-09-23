import DiameterHull
import PlanarDirections
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! Radial ordering of actual convex-hull vertices around an interior point. -/

namespace Erdos957

private theorem extreme_ne_interior (S : Set Point) {y c : Point}
    (hy : y ∈ S.extremePoints ℝ) (hc : c ∈ interior S) : y ≠ c := by
  intro h
  subst y
  exact (Set.disjoint_left.mp (disjoint_interior_extremePoints S)) hc hy

private theorem same_arg_near_interior (S : Set Point) (hS : Convex ℝ S)
    {c y z : Point} (hc : c ∈ interior S) (hy : y ∈ S.extremePoints ℝ)
    (hz : z ∈ S.extremePoints ℝ) (hyz : y ≠ z)
    (harg : (pointToComplex (z - c)).arg = (pointToComplex (y - c)).arg)
    (hle : ‖pointToComplex (y - c)‖ ≤ ‖pointToComplex (z - c)‖) :
    y ∈ interior S := by
  let t : ℝ := ‖pointToComplex (y - c)‖ / ‖pointToComplex (z - c)‖
  have hyc : y ≠ c := extreme_ne_interior S hy hc
  have hzc : z ≠ c := extreme_ne_interior S hz hc
  have hzy0 : pointToComplex (z - c) ≠ 0 := by
    intro h
    have : z - c = 0 := pointToComplex.injective (by simpa using h)
    exact hzc (sub_eq_zero.mp this)
  have hy0 : pointToComplex (y - c) ≠ 0 := by
    intro h
    have : y - c = 0 := pointToComplex.injective (by simpa using h)
    exact hyc (sub_eq_zero.mp this)
  have hratio := (Complex.arg_eq_arg_iff hzy0 hy0).mp harg
  have htpos : 0 < t := div_pos (norm_pos_iff.mpr hy0) (norm_pos_iff.mpr hzy0)
  have htle : t ≤ 1 := (div_le_one (norm_pos_iff.mpr hzy0)).mpr hle
  have hlinear : y - c = t • (z - c) := by
    apply pointToComplex.injective
    simpa only [map_smul, Complex.real_smul, t, Complex.ofReal_div] using hratio.symm
  have htne : t ≠ 1 := by
    intro h
    have : y = z := by
      rw [h, one_smul] at hlinear
      have hsum := congrArg (· + c) hlinear
      simpa only [sub_add_cancel] using hsum
    exact hyz this
  have htlt : t < 1 := lt_of_le_of_ne htle htne
  have heq : y = (1 - t) • c + t • z := by
    calc
      y = (y - c) + c := by module
      _ = t • (z - c) + c := by rw [hlinear]
      _ = (1 - t) • c + t • z := by module
  rw [heq]
  exact hS.combo_interior_self_mem_interior hc
    (extremePoints_subset hz) (by linarith) (le_of_lt htpos) (by ring)

/-- Distinct extreme points have distinct principal arguments about an interior point. -/
theorem hull_extreme_radial_arg_injOn {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) :
    Set.InjOn (fun i => (pointToComplex (p i - c)).arg)
      (hullVertexIndices p : Set (Fin n)) := by
  classical
  intro i hi j hj harg
  have hei : p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hi).2
  have hej : p j ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hj).2
  by_contra hij
  have hpij : p i ≠ p j := fun h => hij (hp h)
  let S := convexHull ℝ (Set.range p)
  have hle := le_total (‖pointToComplex (p i - c)‖) (‖pointToComplex (p j - c)‖)
  rcases hle with hle | hle
  · have hiinside := same_arg_near_interior S (convex_convexHull ℝ (Set.range p))
      hc hei hej hpij harg.symm hle
    exact (Set.disjoint_left.mp (disjoint_interior_extremePoints S)) hiinside hei
  · have hjinside := same_arg_near_interior S (convex_convexHull ℝ (Set.range p))
      hc hej hei (Ne.symm hpij) harg hle
    exact (Set.disjoint_left.mp (disjoint_interior_extremePoints S)) hjinside hej

/-- Enumerate hull vertices in strictly increasing principal radial argument. -/
theorem hull_extreme_radial_order {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (c : Point)
    (hc : c ∈ interior (convexHull ℝ (Set.range p))) :
    ∃ v : Fin (hullVertexCount p) → Fin n,
      Function.Injective v ∧
      Set.range v = (hullVertexIndices p : Set (Fin n)) ∧
      StrictMono (fun i => (pointToComplex (p (v i) - c)).arg) ∧
      (∀ i, (pointToComplex (p (v i) - c)).arg ∈ Set.Ioc (-Real.pi) Real.pi) := by
  classical
  let θ : Fin n → ℝ := fun i => (pointToComplex (p i - c)).arg
  let H := hullVertexIndices p
  let A := H.image θ
  have hθinj : Set.InjOn θ (H : Set (Fin n)) := hull_extreme_radial_arg_injOn p hp c hc
  have hcard : A.card = hullVertexCount p := by
    calc
      A.card = H.card := Finset.card_image_of_injOn hθinj
      _ = hullVertexCount p := rfl
  let a := A.orderEmbOfFin hcard
  have hpre (i : Fin (hullVertexCount p)) : ∃ j ∈ H, θ j = a i := by
    exact Finset.mem_image.mp (A.orderEmbOfFin_mem hcard i)
  choose v hvH hvθ using hpre
  have hvinj : Function.Injective v := by
    intro i j hij
    apply a.injective
    calc
      a i = θ (v i) := (hvθ i).symm
      _ = θ (v j) := congrArg θ hij
      _ = a j := hvθ j
  have hrange : Set.range v = (H : Set (Fin n)) := by
    ext j
    constructor
    · rintro ⟨i, rfl⟩
      exact hvH i
    · intro hj
      have hjA : θ j ∈ A := Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have hjrange : θ j ∈ Set.range a := by
        rw [Finset.range_orderEmbOfFin]
        exact hjA
      obtain ⟨i, hi⟩ := hjrange
      exact ⟨i, hθinj (hvH i) hj (by rw [hvθ i, hi])⟩
  refine ⟨v, hvinj, hrange, ?_, ?_⟩
  · change StrictMono (fun i => θ (v i))
    simpa only [hvθ] using a.strictMono
  · intro i
    exact Complex.arg_mem_Ioc _

end Erdos957
