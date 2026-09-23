import RadialAngles
import Mathlib.Tactic.Linarith

namespace Erdos957

open scoped BigOperators

/-- The next index in a nonempty cyclic enumeration. -/
def cyclicNext {h : ℕ} [NeZero h] (i : Fin h) : Fin h := i + 1

/-- Lift the next angle across the principal branch cut at the last index. -/
noncomputable def wrapLift {h : ℕ} [NeZero h] (E : Fin h → ℝ) (i : Fin h) : ℝ :=
  E (cyclicNext i) + if i.val + 1 = h then 2 * Real.pi else 0

private theorem sum_cyclicNext {h : ℕ} [NeZero h] (E : Fin h → ℝ) :
    ∑ i, E (cyclicNext i) = ∑ i, E i := by
  simpa only [cyclicNext] using
    (Fintype.sum_equiv (Equiv.addRight (1 : Fin h))
      (fun i => E (i + 1)) E (by intro i; rfl))

/-- The sum of lifted consecutive differences makes one complete turn. -/
theorem sum_wrapLift_sub {h : ℕ} [NeZero h] (E : Fin h → ℝ) :
    ∑ i : Fin h, (wrapLift E i - E i) = 2 * Real.pi := by
  have hh : 0 < h := NeZero.pos h
  let last : Fin h := ⟨h - 1, by omega⟩
  have hlast (i : Fin h) : (i.val + 1 = h) ↔ i = last := by
    constructor
    · intro hi
      apply Fin.ext
      change i.val = h - 1
      omega
    · intro hi
      subst i
      change h - 1 + 1 = h
      omega
  have hwrap : (∑ i : Fin h, if i.val + 1 = h then 2 * Real.pi else 0) =
      2 * Real.pi := by
    simp_rw [hlast]
    simp
  simp only [wrapLift, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_cyclicNext, hwrap]
  ring

private theorem cyclicNext_val {h : ℕ} [NeZero h] (i : Fin h) :
    (cyclicNext i).val = (i.val + 1) % h := by
  simp [cyclicNext, Fin.val_add]

/-- Strict principal radial order becomes strict cyclic order after adding
`2π` at the last index. -/
theorem lt_wrapLift_of_strictMono {h : ℕ} [NeZero h] (hh : 3 ≤ h)
    (θ : Fin h → ℝ) (hθ : StrictMono θ)
    (hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi)
    (i : Fin h) : θ i < wrapLift θ i := by
  by_cases hi : i.val + 1 = h
  · have hnext : cyclicNext i = ⟨0, by omega⟩ := by
      apply Fin.ext
      rw [cyclicNext_val]
      simp [hi]
    have hilast : i = ⟨h - 1, by omega⟩ := by
      apply Fin.ext
      change i.val = h - 1
      omega
    have hlt : θ i < θ (cyclicNext i) + 2 * Real.pi := by
      have heq : θ i = θ ⟨h - 1, by omega⟩ := congrArg θ hilast
      rw [hnext]
      linarith [hspan, heq]
    simpa [wrapLift, hi] using hlt
  · have hlt : i.val + 1 < h := by omega
    have hnext : i < cyclicNext i := by
      change i.val < (cyclicNext i).val
      rw [cyclicNext_val]
      rw [Nat.mod_eq_of_lt hlt]
      omega
    simpa [wrapLift, hi] using hθ hnext

/-- Chord angle bounds force each lifted difference of consecutive chord
angles to lie strictly between `-π` and `π`. -/
theorem cyclic_angle_gap_bounds {h : ℕ} [NeZero h] (hh : 3 ≤ h)
    (θ E : Fin h → ℝ) (hθ : StrictMono θ)
    (hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi)
    (hE : ∀ i, wrapLift θ i < E i ∧ E i < θ i + Real.pi)
    (i : Fin h) :
    -Real.pi < wrapLift E i - E i ∧
      wrapLift E i - E i < Real.pi := by
  have hstep := lt_wrapLift_of_strictMono hh θ hθ hspan i
  have hstepNext := lt_wrapLift_of_strictMono hh θ hθ hspan (cyclicNext i)
  have hnextLower := (hE (cyclicNext i)).1
  have hnextUpper := (hE (cyclicNext i)).2
  have hiLower := (hE i).1
  have hiUpper := (hE i).2
  dsimp [wrapLift] at hstep hstepNext hnextLower hiLower ⊢
  constructor <;> linarith

/-- Positive sine selects the positive branch of each lifted turn. -/
theorem cyclic_angle_gaps_pos_lt_pi {h : ℕ} [NeZero h] (hh : 3 ≤ h)
    (θ E : Fin h → ℝ) (hθ : StrictMono θ)
    (hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi)
    (hE : ∀ i, wrapLift θ i < E i ∧ E i < θ i + Real.pi)
    (hsin : ∀ i, 0 < Real.sin (wrapLift E i - E i))
    (i : Fin h) :
    0 < wrapLift E i - E i ∧ wrapLift E i - E i < Real.pi := by
  obtain ⟨hlo, hhi⟩ := cyclic_angle_gap_bounds hh θ E hθ hspan hE i
  refine ⟨?_, hhi⟩
  by_contra hn
  have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (le_of_not_gt hn) hlo.le
  linarith [hsin i]

end Erdos957
