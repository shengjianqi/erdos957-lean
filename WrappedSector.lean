import RadialAngles
import Mathlib.Tactic.Linarith

/-!
The complementary sector across the branch cut cannot have positive turns
on both of its bounding rays.
-/

namespace Erdos957

/-- A ray whose principal argument lies between `b` and `a` cannot be strictly
left of both the oriented rays `a → q` and `q → b`. -/
theorem not_two_pos_turns_of_wrapped_arg_between (c a b q : Point)
    (hβγ : (pointToComplex (b - c)).arg ≤ (pointToComplex (q - c)).arg)
    (hγα : (pointToComplex (q - c)).arg ≤ (pointToComplex (a - c)).arg) :
    ¬ (0 < turn c a q ∧ 0 < turn c q b) := by
  let za := pointToComplex (a - c)
  let zb := pointToComplex (b - c)
  let zq := pointToComplex (q - c)
  change zb.arg ≤ zq.arg at hβγ
  change zq.arg ≤ za.arg at hγα
  intro ⟨ht₁, ht₂⟩
  rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub] at ht₁ ht₂
  change 0 < ‖za‖ * ‖zq‖ * Real.sin (zq.arg - za.arg) at ht₁
  change 0 < ‖zq‖ * ‖zb‖ * Real.sin (zb.arg - zq.arg) at ht₂
  by_cases h : -Real.pi ≤ zq.arg - za.arg
  · have hs : Real.sin (zq.arg - za.arg) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) h
    have hprod : ‖za‖ * ‖zq‖ * Real.sin (zq.arg - za.arg) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs
    linarith
  · have hβ : -Real.pi < zb.arg := (Complex.arg_mem_Ioc zb).1
    have hα : za.arg ≤ Real.pi := (Complex.arg_mem_Ioc za).2
    have hs : Real.sin (zb.arg - zq.arg) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    have hprod : ‖zq‖ * ‖zb‖ * Real.sin (zb.arg - zq.arg) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs
    linarith

end Erdos957
