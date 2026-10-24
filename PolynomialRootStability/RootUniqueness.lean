/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Ultrametric

/-!
# Polynomial root uniqueness in an ultrametric derivative ball

A uniform coefficient bound controls the radius in which a root in the norm
unit ball is the only root. Neither completeness nor division is required.
The standard first-order Taylor argument uses the derivative bound to put the
other root in the unit ball, then compares the linear term with the quadratic
remainder.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A root in the norm unit ball is the only root at distance strictly less
than its derivative norm divided by a uniform coefficient bound, expressed
without division. -/
theorem eq_of_eval_eq_zero_of_mul_norm_sub_lt_norm_derivative
    {R : Type u} [NormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f : R[X]} {M : ℝ} {x y : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hy : ‖y‖ ≤ 1)
    (hfx : f.eval x = 0) (hfy : f.eval y = 0)
    (hxy : M * ‖x - y‖ < ‖f.derivative.eval y‖) : x = y := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hd : ‖f.derivative.eval y‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hf) hy
  have hdist : ‖x - y‖ < 1 :=
    lt_of_mul_lt_mul_left
      (by simpa only [mul_one] using hxy.trans_le hd) hM
  have hx : ‖x‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (x - y) y).trans (max_le hdist.le hy)
  by_contra hne
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have ht := norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le hf hx hy
  simp only [hfx, hfy, sub_self, zero_sub, norm_neg, norm_mul] at ht
  have hlt : M * ‖x - y‖ ^ 2 < ‖f.derivative.eval y‖ * ‖x - y‖ := by
    simpa only [pow_two, mul_assoc] using mul_lt_mul_of_pos_right hxy hr
  exact (not_lt_of_ge ht) hlt

end Polynomial
