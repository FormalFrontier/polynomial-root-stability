/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Ultrametric

/-!
# Polynomial root uniqueness in an ultrametric derivative ball

A uniform coefficient bound controls the radius in which a root in the norm
unit ball is the only root. Local polynomial norm scaling forces two roots in
this derivative ball to have zero distance; separation gives equality.
Neither completeness nor division is required.
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
  have hnorm := norm_eval_sub_eq_of_mul_norm_sub_lt_norm_derivative
    (a := y) (b := x) hf hy hxy
  rw [hfx, hfy, sub_self, norm_zero] at hnorm
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hdpos : 0 < ‖f.derivative.eval y‖ :=
    (mul_nonneg hM (norm_nonneg (x - y))).trans_lt hxy
  have hdist : ‖x - y‖ = 0 :=
    (mul_eq_zero.mp hnorm.symm).resolve_left (ne_of_gt hdpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hdist)

end Polynomial
