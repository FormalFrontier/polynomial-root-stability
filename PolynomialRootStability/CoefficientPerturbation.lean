/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Ultrametric

/-!
# Root bounds under coefficient perturbation

A uniform perturbation of polynomial coefficients bounds the distance between roots
that lie in the original polynomial's strict derivative ball. The bound is scaled
by the original derivative norm and is quantitative over ultrametric seminormed
commutative rings with multiplicative norm; no separation assumption is needed.
-/

@[expose] public section

universe u

namespace Polynomial

/-- Coefficientwise perturbations bound the original derivative norm times the
root distance when both roots lie in the original strict derivative ball about a
center in the norm unit ball. -/
theorem norm_derivative_eval_mul_norm_sub_le_of_norm_coeff_sub_le
    {R : Type u} [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f g : R[X]} {M ε : ℝ} {a x y : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hx : f.eval x = 0)
    (hy : g.eval y = 0)
    (hxa : M * ‖x - a‖ < ‖f.derivative.eval a‖)
    (hya : M * ‖y - a‖ < ‖f.derivative.eval a‖)
    (hdiff : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε) :
    ‖f.derivative.eval a‖ * ‖x - y‖ ≤ ε := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hf' : ∀ n : ℕ, ‖f.derivative.coeff n‖ ≤ M :=
    norm_derivative_coeff_le_of_norm_coeff_le hf
  have hd : ‖f.derivative.eval a‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le hf' ha
  have hMpos : 0 < M :=
    (mul_nonneg hM (norm_nonneg (y - a))).trans_lt (hya.trans_le hd)
  have hdist : ‖y - a‖ < 1 :=
    lt_of_mul_lt_mul_left
      (by simpa only [mul_one] using hya.trans_le hd) hMpos.le
  have hy_unit : ‖y‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (y - a) a).trans (max_le hdist.le ha)
  have hcoeff : ∀ n : ℕ, ‖(f - g).coeff n‖ ≤ ε := by
    intro n
    simpa only [coeff_sub] using hdiff n
  calc
    ‖f.derivative.eval a‖ * ‖x - y‖ =
        ‖f.derivative.eval a‖ * ‖y - x‖ := by rw [norm_sub_rev x y]
    _ = ‖f.eval y - f.eval x‖ :=
      (norm_eval_sub_eval_eq_of_mul_norm_sub_lt_norm_derivative hf ha hxa hya).symm
    _ = ‖(f - g).eval y‖ := by simp only [eval_sub, hx, hy, sub_zero]
    _ ≤ ε := norm_eval_le_of_norm_coeff_le hcoeff hy_unit

end Polynomial
