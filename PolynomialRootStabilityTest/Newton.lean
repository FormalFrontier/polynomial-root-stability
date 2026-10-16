/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Newton
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.NumberTheory.Padics.PadicIntegers

import Mathlib.Tactic.NormNum

/-!
# A quadratic approximate root over the 2-adic field

For `f = X² - 17` over `ℚ_[2]`, the integral starting point `1` has nonzero
error of norm `1 / 16` and derivative of norm `1 / 2`. Thus the error is strictly
smaller than the square of the derivative norm, even though the derivative is
not a unit in the valuation integers `ℤ_[2]`. It is a unit in the field.
The polynomial is monic and all its coefficients have norm at most one.

The field, norm, ultrametric inequality and completeness are Mathlib's standard
structures on the 2-adic numbers. The input calculations are proved independently
of quantitative lifting. A further application of the general quantitative lifting
statement gives convergence of the explicit Newton iterates to an integral root,
exact distance `1 / 8`, derivative-norm stability, nonzero denominators and local
uniqueness. The input calculation is independent of the root-existence proof.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter II, §1, Corollary 3 and Exercise 1, motivate the
  quantitative approximate-root hypotheses with a nonunit derivative.
* Mathlib's p-adic development by Robert Y. Lewis, Mario Carneiro and Johan
  Commelin: `Mathlib.NumberTheory.Padics.PadicNumbers` provides the complete
  ultrametric normed field and the bounds `Padic.norm_p` and
  `Padic.norm_int_le_one`; `Mathlib.NumberTheory.Padics.PadicIntegers`
  provides the unit criterion for the valuation integers.
-/

public section

open Filter Function
open scoped Topology

namespace Polynomial

/-- The monic integral quadratic `X² - 17` at `1` over the 2-adic field satisfies
the strict quantitative approximate-root inequality, with nonzero error and
nonunit derivative in the valuation integers. -/
theorem sq_sub_seventeen_padic_two_data :
    let f : ℚ_[2][X] := X ^ 2 - C 17
    f.Monic ∧
      (∀ n, ‖f.coeff n‖ ≤ 1) ∧
      ‖(1 : ℚ_[2])‖ ≤ 1 ∧
      f.eval 1 ≠ 0 ∧
      ‖f.eval 1‖ = (1 / 16 : ℝ) ∧
      ‖f.derivative.eval 1‖ = (1 / 2 : ℝ) ∧
      ‖f.eval 1‖ < ‖f.derivative.eval 1‖ ^ 2 ∧
      ‖f.derivative.eval 1‖ < 1 ∧
      ¬ IsUnit (2 : ℤ_[2]) := by
  let f : ℚ_[2][X] := X ^ 2 - C 17
  have hvalue : f.eval 1 = -(2 : ℚ_[2]) ^ 4 := by
    norm_num [f]
  have hderiv : f.derivative.eval 1 = (2 : ℚ_[2]) := by
    norm_num [f]
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  have herror : ‖f.eval 1‖ = (1 / 16 : ℝ) := by
    rw [hvalue, norm_neg, norm_pow, htwo]
    norm_num
  have hderivNorm : ‖f.derivative.eval 1‖ = (1 / 2 : ℝ) := by
    rw [hderiv, htwo]
  refine ⟨monic_X_pow_sub_C _ (by decide), ?_, by simp, ?_, herror, hderivNorm, ?_, ?_, ?_⟩
  · intro n
    by_cases h2 : n = 2
    · simp [h2]
    by_cases h0 : n = 0
    · subst n
      simpa using Padic.norm_int_le_one (p := 2) (-17)
    · simp [coeff_X_pow, coeff_C, h2, h0]
  · rw [hvalue]
    norm_num
  · rw [herror, hderivNorm]
    norm_num
  · rw [hderivNorm]
    norm_num
  · exact PadicInt.not_isUnit_iff.mpr (Padic.norm_p_lt_one (p := 2))

/-- Newton iteration for `X² - 17` at `1` over `ℚ_[2]` converges to an integral root
at distance exactly `1 / 8`. The derivative norm is `1 / 2`, every denominator is
nonzero, and the root is unique within distance strictly less than `1 / 2` of `1`.
This application uses the general quantitative lifting theorem. -/
theorem sq_sub_seventeen_padic_two_newton :
    let f : ℚ_[2][X] := X ^ 2 - C 17
    ∃ a : ℚ_[2], a ^ 2 = 17 ∧ ‖a‖ ≤ 1 ∧
      ‖a - 1‖ = (1 / 8 : ℝ) ∧ ‖a - 1‖ < (1 / 2 : ℝ) ∧
      ‖(2 : ℚ_[2]) * a‖ = (1 / 2 : ℝ) ∧
      Tendsto (fun n : ℕ => f.newtonMap^[n] (1 : ℚ_[2])) atTop (𝓝 a) ∧
      (∀ n : ℕ, ‖f.newtonMap^[n] (1 : ℚ_[2])‖ ≤ 1 ∧
        (2 : ℚ_[2]) * (f.newtonMap^[n] (1 : ℚ_[2])) ≠ 0 ∧
        ‖(2 : ℚ_[2]) * (f.newtonMap^[n] (1 : ℚ_[2]))‖ = (1 / 2 : ℝ)) ∧
      ∀ b : ℚ_[2], b ^ 2 = 17 → ‖b - 1‖ < (1 / 2 : ℝ) → b = a := by
  let f : ℚ_[2][X] := X ^ 2 - C 17
  obtain ⟨_, hf, hstart, _, herror, hderiv, hclose, _, _⟩ :=
    sq_sub_seventeen_padic_two_data
  obtain ⟨a, hroot, hintegral, hdist, hdist_lt, hroot_deriv, hconv, hiter, huniq⟩ :=
    exists_root_tendsto_iterate_newtonMap hf hstart hclose
  have hderiv_eval (x : ℚ_[2]) :
      (X ^ 2 - C 17 : ℚ_[2][X]).derivative.eval x = 2 * x := by
    simp only [derivative_sub, derivative_X_sq, derivative_C, sub_zero,
      eval_mul, eval_C, eval_X]
  refine ⟨a, ?_, hintegral, ?_, ?_, ?_, hconv, ?_, ?_⟩
  · simpa [sub_eq_zero] using hroot
  · rw [herror, hderiv] at hdist
    norm_num at hdist
    exact hdist
  · simpa only [hderiv] using hdist_lt
  · rw [hderiv] at hroot_deriv
    simpa only [hderiv_eval] using hroot_deriv
  · intro n
    obtain ⟨hnorm, hne, hnorm_deriv⟩ := hiter n
    rw [hderiv] at hnorm_deriv
    exact ⟨hnorm, by simpa only [hderiv_eval] using hne,
      by simpa only [hderiv_eval] using hnorm_deriv⟩
  · intro b hb hdist_b
    apply huniq b
    · simp [hb]
    · simpa only [hderiv] using hdist_b

end Polynomial
