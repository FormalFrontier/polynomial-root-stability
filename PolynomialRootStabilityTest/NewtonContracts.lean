/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Newton

/-!
# Boundary cases for polynomial Newton iteration

At an exact root the iterates are stationary. A nonconstant linear polynomial reaches
its root in one step, with no monicity or characteristic hypothesis. A constant polynomial
has zero derivative, so the total Newton map is stationary even if the polynomial is nonzero;
the nonzero-denominator conclusion in quantitative lifting is therefore essential.
-/

@[expose] public section

open Polynomial Function

namespace PolynomialRootStabilityTest.NewtonContracts

universe u

/-- Newton iteration at an exact root is stationary, including when its derivative vanishes. -/
theorem iterate_at_root {K : Type u} [Field K] {f : K[X]} {a : K}
    (h : f.eval a = 0) (n : ℕ) : f.newtonMap^[n] a = a := by
  exact (f.isFixedPt_newtonMap_of_aeval_eq_zero
    (by simpa only [coe_aeval_eq_eval] using h)).iterate n

/-- A linear polynomial with any nonzero slope reaches its root after one Newton step. -/
theorem iterate_linear {K : Type u} [Field K] (a b c : K) (hc : c ≠ 0) (n : ℕ) :
    (C c * X - C b).newtonMap^[n + 1] a = b / c := by
  rw [iterate_succ_apply', newtonMap_apply_eq_sub_div]
  simp [coe_aeval_eq_eval, sub_div, hc]

/-- If the denominator vanishes identically, the total Newton map is stationary. -/
theorem iterate_constant {K : Type u} [Field K] (a c : K) (n : ℕ) :
    (C c).newtonMap^[n] a = a := by
  have h : Function.IsFixedPt (C c).newtonMap a := by
    rw [Function.IsFixedPt, newtonMap_apply_eq_sub_div]
    simp
  exact h.iterate n

end PolynomialRootStabilityTest.NewtonContracts
