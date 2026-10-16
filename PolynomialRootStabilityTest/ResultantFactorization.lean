/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import PolynomialRootStability.ResultantFactorization
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Independent quantitative factorization inputs over the 5-adic field

The prescribed approximations `5X² + 2` and `5X² + 7` have degree two and
leading coefficients of norm `1 / 5`. Their resultant is `5⁴`, of norm `5⁻⁴`.
Adding `5⁹X` to their product gives a nonzero error of degree one and sup norm
`5⁻⁹`, strictly less than the square of the resultant norm. The target leading
coefficient is exactly the product of the initial leading coefficients.

The input calculations use no factorization, root or quantitative lifting statement.
The final example applies the quantitative lifting theorem to obtain factors with the
prescribed degrees, leading coefficients, integrality and correction bounds. Norms less
than one certify nonunits in the valuation integer ring, not in the field. The separate
mathematical no-root argument for the target is not formalized here.

The calculations reuse Mathlib's canonical `Polynomial.supNorm`, its fixed-size
resultant addition and constant formulas, and its standard complete ultrametric
normed field `ℚ_[5]`. In particular, reduction of these quadratics modulo five
drops their degrees; the field resultant calculation retains both sizes two.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter II, §1, Proposition 1.1 motivates these nonmonic,
  nonunit-resultant quantitative lifting inputs.
* Mathlib's polynomial resultant API supplies the fixed-size addition and constant
  formulas; its polynomial sup norm is the maximum of coefficient norms.
-/

-- This test module intentionally exports no public mathematical API.
set_option linter.privateModule false

@[expose] public section

namespace Polynomial

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private noncomputable def g₀ : ℚ_[5][X] := C 5 * X ^ 2 + C 2
private noncomputable def h₀ : ℚ_[5][X] := C 5 * X ^ 2 + C 7
private noncomputable def f : ℚ_[5][X] := g₀ * h₀ + C (5 ^ 9) * X

private theorem g₀_natDegree : g₀.natDegree = 2 := by
  rw [g₀, natDegree_add_C, natDegree_C_mul_X_pow _ _ (by norm_num)]

private theorem h₀_natDegree : h₀.natDegree = 2 := by
  rw [h₀, natDegree_add_C, natDegree_C_mul_X_pow _ _ (by norm_num)]

private theorem g₀_leadingCoeff : g₀.leadingCoeff = 5 := by
  rw [leadingCoeff, g₀_natDegree]
  norm_num [g₀]

private theorem h₀_leadingCoeff : h₀.leadingCoeff = 5 := by
  rw [leadingCoeff, h₀_natDegree]
  norm_num [h₀]

private theorem residual_eq : f - g₀ * h₀ = C (5 ^ 9) * X := by
  simp [f]

private theorem residual_degree : (f - g₀ * h₀).degree = 1 := by
  rw [residual_eq, degree_C_mul_X (by norm_num)]

private theorem residual_natDegree : (f - g₀ * h₀).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some residual_degree

private theorem residual_ne_zero : f - g₀ * h₀ ≠ 0 := by
  intro hz
  simpa [hz] using residual_degree

private theorem f_expansion :
    f = C 25 * X ^ 4 + C 45 * X ^ 2 + C (5 ^ 9) * X + C 14 := by
  dsimp [f, g₀, h₀]
  simp only [map_ofNat]
  ring

private theorem f_natDegree : f.natDegree = 4 := by
  have hprod : (g₀ * h₀).natDegree = 4 := by
    rw [natDegree_mul' (by rw [g₀_leadingCoeff, h₀_leadingCoeff]; norm_num),
      g₀_natDegree, h₀_natDegree]
  have herror : (C (5 ^ 9) * X : ℚ_[5][X]).natDegree = 1 := by
    exact natDegree_C_mul_X _ (by norm_num)
  rw [f, natDegree_add_eq_left_of_natDegree_lt (by rw [herror, hprod]; decide), hprod]

private theorem f_leadingCoeff : f.leadingCoeff = 25 := by
  rw [leadingCoeff, f_natDegree, f_expansion]
  norm_num

private theorem leadingCoeff_exact : f.leadingCoeff = g₀.leadingCoeff * h₀.leadingCoeff := by
  rw [f_leadingCoeff, g₀_leadingCoeff, h₀_leadingCoeff]
  norm_num

private theorem residual_degree_lt :
    (f - g₀ * h₀).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
  rw [residual_degree, g₀_natDegree, h₀_natDegree]
  norm_num

private theorem g₀_supNorm_le_one : g₀.supNorm ≤ 1 := by
  obtain ⟨n, hn⟩ := g₀.exists_eq_supNorm
  rw [hn]
  by_cases h2 : n = 2
  · subst n
    simpa [g₀] using Padic.norm_int_le_one (p := 5) 5
  by_cases h0 : n = 0
  · subst n
    simpa [g₀] using Padic.norm_int_le_one (p := 5) 2
  · simp [g₀, coeff_X_pow, coeff_C, h2, h0]

private theorem h₀_supNorm_le_one : h₀.supNorm ≤ 1 := by
  obtain ⟨n, hn⟩ := h₀.exists_eq_supNorm
  rw [hn]
  by_cases h2 : n = 2
  · subst n
    simpa [h₀] using Padic.norm_int_le_one (p := 5) 5
  by_cases h0 : n = 0
  · subst n
    simpa [h₀] using Padic.norm_int_le_one (p := 5) 7
  · simp [h₀, coeff_X_pow, coeff_C, h2, h0]

private theorem resultant_eq : g₀.resultant h₀ = 5 ^ 4 := by
  have hh : h₀ = C 5 + g₀ * 1 := by
    dsimp [g₀, h₀]
    simp only [map_ofNat]
    ring
  change g₀.resultant h₀ g₀.natDegree h₀.natDegree = _
  rw [g₀_natDegree, h₀_natDegree, hh,
    resultant_add_mul_right _ _ _ _ _ (by simp) (by rw [g₀_natDegree]),
    resultant_C_right]
  norm_num [g₀]

private theorem norm_five : ‖(5 : ℚ_[5])‖ = (1 / 5 : ℝ) := by
  simpa using Padic.norm_p (p := 5)

private theorem resultant_norm : ‖g₀.resultant h₀‖ = (1 / 5 : ℝ) ^ 4 := by
  rw [resultant_eq, norm_pow, norm_five]

private theorem residual_supNorm : (f - g₀ * h₀).supNorm = (1 / 5 : ℝ) ^ 9 := by
  rw [residual_eq, ← pow_one (X : ℚ_[5][X]), C_mul_X_pow_eq_monomial,
    supNorm_monomial, norm_pow, norm_five]

private theorem residual_supNorm_lt_resultant_sq :
    (f - g₀ * h₀).supNorm < ‖g₀.resultant h₀‖ ^ 2 := by
  rw [residual_supNorm, resultant_norm]
  norm_num

private theorem correction_bound_value :
    (f - g₀ * h₀).supNorm / ‖g₀.resultant h₀‖ = (1 / 5 : ℝ) ^ 5 := by
  rw [residual_supNorm, resultant_norm]
  norm_num

private theorem leadingCoeff_norms :
    ‖g₀.leadingCoeff‖ = (1 / 5 : ℝ) ∧ ‖h₀.leadingCoeff‖ = (1 / 5 : ℝ) ∧
      ‖g₀.leadingCoeff‖ < 1 ∧ ‖h₀.leadingCoeff‖ < 1 := by
  rw [g₀_leadingCoeff, h₀_leadingCoeff, norm_five]
  norm_num

private theorem resultant_norm_lt_one : ‖g₀.resultant h₀‖ < 1 := by
  rw [resultant_norm]
  norm_num

/-- The four quantitative lifting inputs, proved without a lifting theorem. -/
private theorem quadratic_padic_five_inputs :
    g₀.supNorm ≤ 1 ∧ h₀.supNorm ≤ 1 ∧
      (f - g₀ * h₀).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) ∧
      (f - g₀ * h₀).supNorm < ‖g₀.resultant h₀‖ ^ 2 :=
  ⟨g₀_supNorm_le_one, h₀_supNorm_le_one, residual_degree_lt,
    residual_supNorm_lt_resultant_sq⟩

/-- Zero error has degree bottom, including the strict bound by zero. -/
private theorem zero_error_boundary :
    (0 : ℚ_[5][X]).degree < (0 : WithBot ℕ) ∧
      (g₀ * h₀ - g₀ * h₀).supNorm < ‖g₀.resultant h₀‖ ^ 2 := by
  rw [resultant_norm]
  norm_num

/-- Small constant error passes the norm test but fails the degree test at size zero. -/
private theorem constant_degree_boundary :
    let a : ℚ_[5][X] := C 5
    let F : ℚ_[5][X] := C 30
    F - a * a = C 5 ∧ a.resultant a = 1 ∧
      (F - a * a).supNorm < ‖a.resultant a‖ ^ 2 ∧
      ¬ (F - a * a).degree < ((a.natDegree + a.natDegree : ℕ) : WithBot ℕ) := by
  have he : (C 30 - C 5 * C 5 : ℚ_[5][X]) = C 5 := by
    norm_num [← C_mul, ← C_sub]
  have hr : (C 5 : ℚ_[5][X]).resultant (C 5) = 1 := by
    norm_num
  change _ ∧ _ ∧ _ ∧ _
  rw [he, hr]
  norm_num [norm_five]

/-- Quantitative factorization of the independently checked nonmonic inputs. -/
private theorem quadratic_padic_five_factorization :
    ∃ g h : ℚ_[5][X],
      f = g * h ∧ g.degree = 2 ∧ h.degree = 2 ∧
      g.leadingCoeff = 5 ∧ h.leadingCoeff = 5 ∧
      (g - g₀).degree < 2 ∧ (h - h₀).degree < 2 ∧
      g.supNorm ≤ 1 ∧ h.supNorm ≤ 1 ∧
      (g - g₀).supNorm ≤ (1 / 5 : ℝ) ^ 5 ∧
      (h - h₀).supNorm ≤ (1 / 5 : ℝ) ^ 5 := by
  obtain ⟨hg₀, hh₀, hdegree, hclose⟩ := quadratic_padic_five_inputs
  obtain ⟨g, h, hfactor, hgd, hhd, hgl, hhl, hgc, hhc, hgb, hhb, hge, hhe⟩ :=
    exists_factorization_of_supNorm_lt_resultant_sq f g₀ h₀ hg₀ hh₀ hdegree hclose
  have hg₀_ne : g₀ ≠ 0 := by
    intro hz
    have hn := g₀_natDegree
    simp [hz] at hn
  have hh₀_ne : h₀ ≠ 0 := by
    intro hz
    have hn := h₀_natDegree
    simp [hz] at hn
  refine ⟨g, h, hfactor, ?_, ?_, ?_, ?_, ?_, ?_, hgb, hhb, ?_, ?_⟩
  · rw [hgd, degree_eq_natDegree hg₀_ne, g₀_natDegree]
    norm_num
  · rw [hhd, degree_eq_natDegree hh₀_ne, h₀_natDegree]
    norm_num
  · simpa [g₀_leadingCoeff] using hgl
  · simpa [h₀_leadingCoeff] using hhl
  · simpa [g₀_natDegree] using hgc
  · simpa [h₀_natDegree] using hhc
  · simpa [correction_bound_value] using hge
  · simpa [correction_bound_value] using hhe

end Polynomial
