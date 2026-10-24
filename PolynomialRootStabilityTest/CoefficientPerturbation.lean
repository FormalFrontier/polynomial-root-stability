/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import PolynomialRootStability.CoefficientPerturbation

/-!
# A sharp coefficient-perturbation bound over the 3-adic numbers

The roots `-2` of `X² - 4` and `5 / 2` of `X² - 25 / 4` lie in the original
strict derivative ball about `1`. Their scaled distance equals the positive
coefficient perturbation bound `1 / 9`.
-/

@[expose] public section
open Polynomial

example [Fact (Nat.Prime 3)] :
    let f : (Padic 3)[X] := X ^ 2 - C 4
    (‖f.derivative.eval (1 : Padic 3)‖ *
        ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ ≤ (1 / 9 : ℝ)) ∧
    (‖f.derivative.eval (1 : Padic 3)‖ *
        ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ = (1 / 9 : ℝ)) ∧
    0 < ‖f.derivative.eval (1 : Padic 3)‖ *
        ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ := by
  let f : (Padic 3)[X] := X ^ 2 - C 4
  let g : (Padic 3)[X] := X ^ 2 - C (25 / 4)
  have htwo : ‖(2 : Padic 3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 2)).2 (by decide)
  have hfour : ‖(4 : Padic 3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 4)).2 (by decide)
  have hthree : ‖(3 : Padic 3)‖ = (1 / 3 : ℝ) := by
    simpa only [Nat.cast_ofNat, one_div] using (Padic.norm_p (p := 3))
  have hnine : ‖(9 : Padic 3)‖ = (1 / 9 : ℝ) := by
    have hmul : (9 : Padic 3) = 3 * 3 := by norm_num
    rw [hmul, norm_mul]
    norm_num [hthree]
  have h94 : ‖(9 / 4 : Padic 3)‖ = (1 / 9 : ℝ) := by
    rw [norm_div, hnine, hfour]
    norm_num
  have hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ (1 : ℝ) := by
    intro n
    by_cases h0 : n = 0
    · subst n
      simp [f, coeff_X_pow, hfour]
    by_cases h2 : n = 2
    · subst n
      simp [f, coeff_X_pow]
    · simp [f, coeff_X_pow, coeff_C, h0, h2]
  have ha : ‖(1 : Padic 3)‖ ≤ (1 : ℝ) := by simp
  have hx : f.eval (-2 : Padic 3) = 0 := by norm_num [f]
  have hy : g.eval (5 / 2 : Padic 3) = 0 := by norm_num [g]
  have hderiv : f.derivative.eval (1 : Padic 3) = 2 := by
    norm_num [f, derivative_pow]
  have hderivnorm : ‖f.derivative.eval (1 : Padic 3)‖ = 1 := by
    rw [hderiv, htwo]
  have hxoffset : ‖(-2 : Padic 3) - 1‖ = (1 / 3 : ℝ) := by
    have hsub : (-2 : Padic 3) - 1 = -3 := by ring
    rw [hsub, norm_neg, hthree]
  have hyoffset : ‖(5 / 2 : Padic 3) - 1‖ = (1 / 3 : ℝ) := by
    have hsub : (5 / 2 : Padic 3) - 1 = 3 / 2 := by norm_num
    rw [hsub, norm_div, hthree, htwo]
    norm_num
  have hxstrict : (1 : ℝ) * ‖(-2 : Padic 3) - 1‖ <
      ‖f.derivative.eval (1 : Padic 3)‖ := by
    rw [one_mul, hxoffset, hderivnorm]
    norm_num
  have hystrict : (1 : ℝ) * ‖(5 / 2 : Padic 3) - 1‖ <
      ‖f.derivative.eval (1 : Padic 3)‖ := by
    rw [one_mul, hyoffset, hderivnorm]
    norm_num
  have hdiff : ∀ n : ℕ,
      ‖f.coeff n - g.coeff n‖ ≤ (1 / 9 : ℝ) := by
    intro n
    by_cases h0 : n = 0
    · subst n
      have hc0 : f.coeff 0 - g.coeff 0 = (9 / 4 : Padic 3) := by
        norm_num [f, g, coeff_X_pow]
      simpa only [hc0] using (le_of_eq h94)
    · have hcn : f.coeff n - g.coeff n = 0 := by
        simp [f, g, coeff_sub, coeff_C, h0]
      rw [hcn, norm_zero]
      norm_num
  -- Compute exact positive sharpness independently of the perturbation bound.
  have hdist : ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ = (1 / 9 : ℝ) := by
    have hsub : (-2 : Padic 3) - (5 / 2 : Padic 3) = -(9 / 2 : Padic 3) := by
      norm_num
    rw [hsub, norm_neg, norm_div, hnine, htwo]
    norm_num
  have htight : ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ = (1 / 9 : ℝ) := by
    rw [hderivnorm, hdist, one_mul]
  have hpositive : 0 < ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ := by
    rw [htight]
    norm_num
  -- Apply the perturbation bound to the independently checked inputs.
  have hbound : ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - (5 / 2 : Padic 3)‖ ≤ (1 / 9 : ℝ) :=
    Polynomial.norm_derivative_eval_mul_norm_sub_le_of_norm_coeff_sub_le
      (f := f) (g := g) (M := (1 : ℝ)) (ε := (1 / 9 : ℝ))
      (a := (1 : Padic 3)) (x := (-2 : Padic 3)) (y := (5 / 2 : Padic 3))
      hf ha hx hy hxstrict hystrict hdiff
  exact ⟨hbound, htight, hpositive⟩
