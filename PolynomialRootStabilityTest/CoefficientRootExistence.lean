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
# Local root transport over the 3-adic numbers

Both root-existence statements are used on `X² - 4` and `X² - 25 / 4`.
Their returned roots are identified using uniqueness in the original ball,
and attain the independently computed positive bound `1 / 9`.
The same original polynomial also tests the zero-perturbation boundary.
-/

@[expose] public section
open Polynomial

example [Fact (Nat.Prime 3)] :
    let f : (Padic 3)[X] := X ^ 2 - C 4
    let g : (Padic 3)[X] := X ^ 2 - C (25 / 4)
    ∃ yCore yField yZero : Padic 3,
      (g.eval yCore = 0 ∧
        (1 : ℝ) * ‖yCore - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ ∧
        ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yCore‖ ≤ (1 / 9 : ℝ) ∧
        yCore = (5 / 2 : Padic 3) ∧
        ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yCore‖ = (1 / 9 : ℝ) ∧
        0 < ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yCore‖ ∧
        ∀ z : Padic 3, g.eval z = 0 →
          (1 : ℝ) * ‖z - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ → z = yCore) ∧
      (g.eval yField = 0 ∧
        (1 : ℝ) * ‖yField - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ ∧
        ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yField‖ ≤ (1 / 9 : ℝ) ∧
        yField = (5 / 2 : Padic 3) ∧
        ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yField‖ = (1 / 9 : ℝ) ∧
        0 < ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yField‖ ∧
        ∀ z : Padic 3, g.eval z = 0 →
          (1 : ℝ) * ‖z - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ → z = yField) ∧
      yCore = yField ∧
      (f.eval yZero = 0 ∧
        (1 : ℝ) * ‖yZero - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ ∧
        ‖f.derivative.eval (1 : Padic 3)‖ * ‖(-2 : Padic 3) - yZero‖ ≤ (0 : ℝ) ∧
        yZero = (-2 : Padic 3) ∧
        ∀ z : Padic 3, f.eval z = 0 →
          (1 : ℝ) * ‖z - 1‖ < ‖f.derivative.eval (1 : Padic 3)‖ → z = yZero) := by
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
  have hderiv : f.derivative.eval (1 : Padic 3) = 2 := by
    norm_num [f, derivative_pow]
  have hderivnorm : ‖f.derivative.eval (1 : Padic 3)‖ = 1 := by
    rw [hderiv, htwo]
  have hu : IsUnit (f.derivative.eval (1 : Padic 3)) := by
    rw [hderiv]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hxoffset : ‖(-2 : Padic 3) - 1‖ = (1 / 3 : ℝ) := by
    have hsub : (-2 : Padic 3) - 1 = -3 := by ring
    rw [hsub, norm_neg, hthree]
  have hxstrict : (1 : ℝ) * ‖(-2 : Padic 3) - 1‖ <
      ‖f.derivative.eval (1 : Padic 3)‖ := by
    rw [one_mul, hxoffset, hderivnorm]
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
  have hsmall : (1 : ℝ) * (1 / 9 : ℝ) <
      ‖f.derivative.eval (1 : Padic 3)‖ ^ 2 := by
    rw [hderivnorm]
    norm_num
  -- Exact positive sharpness is independent of either existence statement.
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
  have hdiffZero : ∀ n : ℕ, ‖f.coeff n - f.coeff n‖ ≤ (0 : ℝ) := by
    intro n
    simp
  have hsmallZero : (1 : ℝ) * (0 : ℝ) <
      ‖f.derivative.eval (1 : Padic 3)‖ ^ 2 := by
    rw [hderivnorm]
    norm_num
  -- Only original-polynomial and coefficient-smallness data enter these calls.
  obtain ⟨yCore, hCoreRoot, hCoreBall, hCoreBound, hCoreUnique⟩ :=
    Polynomial.exists_root_of_norm_coeff_sub_le_of_isUnit
      (f := f) (g := g) (M := (1 : ℝ)) (ε := (1 / 9 : ℝ))
      (a := (1 : Padic 3)) (x := (-2 : Padic 3))
      hf ha hx hxstrict hdiff hsmall hu
  obtain ⟨yField, hFieldRoot, hFieldBall, hFieldBound, hFieldUnique⟩ :=
    Polynomial.exists_root_of_norm_coeff_sub_le
      (f := f) (g := g) (M := (1 : ℝ)) (ε := (1 / 9 : ℝ))
      (a := (1 : Padic 3)) (x := (-2 : Padic 3))
      hf ha hx hxstrict hdiff hsmall
  -- The expected perturbed root and its ball membership are checked only now.
  have hy : g.eval (5 / 2 : Padic 3) = 0 := by norm_num [g]
  have hyoffset : ‖(5 / 2 : Padic 3) - 1‖ = (1 / 3 : ℝ) := by
    have hsub : (5 / 2 : Padic 3) - 1 = 3 / 2 := by norm_num
    rw [hsub, norm_div, hthree, htwo]
    norm_num
  have hystrict : (1 : ℝ) * ‖(5 / 2 : Padic 3) - 1‖ <
      ‖f.derivative.eval (1 : Padic 3)‖ := by
    rw [one_mul, hyoffset, hderivnorm]
    norm_num
  have hCoreExpected : yCore = (5 / 2 : Padic 3) :=
    (hCoreUnique (5 / 2 : Padic 3) hy hystrict).symm
  have hFieldExpected : yField = (5 / 2 : Padic 3) :=
    (hFieldUnique (5 / 2 : Padic 3) hy hystrict).symm
  have hSame : yCore = yField :=
    (hCoreUnique yField hFieldRoot hFieldBall).symm
  have hCoreTight : ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - yCore‖ = (1 / 9 : ℝ) := by
    simpa only [hCoreExpected] using htight
  have hCorePositive : 0 < ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - yCore‖ := by
    simpa only [hCoreExpected] using hpositive
  have hFieldTight : ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - yField‖ = (1 / 9 : ℝ) := by
    simpa only [hFieldExpected] using htight
  have hFieldPositive : 0 < ‖f.derivative.eval (1 : Padic 3)‖ *
      ‖(-2 : Padic 3) - yField‖ := by
    simpa only [hFieldExpected] using hpositive
  -- Zero perturbation needs no positive-epsilon hypothesis or extra model.
  obtain ⟨yZero, hZeroRoot, hZeroBall, hZeroBound, hZeroUnique⟩ :=
    Polynomial.exists_root_of_norm_coeff_sub_le
      (f := f) (g := f) (M := (1 : ℝ)) (ε := (0 : ℝ))
      (a := (1 : Padic 3)) (x := (-2 : Padic 3))
      hf ha hx hxstrict hdiffZero hsmallZero
  have hzeroDist : ‖(-2 : Padic 3) - yZero‖ = 0 := by
    apply le_antisymm
    · simpa only [hderivnorm, one_mul] using hZeroBound
    · exact norm_nonneg _
  have hZeroExpected : yZero = (-2 : Padic 3) :=
    (sub_eq_zero.mp (norm_eq_zero.mp hzeroDist)).symm
  exact ⟨yCore, yField, yZero,
    ⟨hCoreRoot, hCoreBall, hCoreBound, hCoreExpected, hCoreTight,
      hCorePositive, hCoreUnique⟩,
    ⟨hFieldRoot, hFieldBall, hFieldBound, hFieldExpected, hFieldTight,
      hFieldPositive, hFieldUnique⟩,
    hSame, ⟨hZeroRoot, hZeroBall, hZeroBound, hZeroExpected, hZeroUnique⟩⟩
