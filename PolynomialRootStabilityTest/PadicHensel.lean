/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Newton
public import PolynomialRootStability.Ultrametric
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Tactic.NormNum

/-!
# Recovering p-adic Hensel lifting from Newton lifting over a field

Mapping coefficients along `R →+* ℤ_[p] →+* ℚ_[p]` allows the complete-field Newton
theorem to handle any commutative semiring of coefficients. Its integral root belongs
to `ℤ_[p]`, and the isometric inclusion transfers the quantitative conclusions and
uniqueness. The lifting application retains the entire conclusion of Mathlib's
`hensels_lemma`, without using a p-adic root-existence theorem. The polynomial
Lipschitz estimate also recovers Mathlib's `padic_polynomial_dist` from the
coefficient-controlled ultrametric estimate.

The quadratic `X² - 1` over `ℚ_[2]` shows why uniqueness is stated in an open ball:
its second root lies exactly on the boundary, even though the strict approximate-root
hypothesis holds.

## Implementation notes

The private lifting client checks the full commutative-semiring coefficient
interface without adding a duplicate public Hensel theorem. The coercion
calculation, Lipschitz estimate and quadratic boundary calculation are independent
of the root-existence argument.

## References

* Mathlib's `hensels_lemma` and `padic_polynomial_dist`, formalized by Robert Y.
  Lewis following Keith Conrad's exposition of Hensel's lemma, supply the p-adic
  interfaces recovered here.
* Mathlib's `PadicInt.Coe.ringHom`, `Polynomial.hom_eval₂` and `Padic.norm_p` supply
  the coefficient transport and the boundary norm calculation.
-/

@[expose] public section

namespace Polynomial

universe u

private theorem norm_coeff_map_padicInt_le_one {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommSemiring R] (φ : R →+* ℤ_[p]) (f : R[X]) (n : ℕ) :
    ‖(f.map (PadicInt.Coe.ringHom.comp φ)).coeff n‖ ≤ 1 := by
  rw [coeff_map]
  exact PadicInt.norm_le_one (φ (f.coeff n))

private theorem eval_map_padicInt_coe {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommSemiring R] (φ : R →+* ℤ_[p]) (f : R[X]) (a : ℤ_[p]) :
    (f.map (PadicInt.Coe.ringHom.comp φ)).eval (a : ℚ_[p]) =
      (↑(f.eval₂ φ a) : ℚ_[p]) := by
  rw [eval_map]
  exact (hom_eval₂ f φ PadicInt.Coe.ringHom a).symm

private theorem norm_aeval_sub_padicInt_le {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommSemiring R] [Algebra R ℤ_[p]] (f : R[X]) (x y : ℤ_[p]) :
    ‖f.aeval x - f.aeval y‖ ≤ ‖x - y‖ := by
  have hcoeff (n : ℕ) : ‖(f.map (algebraMap R ℤ_[p])).coeff n‖ ≤ 1 := by
    rw [coeff_map]
    exact PadicInt.norm_le_one _
  simpa only [eval_map_algebraMap, one_mul] using
    norm_eval_sub_le_of_norm_coeff_le hcoeff (PadicInt.norm_le_one x) (PadicInt.norm_le_one y)

/-- The complete p-adic Hensel interface in algebra-evaluation notation, recovered
from the complete-field Newton theorem: a root, strict distance bound, derivative-norm
stability, and uniqueness. This has the hypotheses and conclusion of Mathlib's
`hensels_lemma`, including arbitrary commutative semiring coefficients. -/
private theorem exists_padicInt_root_of_aeval_norm_lt {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommSemiring R] [Algebra R ℤ_[p]] {f : R[X]} {a : ℤ_[p]}
    (hclose : ‖f.aeval a‖ < ‖f.derivative.aeval a‖ ^ 2) :
    ∃ z : ℤ_[p], f.aeval z = 0 ∧
      ‖z - a‖ < ‖f.derivative.aeval a‖ ∧
      ‖f.derivative.aeval z‖ = ‖f.derivative.aeval a‖ ∧
      ∀ z', f.aeval z' = 0 → ‖z' - a‖ < ‖f.derivative.aeval a‖ → z' = z := by
  let φ : R →+* ℤ_[p] := algebraMap R ℤ_[p]
  let F : ℚ_[p][X] := f.map (PadicInt.Coe.ringHom.comp φ)
  have hcoeff (n : ℕ) : ‖F.coeff n‖ ≤ 1 := norm_coeff_map_padicInt_le_one φ f n
  have hstart : ‖(a : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one a
  have heval (x : ℤ_[p]) : F.eval (x : ℚ_[p]) = (↑(f.aeval x) : ℚ_[p]) :=
    eval_map_padicInt_coe φ f x
  have hderiv (x : ℤ_[p]) :
      F.derivative.eval (x : ℚ_[p]) = (↑(f.derivative.aeval x) : ℚ_[p]) := by
    simpa only [F, derivative_map, φ, aeval_def] using
      eval_map_padicInt_coe φ f.derivative x
  have hcloseF : ‖F.eval (a : ℚ_[p])‖ < ‖F.derivative.eval (a : ℚ_[p])‖ ^ 2 := by
    simpa only [heval, hderiv, PadicInt.padic_norm_e_of_padicInt] using hclose
  obtain ⟨x, hx, hxint, _, hdist_lt, hderiv_eq, _, _, huniq⟩ :=
    exists_root_tendsto_iterate_newtonMap hcoeff hstart hcloseF
  let z : ℤ_[p] := ⟨x, hxint⟩
  have hz : (z : ℚ_[p]) = x := rfl
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · apply PadicInt.coe_eq_zero.mp
    rw [← heval, hz]
    exact hx
  · simpa only [← hz, hderiv, ← PadicInt.coe_sub,
      PadicInt.padic_norm_e_of_padicInt] using hdist_lt
  · simpa only [← hz, hderiv, PadicInt.padic_norm_e_of_padicInt] using hderiv_eq
  · intro z' hroot hball
    apply PadicInt.ext
    rw [hz]
    apply huniq (z' : ℚ_[p])
    · rw [heval, hroot, PadicInt.coe_zero]
    · simpa only [hderiv, ← PadicInt.coe_sub,
        PadicInt.padic_norm_e_of_padicInt] using hball

end Polynomial

namespace PolynomialRootStabilityTest.PadicHensel

open Polynomial

/-- For `X² - 1` at `1` over `ℚ_[2]`, all coefficients and the start are integral
and the strict error inequality holds, but the distinct root `-1` is at distance
exactly the derivative norm `1 / 2`. Thus the open uniqueness ball in quantitative
Newton lifting cannot be replaced by its closed ball. -/
theorem sq_sub_one_padic_two_boundary :
    let f : ℚ_[2][X] := X ^ 2 - C 1
    (∀ n, ‖f.coeff n‖ ≤ 1) ∧ ‖(1 : ℚ_[2])‖ ≤ 1 ∧
      f.eval 1 = 0 ∧ f.eval (-1) = 0 ∧ (-1 : ℚ_[2]) ≠ 1 ∧
      ‖f.eval 1‖ < ‖f.derivative.eval 1‖ ^ 2 ∧
      ‖f.derivative.eval 1‖ = (1 / 2 : ℝ) ∧
      ‖(-1 : ℚ_[2]) - 1‖ = ‖f.derivative.eval 1‖ := by
  let f : ℚ_[2][X] := X ^ 2 - C 1
  have hderiv : f.derivative.eval 1 = (2 : ℚ_[2]) := by norm_num [f]
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  have hderiv_norm : ‖f.derivative.eval 1‖ = (1 / 2 : ℝ) := by rw [hderiv, htwo]
  refine ⟨?_, by simp, by norm_num [f], by norm_num [f], by norm_num, ?_,
    hderiv_norm, ?_⟩
  · intro n
    by_cases h2 : n = 2
    · simp [h2, coeff_one]
    by_cases h0 : n = 0
    · simp [h0]
    · simp [coeff_X_pow, coeff_one, h2, h0]
  · rw [hderiv_norm]
    norm_num [f]
  · have hsub : (-1 : ℚ_[2]) - 1 = -(2 : ℚ_[2]) := by norm_num
    rw [hsub, norm_neg, hderiv, htwo]

end PolynomialRootStabilityTest.PadicHensel
