/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Aggregate-root and ordinary/normalized coefficient clients

The concrete 2-adic cases use the same base and ambient field and so do not
test a nontrivial field extension. The generic client separately uses
independent base/ambient universes; its `IsKrasner` and splitting assumptions
remain explicit. In particular, concrete constant polynomials test the empty
root-set boundary, not a nontrivial generated field.
-/

public section

open Polynomial

noncomputable section

namespace PolynomialRootStabilityTest

universe u v

variable {K : Type u} {L : Type v}
  [NormedField K] [NormedField L] [NormedAlgebra K L] [IsKrasner K L]

/-- Generic same-degree ordinary-coefficient stability, without monicity. -/
theorem aggregate_ordinary_stability {f : K[X]}
    (hf0 : f ≠ 0) (hfsep : f.Separable)
    (hfsplit : (f.map (algebraMap K L)).Splits) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : K[X]},
      g.natDegree = f.natDegree →
      (∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) →
      (g.map (algebraMap K L)).Splits →
      g.Separable ∧
        IntermediateField.adjoin K (f.rootSet L) =
          IntermediateField.adjoin K (g.rootSet L) :=
  IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable hf0 hfsep hfsplit

/-- Generic normalized-coefficient neighbourhood, with the comparison
polynomial's nonzeroness and equal degree stated separately. -/
theorem aggregate_normalized_stability {f : K[X]}
    (hf0 : f ≠ 0) (hfsep : f.Separable)
    (hfsplit : (f.map (algebraMap K L)).Splits) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : K[X]},
      g ≠ 0 → g.natDegree = f.natDegree →
      (∀ i : ℕ,
        ‖(g * C g.leadingCoeff⁻¹).coeff i -
          (f * C f.leadingCoeff⁻¹).coeff i‖ < ε) →
      (g.map (algebraMap K L)).Splits →
      g.Separable ∧
        IntermediateField.adjoin K (f.rootSet L) =
          IntermediateField.adjoin K (g.rootSet L) :=
  IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable_normalized hf0 hfsep hfsplit

/-- A nonzero scalar leaves the monic normalization unchanged. This concrete
use of the normalized stability neighbourhood proves separability and the
root-field equality for `f * C c` without assuming either conclusion. -/
theorem aggregate_scalar_normalized_invariance {f : K[X]}
    (hf0 : f ≠ 0) (hfsep : f.Separable)
    (hfsplit : (f.map (algebraMap K L)).Splits) (c : K) (hc : c ≠ 0) :
    (f * C c).Separable ∧
      IntermediateField.adjoin K (f.rootSet L) =
        IntermediateField.adjoin K ((f * C c).rootSet L) := by
  obtain ⟨ε, hε, hstable⟩ :=
    IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable_normalized hf0 hfsep hfsplit
  have hnorm : (f * C c) * C (f * C c).leadingCoeff⁻¹ =
      f * C f.leadingCoeff⁻¹ := by
    rw [leadingCoeff_mul_C_of_isUnit (isUnit_iff_ne_zero.mpr hc) f, mul_assoc, ← C_mul]
    congr 1
    field_simp [leadingCoeff_ne_zero.mpr hf0, hc]
  apply hstable (mul_ne_zero hf0 (C_ne_zero.mpr hc)) (natDegree_mul_C hc)
  · intro i
    rw [hnorm, sub_self, norm_zero]
    exact hε
  · simpa [Polynomial.map_mul, Polynomial.map_C] using
      hfsplit.mul (Splits.C (algebraMap K L c))

/-- Rational normalization for a nonzero constant and positive requested
normalized radius; the conclusion derives comparison nonzeroness. -/
theorem rational_constant_normalization :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : ℚ[X]},
      g.natDegree = (C (2 : ℚ)).natDegree →
      (∀ i : ℕ, ‖g.coeff i - (C (2 : ℚ)).coeff i‖ < ε) →
      g ≠ 0 ∧ ∀ i : ℕ,
        ‖(g * C g.leadingCoeff⁻¹).coeff i -
          (C (2 : ℚ) * C (C (2 : ℚ)).leadingCoeff⁻¹).coeff i‖ < 1 :=
  Polynomial.exists_pos_norm_mul_leadingCoeff_inv_coeff_sub_lt
    (f := C (2 : ℚ)) (η := 1) (by norm_num) (by norm_num)

/-- The 2-adic constant reference has no roots, yet its ordinary-coefficient
neighbourhood still forces comparison separability and root-field equality. -/
theorem padic_constant_stability :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : ℚ_[2][X]},
      g.natDegree = (C (2 : ℚ_[2])).natDegree →
      (∀ i : ℕ, ‖g.coeff i - (C (2 : ℚ_[2])).coeff i‖ < ε) →
      (g.map (algebraMap ℚ_[2] ℚ_[2])).Splits →
      g.Separable ∧
        IntermediateField.adjoin ℚ_[2] ((C (2 : ℚ_[2])).rootSet ℚ_[2]) =
          IntermediateField.adjoin ℚ_[2] (g.rootSet ℚ_[2]) := by
  apply IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable
  · norm_num
  · exact (separable_C 2).mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  · simp

/-- Explicitly identifies the empty-root-set boundary in the preceding
2-adic constant client, rather than treating it as a nontrivial extension. -/
theorem padic_constant_rootSet_empty :
    (C (2 : ℚ_[2])).rootSet ℚ_[2] = ∅ := by
  simp

/-- Nonmonic degree-one reference `2 * (X - 3)` over the 2-adics. -/
theorem padic_nonmonic_linear_stability :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : ℚ_[2][X]},
      g.natDegree = (C (2 : ℚ_[2]) * (X - C 3)).natDegree →
      (∀ i : ℕ,
        ‖g.coeff i - (C (2 : ℚ_[2]) * (X - C 3)).coeff i‖ < ε) →
      (g.map (algebraMap ℚ_[2] ℚ_[2])).Splits →
      g.Separable ∧
        IntermediateField.adjoin ℚ_[2]
            ((C (2 : ℚ_[2]) * (X - C 3)).rootSet ℚ_[2]) =
          IntermediateField.adjoin ℚ_[2] (g.rootSet ℚ_[2]) := by
  apply IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable
  · exact mul_ne_zero (by norm_num) (X_sub_C_ne_zero 3)
  · exact Separable.unit_mul
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))) separable_X_sub_C
  · simpa [sub_eq_add_neg] using
      (Polynomial.Splits.X_add_C (-3 : ℚ_[2])).C_mul (2 : ℚ_[2])

end PolynomialRootStabilityTest
