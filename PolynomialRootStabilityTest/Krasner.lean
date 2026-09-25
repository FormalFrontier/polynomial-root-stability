/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Krasner

/-!
# Direct Krasner-module clients

These named clients check that the direct public import supplies the generic
monic theorem and finite separation without unnecessarily requiring Krasner's
axiom for the latter. The independent universes do not force a same-type
base and ambient field.
-/

public section

open Polynomial

noncomputable section

namespace PolynomialRootStabilityTest

universe u v

/-- Uniform separation of distinct roots needs only a field, its normed
ambient extension, and an algebra structure, not `IsKrasner`. -/
theorem direct_distinct_root_separation
    {K : Type u} {L : Type v}
    [Field K] [NormedField L] [Algebra K L] (f : K[X]) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ f.rootSet L, ∀ x' ∈ f.rootSet L,
        x ≠ x' → δ ≤ ‖x - x'‖ :=
  IsKrasner.exists_pos_le_norm_sub_of_distinct_roots f

/-- Direct-import use of the generic monic root-field stability theorem. -/
theorem direct_monic_stability
    {K : Type u} {L : Type v}
    [NormedField K] [NormedField L] [NormedAlgebra K L] [IsKrasner K L]
    {f : K[X]} (hfm : f.Monic) (hfsep : f.Separable)
    (hfsplit : (f.map (algebraMap K L)).Splits) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g : K[X]},
      g.Monic → g.natDegree = f.natDegree →
      (∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) →
      (g.map (algebraMap K L)).Splits →
      g.Separable ∧
        IntermediateField.adjoin K (f.rootSet L) =
          IntermediateField.adjoin K (g.rootSet L) :=
  IsKrasner.exists_pos_adjoin_rootSet_eq_of_monic_separable hfm hfsep hfsplit

end PolynomialRootStabilityTest
