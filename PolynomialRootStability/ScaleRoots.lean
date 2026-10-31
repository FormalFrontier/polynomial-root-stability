/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Continuity and nonvanishing of polynomial root scaling

For a fixed polynomial over a topological semiring, evaluation of Mathlib's
`Polynomial.scaleRoots` is jointly continuous in the scaling and value parameters.
Over a normed field, a polynomial with no zero of norm at least one remains
nonzero after root scaling at every nonzero value whose norm is at least the
scaling parameter's norm.

## Implementation notes

The continuity proof uses the fixed polynomial's coefficient and degree API,
without commuting any factors. The nonvanishing proof uses Mathlib's evaluation
identity when the parameter is nonzero, and its leading-monomial identity at
zero. No new polynomial family is defined. These are scaling prerequisites
motivated by the reference below, not an exterior homotopy or a root-count theorem.

## References

* Mathlib's `Mathlib.RingTheory.Polynomial.ScaleRoots`, by Anne Baanen and Devon
  Tuma, supplies the root-scaling operation and its algebraic identities.
* Mathlib's `Mathlib.Topology.Algebra.Polynomial`, by Robert Y. Lewis, supplies
  polynomial evaluation and topology support.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §7, proof of the
  fundamental theorem of algebra, printed p. 11 / PDF p. 19, motivates polynomial
  root scaling on the unit boundary.
-/

@[expose] public section

universe u

namespace Polynomial

/-- For a fixed polynomial over a possibly noncommutative topological semiring,
root-scaled evaluation is jointly continuous in the scaling and value parameters.
The polynomial is fixed; no continuity across changes of degree is asserted. -/
theorem continuous_eval_scaleRoots
    {R : Type u} [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (p : Polynomial R) :
    Continuous (fun tz : R × R => (p.scaleRoots tz.1).eval tz.2) := by
  simp_rw [eval_eq_sum_range, natDegree_scaleRoots, coeff_scaleRoots]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_fst.pow _)).mul (continuous_snd.pow _)

/-- If a polynomial has no zero of norm at least one, its root-scaled evaluation
is nonzero whenever the value is nonzero and its norm is at least the scaling
parameter's norm. This includes the zero parameter and constant polynomials,
and generalizes the unit-boundary case without completeness or a nontrivial norm. -/
theorem scaleRoots_eval_ne_zero_of_norm_le
    {K : Type u} [NormedField K] (p : Polynomial K)
    (hOutside : ∀ w : K, 1 ≤ ‖w‖ → p.eval w ≠ 0)
    {t z : K} (htz : ‖t‖ ≤ ‖z‖) (hz : z ≠ 0) :
    (p.scaleRoots t).eval z ≠ 0 := by
  have hp : p ≠ 0 := by
    intro hp
    simpa [hp] using hOutside 1 (by simp)
  by_cases ht : t = 0
  · subst t
    rw [scaleRoots_zero, eval_smul, eval_X_pow, smul_eq_mul]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ hz)
  · have hquot : 1 ≤ ‖z / t‖ := by
      rw [norm_div]
      exact (one_le_div (norm_pos_iff.mpr ht)).mpr htz
    have heval := scaleRoots_eval_mul p (z / t) t
    rw [mul_div_cancel₀ z ht] at heval
    rw [heval]
    exact mul_ne_zero (pow_ne_zero _ ht) (hOutside _ hquot)

end Polynomial
