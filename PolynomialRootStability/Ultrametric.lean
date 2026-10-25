/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial estimates in ultrametric seminormed rings

A uniform coefficient bound controls evaluation, differences of evaluations, and
first-order Taylor remainders on the norm unit ball. Differentiation preserves
the coefficient bound: natural-number multiples do not increase an ultrametric
seminorm. In particular, none of these estimates requires the norm of one to be
one, a separated norm, or completeness.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*}

section SeminormedRing

variable [SeminormedRing R] [IsUltrametricDist R] {f : R[X]} {M : ℝ} {x y : R}

/-- Differentiation preserves a uniform coefficient bound for an ultrametric seminorm. -/
theorem norm_derivative_coeff_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (n : ℕ) :
    ‖f.derivative.coeff n‖ ≤ M := by
  simpa only [coeff_derivative, nsmul_eq_mul', Nat.cast_add, Nat.cast_one] using
    (IsUltrametricDist.norm_nsmul_le (f.coeff (n + 1)) (n + 1)).trans (hf (n + 1))

/-- On the norm unit ball, evaluation is bounded by any uniform coefficient bound. -/
theorem norm_eval_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) :
    ‖f.eval x‖ ≤ M := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · simpa only [hf0, eval_zero, norm_zero, coeff_zero] using hf 0
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    rw [← divX_mul_X_add f, eval_add, eval_mul_X, eval_C]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    exact max_le
      ((norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hbound))
      (hf 0)

/-- On the norm unit ball, a polynomial is Lipschitz with any uniform coefficient bound. -/
theorem norm_eval_sub_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f.eval x - f.eval y‖ ≤ M * ‖x - y‖ := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
      simpa only [hf0, eval_zero, sub_self, norm_zero] using
        mul_nonneg hM (norm_nonneg (x - y))
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    have hid : f.eval x - f.eval y =
        (f.divX.eval x - f.divX.eval y) * x + f.divX.eval y * (x - y) := by
      conv_lhs => rw [← divX_mul_X_add f]
      simp only [eval_add, eval_mul_X, eval_C, sub_mul, mul_sub,
        sub_add_sub_cancel, add_sub_add_right_eq_sub]
    rw [hid]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hbound)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_eval_le_of_norm_coeff_le htail hy)
          (norm_nonneg _))

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R] [IsUltrametricDist R] {f : R[X]} {M : ℝ} {x y : R}

/-- The first-order Taylor remainder on the norm unit ball has a quadratic bound
with the same uniform coefficient bound, without any characteristic assumption. -/
theorem norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f.eval x - f.eval y - f.derivative.eval y * (x - y)‖ ≤ M * ‖x - y‖ ^ 2 := by
  induction f using degree_lt_wf.induction with
  | h f ih =>
    by_cases hf0 : f = 0
    · have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
      simpa only [hf0, eval_zero, sub_self, derivative_zero, zero_mul, norm_zero] using
        mul_nonneg hM (sq_nonneg ‖x - y‖)
    have htail : ∀ n : ℕ, ‖f.divX.coeff n‖ ≤ M := fun n => by
      simpa only [coeff_divX] using hf (n + 1)
    have hbound := ih f.divX (degree_divX_lt hf0) htail
    have hderiv : ‖f.divX.derivative.eval y‖ ≤ M :=
      norm_eval_le_of_norm_coeff_le (norm_derivative_coeff_le_of_norm_coeff_le htail) hy
    have hid : f.eval x - f.eval y - f.derivative.eval y * (x - y) =
        x * (f.divX.eval x - f.divX.eval y - f.divX.derivative.eval y * (x - y)) +
          f.divX.derivative.eval y * (x - y) ^ 2 := by
      conv_lhs => rw [← divX_mul_X_add f]
      simp only [eval_add, eval_mul_X, eval_C, derivative_add, derivative_mul,
        derivative_X, derivative_C, mul_one, add_zero]
      ring
    rw [hid]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hbound)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul hderiv (norm_pow_le' (x - y) (by decide : 0 < 2))
          (norm_nonneg _) ((norm_nonneg (f.coeff 0)).trans (hf 0)))

/-- An approximate derivative at an anchor controls evaluation differences on the norm unit
ball. The bound combines the quadratic Taylor remainder at `w`, the variation of the derivative
from `a` to `w`, and the error in approximating the derivative at `a` by `d`. -/
theorem norm_eval_sub_sub_mul_le_max_of_norm_coeff_le
    {g : R[X]} {eta : ℝ} {a z w d : R}
    (hg : ∀ n : ℕ, ‖g.coeff n‖ ≤ M) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hd : ‖g.derivative.eval a - d‖ ≤ eta) :
    ‖g.eval z - g.eval w - d * (z - w)‖ ≤
      max (M * ‖w - a‖) (max eta (M * ‖z - w‖)) * ‖z - w‖ := by
  have hderiv : ‖g.derivative.eval w - d‖ ≤ max (M * ‖w - a‖) eta := by
    calc
      ‖g.derivative.eval w - d‖ =
          ‖(g.derivative.eval w - g.derivative.eval a) +
            (g.derivative.eval a - d)‖ := by
              congr 1
              ring
      _ ≤ max ‖g.derivative.eval w - g.derivative.eval a‖
          ‖g.derivative.eval a - d‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (M * ‖w - a‖) eta :=
        max_le_max
          (norm_eval_sub_le_of_norm_coeff_le
            (norm_derivative_coeff_le_of_norm_coeff_le hg) hw ha) hd
  have hid : g.eval z - g.eval w - d * (z - w) =
      (g.eval z - g.eval w - g.derivative.eval w * (z - w)) +
        (g.derivative.eval w - d) * (z - w) := by ring
  rw [hid]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · calc
      ‖g.eval z - g.eval w - g.derivative.eval w * (z - w)‖ ≤
          M * ‖z - w‖ ^ 2 :=
        norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le hg hz hw
      _ = (M * ‖z - w‖) * ‖z - w‖ := by ring
      _ ≤ max (M * ‖w - a‖) (max eta (M * ‖z - w‖)) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right
          ((le_max_right eta (M * ‖z - w‖)).trans
            (le_max_right (M * ‖w - a‖) (max eta (M * ‖z - w‖))))
          (norm_nonneg _)
  · exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (hderiv.trans (max_le_max le_rfl (le_max_left eta (M * ‖z - w‖))))
        (norm_nonneg _))

end SeminormedCommRing

/-- A polynomial scales distances from a unit-ball anchor by its derivative norm
when the coefficient-controlled displacement is strictly smaller than that norm.
The receiver automatically lies in the unit ball; no root or separated norm is required. -/
theorem norm_eval_sub_eq_of_mul_norm_sub_lt_norm_derivative
    [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f : R[X]} {M : ℝ} {a b : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (ha : ‖a‖ ≤ 1)
    (hba : M * ‖b - a‖ < ‖f.derivative.eval a‖) :
    ‖f.eval b - f.eval a‖ = ‖f.derivative.eval a‖ * ‖b - a‖ := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hd : ‖f.derivative.eval a‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hf) ha
  have hdist : ‖b - a‖ < 1 :=
    lt_of_mul_lt_mul_left
      (by simpa only [mul_one] using hba.trans_le hd) hM
  have hb : ‖b‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (b - a) a).trans (max_le hdist.le ha)
  by_cases hzero : ‖b - a‖ = 0
  · have hbound := norm_eval_sub_le_of_norm_coeff_le hf hb ha
    rw [hzero, mul_zero] at hbound ⊢
    exact le_antisymm hbound (norm_nonneg _)
  · have hpos : 0 < ‖b - a‖ :=
      (lt_or_eq_of_le (norm_nonneg (b - a))).resolve_right (Ne.symm hzero)
    have hlt : M * ‖b - a‖ ^ 2 < ‖f.derivative.eval a‖ * ‖b - a‖ := by
      simpa only [pow_two, mul_assoc] using mul_lt_mul_of_pos_right hba hpos
    have hrem : ‖f.eval b - f.eval a - f.derivative.eval a * (b - a)‖ <
        ‖f.derivative.eval a * (b - a)‖ := by
      rw [norm_mul]
      exact (norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le hf hb ha).trans_lt hlt
    have hnorm := IsUltrametricDist.norm_eq_of_add_norm_lt_max
      (x := f.eval b - f.eval a) (y := -(f.derivative.eval a * (b - a)))
      (by
        simpa only [sub_eq_add_neg, norm_neg] using
          hrem.trans_le (le_max_right ‖f.eval b - f.eval a‖
            ‖f.derivative.eval a * (b - a)‖))
    simpa only [norm_neg, norm_mul] using hnorm

universe u

/-- A polynomial scales distances between two points in the same derivative ball
by the derivative norm at its unit-ball anchor. -/
theorem norm_eval_sub_eval_eq_of_mul_norm_sub_lt_norm_derivative
    {R : Type u} [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f : R[X]} {M : ℝ} {a b c : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (ha : ‖a‖ ≤ 1)
    (hb : M * ‖b - a‖ < ‖f.derivative.eval a‖)
    (hc : M * ‖c - a‖ < ‖f.derivative.eval a‖) :
    ‖f.eval c - f.eval b‖ = ‖f.derivative.eval a‖ * ‖c - b‖ := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hf' : ∀ n : ℕ, ‖f.derivative.coeff n‖ ≤ M :=
    norm_derivative_coeff_le_of_norm_coeff_le hf
  have hd : ‖f.derivative.eval a‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le hf' ha
  have hdist : ‖b - a‖ < 1 :=
    lt_of_mul_lt_mul_left
      (by simpa only [mul_one] using hb.trans_le hd) hM
  have hb_unit : ‖b‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (b - a) a).trans (max_le hdist.le ha)
  have hD : ‖f.derivative.eval b - f.derivative.eval a‖ <
      ‖f.derivative.eval a‖ :=
    (norm_eval_sub_le_of_norm_coeff_le hf' hb_unit ha).trans_lt hb
  have hDb : ‖f.derivative.eval b‖ = ‖f.derivative.eval a‖ := by
    have hnorm := IsUltrametricDist.norm_eq_of_add_norm_lt_max
      (x := f.derivative.eval b) (y := -(f.derivative.eval a))
      (by
        simpa only [sub_eq_add_neg, norm_neg] using
          hD.trans_le (le_max_right ‖f.derivative.eval b‖ ‖f.derivative.eval a‖))
    simpa only [norm_neg] using hnorm
  have hcb_le : ‖c - b‖ ≤ max ‖c - a‖ ‖b - a‖ := by
    calc
      ‖c - b‖ = ‖(c - a) + -(b - a)‖ := by
        congr 1
        ring
      _ ≤ max ‖c - a‖ ‖-(b - a)‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖c - a‖ ‖b - a‖ := by rw [norm_neg]
  have hcb : M * ‖c - b‖ < ‖f.derivative.eval a‖ := by
    refine (mul_le_mul_of_nonneg_left hcb_le hM).trans_lt ?_
    rcases le_total ‖c - a‖ ‖b - a‖ with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using hc
  have hscale := norm_eval_sub_eq_of_mul_norm_sub_lt_norm_derivative
    (a := b) (b := c) hf hb_unit (by simpa only [hDb] using hcb)
  simpa only [hDb] using hscale

end Polynomial
