/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Polynomial stability in valuation balls

Let `v : Valuation R Γ₀` take values in a linearly ordered commutative monoid with zero.
If the positive-index coefficients of a polynomial `f` have value at most `M` and
`v a ≤ 1`, then evaluation scales displacement in the strict derivative ball
`M * v (b - a) < v (f.derivative.eval a)` by the value of the derivative at `a`.
The derivative has constant value throughout this ball, and the same scaling
identity holds between any two points of the ball.

The constant coefficient is unrestricted. The value identities need neither
separation nor a field, Henselianity, completeness, or inverses in the value monoid.
A displacement of value zero need not be zero in the ring; only the injectivity
conclusion assumes that the support of the valuation is zero.

## Main results

* `Valuation.map_eval_le_of_coeff_le`: a weak evaluation bound on the unit ball.
* `Valuation.map_eval_sub_le_of_coeff_pos_le`: a difference bound using only
  positive-index coefficients.
* `Valuation.map_eval_sub_eq_of_mul_map_sub_lt_map_derivative`: sharp scaling
  from the anchor in the strict derivative ball.
* `Valuation.map_derivative_eval_eq_of_mul_map_sub_lt_map_derivative`: derivative-value
  stability in that ball.
* `Valuation.map_eval_sub_eval_eq_of_mul_map_sub_lt_map_derivative`: sharp scaling
  between two points of the ball.
* `Valuation.injOn_eval_of_mul_map_sub_lt_map_derivative`: injectivity on the ball
  for a valuation with zero support.

The proofs use Mathlib's finite-sum valuation bounds, geometric-sum identity,
and polynomial Taylor, Hasse derivative and `divX` interfaces.

## References

* Mathlib, [`Mathlib.RingTheory.Valuation.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Valuation/Basic.lean).
* Mathlib, [`Mathlib.Algebra.Polynomial.Taylor`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Polynomial/Taylor.lean).
* Mathlib, [`Mathlib.Algebra.Ring.GeomSum`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Ring/GeomSum.lean).

These existing APIs retain their Mathlib credit; the polynomial estimates here
are a collective formalization by Formal Frontier Agents.
-/

@[expose] public section

universe u w

open Polynomial

namespace Valuation

variable {R : Type u} [CommRing R]
variable {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
variable (v : Valuation R Γ₀) {f : R[X]} {M : Γ₀} {a b c : R}

/-- Evaluation in the valuation unit ball preserves a common bound on all coefficients. -/
theorem map_eval_le_of_coeff_le
    (hf : ∀ n : ℕ, v (f.coeff n) ≤ M) (ha : v a ≤ 1) :
    v (f.eval a) ≤ M := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply v.map_sum_le
  intro n _
  rw [v.map_mul, v.map_pow]
  calc
    v (f.coeff n) * v a ^ n ≤ M * 1 :=
      mul_le_mul' (hf n) (pow_le_one₀ zero_le ha)
    _ = M := mul_one _

private theorem map_derivative_coeff_le_of_coeff_pos_le
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (n : ℕ) :
    v (f.derivative.coeff n) ≤ M := by
  have hnat : v ((n + 1 : ℕ) : R) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one
      (by rw [v.map_zero, v.map_one]; exact zero_le) v.map_one v.map_add
  rw [Polynomial.coeff_derivative, v.map_mul]
  simpa only [Nat.cast_add_one, mul_one] using
    mul_le_mul' (hf (n + 1) (Nat.zero_lt_succ n)) hnat

private theorem map_derivative_eval_le_of_coeff_pos_le
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1) :
    v (f.derivative.eval a) ≤ M :=
  map_eval_le_of_coeff_le v (map_derivative_coeff_le_of_coeff_pos_le v hf) ha

private theorem map_sub_lt_one_of_mul_map_sub_lt_map_derivative
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (hba : M * v (b - a) < v (f.derivative.eval a)) :
    v (b - a) < 1 := by
  have hmul : M * v (b - a) < M * 1 := by
    simpa only [mul_one] using
      hba.trans_le (map_derivative_eval_le_of_coeff_pos_le v hf ha)
  exact lt_of_mul_lt_mul_left hmul zero_le

private theorem map_le_one_of_mul_map_sub_lt_map_derivative
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (hba : M * v (b - a) < v (f.derivative.eval a)) :
    v b ≤ 1 := by
  calc
    v b = v ((b - a) + a) := by rw [sub_add_cancel]
    _ ≤ 1 := v.map_add_le
      (map_sub_lt_one_of_mul_map_sub_lt_map_derivative v hf ha hba).le ha

private theorem map_pow_sub_pow_le (ha : v a ≤ 1) (hb : v b ≤ 1) (n : ℕ) :
    v (b ^ n - a ^ n) ≤ v (b - a) := by
  have hsum : v (∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)) ≤ 1 := by
    apply v.map_sum_le
    intro i _
    rw [v.map_mul, v.map_pow, v.map_pow]
    exact (mul_le_mul' (pow_le_one₀ zero_le hb)
      (pow_le_one₀ zero_le ha)).trans_eq (one_mul _)
  rw [← geom_sum₂_mul b a n, v.map_mul]
  calc
    v (∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)) * v (b - a) ≤
        1 * v (b - a) := mul_le_mul_left hsum _
    _ = v (b - a) := one_mul _

/-- On the valuation unit ball, a bound on the positive-index coefficients bounds
the value of an evaluation difference. The constant coefficient is unrestricted. -/
theorem map_eval_sub_le_of_coeff_pos_le
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M)
    (ha : v a ≤ 1) (hb : v b ≤ 1) :
    v (f.eval b - f.eval a) ≤ M * v (b - a) := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def,
    ← Finset.sum_sub_distrib, ← mul_sub]
  apply v.map_sum_le
  intro n _
  by_cases hn0 : n = 0
  · simp only [hn0, pow_zero, sub_self, mul_zero, v.map_zero]
    exact zero_le
  · rw [v.map_mul]
    exact mul_le_mul' (hf n (Nat.pos_of_ne_zero hn0)) (map_pow_sub_pow_le v ha hb n)

private theorem map_taylor_coeff_pos_le
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (n : ℕ) (hn : 0 < n) : v ((taylor a f).coeff n) ≤ M := by
  rw [taylor_coeff]
  apply map_eval_le_of_coeff_le v ?_ ha
  intro i
  rw [hasseDeriv_coeff]
  calc
    v (((i + n).choose n : R) * f.coeff (i + n)) ≤ v (f.coeff (i + n)) :=
      (show IsNonarchimedean v from v.map_add).nmul_le (by
        rw [v.map_zero]
        exact zero_le)
    _ ≤ M := hf (i + n) (lt_of_lt_of_le hn (Nat.le_add_left n i))

/-- Polynomial evaluation scales displacement from a unit-ball anchor by the
value of its derivative when the coefficient-controlled displacement is smaller. -/
theorem map_eval_sub_eq_of_mul_map_sub_lt_map_derivative
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (hba : M * v (b - a) < v (f.derivative.eval a)) :
    v (f.eval b - f.eval a) = v (f.derivative.eval a) * v (b - a) := by
  have hδ : v (b - a) ≤ 1 :=
    (map_sub_lt_one_of_mul_map_sub_lt_map_derivative v hf ha hba).le
  let q : R[X] := (taylor a f).divX.divX
  have hq : v (q.eval (b - a)) ≤ M := by
    apply map_eval_le_of_coeff_le v ?_ hδ
    intro n
    dsimp only [q]
    rw [coeff_divX, coeff_divX]
    exact map_taylor_coeff_pos_le v hf ha (n + 1 + 1) (Nat.zero_lt_succ _)
  have hexp : f.eval b - f.eval a =
      f.derivative.eval a * (b - a) + q.eval (b - a) * (b - a) ^ 2 := by
    have h₀ := congrArg (fun p : R[X] => p.eval (b - a))
      (divX_mul_X_add (taylor a f))
    have h₁ := congrArg (fun p : R[X] => p.eval (b - a))
      (divX_mul_X_add (taylor a f).divX)
    simp only [eval_add, eval_mul, eval_X, eval_C, taylor_coeff_zero,
      taylor_eval_sub] at h₀
    simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX, zero_add,
      taylor_coeff_one] at h₁
    change q.eval (b - a) * (b - a) + f.derivative.eval a =
      (taylor a f).divX.eval (b - a) at h₁
    rw [← h₀, ← h₁]
    ring
  rw [hexp]
  by_cases hzero : v (b - a) = 0
  · -- A zero-valued displacement need not be zero in the ring.
    have he : v (q.eval (b - a) * (b - a) ^ 2) = 0 := by
      simp [v.map_mul, v.map_pow, hzero]
    rw [v.map_add_of_right_eq_zero he, v.map_mul]
  · have he : v (q.eval (b - a) * (b - a) ^ 2) <
        v (f.derivative.eval a * (b - a)) := by
      rw [v.map_mul, v.map_pow, v.map_mul]
      calc
        v (q.eval (b - a)) * v (b - a) ^ 2 ≤ M * v (b - a) ^ 2 :=
          mul_le_mul_left hq _
        _ = (M * v (b - a)) * v (b - a) := by rw [pow_two, mul_assoc]
        _ < v (f.derivative.eval a) * v (b - a) :=
          mul_lt_mul_of_pos_right hba (zero_lt_iff.2 hzero)
    rw [v.map_add_eq_of_lt_left he, v.map_mul]

/-- The derivative has constant value in the coefficient-controlled strict
ball about a unit-ball anchor. No root hypothesis is needed. -/
theorem map_derivative_eval_eq_of_mul_map_sub_lt_map_derivative
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (hba : M * v (b - a) < v (f.derivative.eval a)) :
    v (f.derivative.eval b) = v (f.derivative.eval a) := by
  have hb : v b ≤ 1 := map_le_one_of_mul_map_sub_lt_map_derivative v hf ha hba
  apply v.map_eq_of_sub_lt
  exact (map_eval_sub_le_of_coeff_pos_le v (f := f.derivative)
    (fun n _ => map_derivative_coeff_le_of_coeff_pos_le v hf n) ha hb).trans_lt hba

/-- Evaluation scales distances between two points of the strict derivative ball
by the derivative value at the original unit-ball anchor. -/
theorem map_eval_sub_eval_eq_of_mul_map_sub_lt_map_derivative
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1)
    (hb : M * v (b - a) < v (f.derivative.eval a))
    (hc : M * v (c - a) < v (f.derivative.eval a)) :
    v (f.eval c - f.eval b) = v (f.derivative.eval a) * v (c - b) := by
  have hbunit : v b ≤ 1 :=
    v.map_le_one_of_mul_map_sub_lt_map_derivative hf ha hb
  have hderiv : v (f.derivative.eval b) = v (f.derivative.eval a) :=
    v.map_derivative_eval_eq_of_mul_map_sub_lt_map_derivative hf ha hb
  have hcb : M * v (c - b) < v (f.derivative.eval b) := by
    rw [hderiv]
    calc
      M * v (c - b) = M * v ((c - a) - (b - a)) := by
        rw [sub_sub_sub_cancel_right]
      _ ≤ M * max (v (c - a)) (v (b - a)) :=
        mul_le_mul_right (v.map_sub (c - a) (b - a)) M
      _ = max (M * v (c - a)) (M * v (b - a)) := mul_max _ _ _
      _ < v (f.derivative.eval a) := max_lt hc hb
  calc
    v (f.eval c - f.eval b) = v (f.derivative.eval b) * v (c - b) :=
      v.map_eval_sub_eq_of_mul_map_sub_lt_map_derivative hf hbunit hcb
    _ = v (f.derivative.eval a) * v (c - b) := by rw [hderiv]

/-- Polynomial evaluation is injective on the strict derivative ball if the
valuation detects zero. The value identities themselves require no separation. -/
theorem injOn_eval_of_mul_map_sub_lt_map_derivative
    (hsep : v.supp = ⊥)
    (hf : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M) (ha : v a ≤ 1) :
    Set.InjOn (fun b : R => f.eval b)
      {b : R | M * v (b - a) < v (f.derivative.eval a)} := by
  intro b hb c hc hbc
  have hderiv : v (f.derivative.eval a) ≠ 0 :=
    ne_of_gt (zero_le.trans_lt hb)
  have hscale :=
    v.map_eval_sub_eval_eq_of_mul_map_sub_lt_map_derivative hf ha hb hc
  change f.eval b = f.eval c at hbc
  rw [← hbc, sub_self, map_zero] at hscale
  have hzero : v (c - b) = 0 :=
    (mul_eq_zero.mp hscale.symm).resolve_left hderiv
  have hmem : c - b ∈ v.supp := (v.mem_supp_iff _).2 hzero
  rw [hsep, Ideal.mem_bot] at hmem
  exact (sub_eq_zero.mp hmem).symm

end Valuation
