/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Ultrametric

/-!
# Polynomial root uniqueness in an ultrametric derivative ball

A uniform coefficient bound controls the radius in which a root in the norm
unit ball is the only root. Local polynomial norm scaling forces two roots in
this derivative ball to have zero distance; separation gives equality.
Neither completeness nor division is required.

Polynomial evaluation is also injective on the strict derivative ball about any
point in the norm unit ball under the same uniform coefficient bound.
-/

@[expose] public section

universe u

namespace Polynomial

/-- Polynomial evaluation is injective on the strict derivative ball about a point
in the norm unit ball, under a uniform coefficient bound. -/
theorem injOn_eval_of_mul_norm_sub_lt_norm_derivative
    {R : Type u} [NormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f : R[X]} {M : ℝ} {a : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (ha : ‖a‖ ≤ 1) :
    Set.InjOn (fun b : R => f.eval b)
      {b : R | M * ‖b - a‖ < ‖f.derivative.eval a‖} := by
  have hsq : ‖(1 : R)‖ ^ 2 = ‖(1 : R)‖ := by
    rw [pow_two, ← norm_mul, one_mul]
  rcases eq_zero_or_one_of_sq_eq_self hsq with hzero | hone
  · have hz (x : R) : ‖x‖ = 0 := by
      simpa only [one_mul, hzero, zero_mul] using (norm_mul (1 : R) x)
    intro b hb
    change M * ‖b - a‖ < ‖f.derivative.eval a‖ at hb
    have hlt : (0 : ℝ) < 0 := by
      simpa only [hz, mul_zero] using hb
    exact (lt_irrefl 0 hlt).elim
  · let : NormOneClass R := ⟨hone⟩
    have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
    let M₀ : NNReal := ⟨M, hM⟩
    let v : Valuation R NNReal :=
      Valuation.mk (nnnormHom : R →*₀ NNReal)
        (fun x y => IsUltrametricDist.nnnorm_add_le_max x y)
    have hv (x : R) : (v x : ℝ) = ‖x‖ := by
      change ((nnnormHom : R →*₀ NNReal) x : ℝ) = ‖x‖
      rfl
    have hM₀ : (M₀ : ℝ) = M := rfl
    have hf₀ : ∀ n : ℕ, 0 < n → v (f.coeff n) ≤ M₀ :=
      fun n _ => NNReal.coe_le_coe.mp (hf n)
    have ha₀ : v a ≤ 1 := NNReal.coe_le_coe.mp ha
    have hsep : v.supp = ⊥ := by
      ext x
      simp only [Valuation.mem_supp_iff, Ideal.mem_bot]
      change ‖x‖₊ = 0 ↔ x = 0
      exact nnnorm_eq_zero
    intro b hb c hc heval
    refine v.injOn_eval_of_mul_map_sub_lt_map_derivative hsep hf₀ ha₀ ?_ ?_ heval
    · apply NNReal.coe_lt_coe.mp
      simpa only [Set.mem_ofPred_eq, NNReal.coe_mul, hv, hM₀] using hb
    · apply NNReal.coe_lt_coe.mp
      simpa only [Set.mem_ofPred_eq, NNReal.coe_mul, hv, hM₀] using hc

/-- A root in the norm unit ball is the only root at distance strictly less
than its derivative norm divided by a uniform coefficient bound, expressed
without division. -/
theorem eq_of_eval_eq_zero_of_mul_norm_sub_lt_norm_derivative
    {R : Type u} [NormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f : R[X]} {M : ℝ} {x y : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M) (hy : ‖y‖ ≤ 1)
    (hfx : f.eval x = 0) (hfy : f.eval y = 0)
    (hxy : M * ‖x - y‖ < ‖f.derivative.eval y‖) : x = y := by
  have hnorm := norm_eval_sub_eq_of_mul_norm_sub_lt_norm_derivative
    (a := y) (b := x) hf hy hxy
  rw [hfx, hfy, sub_self, norm_zero] at hnorm
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hdpos : 0 < ‖f.derivative.eval y‖ :=
    (mul_nonneg hM (norm_nonneg (x - y))).trans_lt hxy
  have hdist : ‖x - y‖ = 0 :=
    (mul_eq_zero.mp hnorm.symm).resolve_left (ne_of_gt hdpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hdist)

end Polynomial
