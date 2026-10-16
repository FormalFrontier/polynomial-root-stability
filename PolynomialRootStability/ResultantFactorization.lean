/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.ResultantFactorization.Algebra
public import PolynomialRootStability.ResultantFactorization.Coordinates
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Resultant-controlled polynomial factorization

A coefficient error smaller than the square of the resultant norm permits a
factorization near two prescribed integral polynomials, with their degrees and
leading coefficients preserved. Integrality means that every coefficient has
norm at most one, expressed using `Polynomial.supNorm`. The resultant uses the
natural degrees of its two inputs.

## Implementation notes

The proof keeps the initial Sylvester inverse fixed and applies Mathlib's Banach
fixed-point theorem on complete finite coefficient spaces. No complete normed
structure on the whole polynomial ring is required. The scope includes complete
ultrametric normed fields of arbitrary characteristic, including trivially normed
fields, without monicity or norm-one leading coefficients. It does not address
arbitrary higher-rank valuations.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Proposition 1.1, p. 36.
* Mathlib's `Polynomial.supNorm`, due to Kevin H. Wilson, and polynomial resultant
  API, due to Kenny Lau, Anne Baanen, and Andrew Yang.
* Mathlib's finite coefficient equivalence `Polynomial.degreeLTEquiv` and
  reconstruction map `Polynomial.ofFn`.
* Mathlib's Banach fixed-point theorem, `ContractingWith.exists_fixedPoint'`,
  by Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, and Yury Kudryashov.
-/

@[expose] public section

universe u

open scoped NNReal

namespace Polynomial

private theorem degree_mul_lt_add_of_degree_lt
    {R : Type*} [Semiring R] {p q : R[X]} {m n : ℕ}
    (hp : p.degree < (m : WithBot ℕ)) (hq : q.degree < (n : WithBot ℕ)) :
    (p * q).degree < ((m + n : ℕ) : WithBot ℕ) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact (degree_mul_le _ _).trans_lt (by
    simpa using WithBot.add_lt_add_of_le_of_lt (degree_ne_bot.mpr hp0) hp.le hq)

private theorem degree_leadingCoeff_add_of_degree_lt_natDegree
    {R : Type*} [Semiring R] {p q : R[X]}
    (hq : q.degree < (p.natDegree : WithBot ℕ)) :
    (p + q).degree = p.degree ∧ (p + q).leadingCoeff = p.leadingCoeff := by
  by_cases hp0 : p = 0
  · have hq0 : q = 0 := by
      simpa only [hp0, natDegree_zero, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
        degree_eq_bot] using hq
    simp [hq0]
  have hqp : q.degree < p.degree := by rwa [degree_eq_natDegree hp0]
  exact ⟨degree_add_eq_left_of_degree_lt hqp, leadingCoeff_add_of_degree_lt' hqp⟩

/-- A bounded right inverse of the linearized product gives a small nonlinear correction. -/
private theorem exists_polynomial_correction
    {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [DecidableEq K]
    {m n : ℕ} (g₀ h₀ e₀ : K[X]) (he₀ : e₀.degree < ((m + n : ℕ) : WithBot ℕ))
    (B : (Fin (m + n) → K) →ₗ[K] ((Fin m → K) × (Fin n → K)))
    (r : ℝ) (hr : 0 < r) (hclose : e₀.supNorm < r ^ 2)
    (hB : ∀ z, ‖B z‖ ≤ ‖z‖ / r)
    (hright : ∀ z, g₀ * ofFn n (B z).2 + h₀ * ofFn m (B z).1 =
      ((degreeLTEquiv K (m + n)).symm z : K[X])) :
    ∃ x : (Fin m → K) × (Fin n → K), ‖x‖ ≤ e₀.supNorm / r ∧
      e₀ = g₀ * ofFn n x.2 + h₀ * ofFn m x.1 + ofFn m x.1 * ofFn n x.2 := by
  let δ := e₀.supNorm
  let t := δ / r
  let C := degreeLTEquiv K (m + n)
  let e : Fin (m + n) → K := C ⟨e₀, mem_degreeLT.mpr he₀⟩
  let P (x : (Fin m → K) × (Fin n → K)) : degreeLT K (m + n) :=
    ⟨ofFn m x.1 * ofFn n x.2, mem_degreeLT.mpr
      (degree_mul_lt_add_of_degree_lt (ofFn_degree_lt _) (ofFn_degree_lt _))⟩
  let Q := fun x => C (P x)
  have hδ : ‖e‖ = δ := (supNorm_degreeLTEquiv _).symm
  have hδ0 : 0 ≤ δ := supNorm_nonneg _
  have ht0 : 0 ≤ t := div_nonneg hδ0 hr.le
  have htr : t < r := (div_lt_iff₀ hr).2 (by simpa [pow_two] using hclose)
  have htq : t ^ 2 / r ≤ t := by
    apply (div_le_iff₀ hr).2
    nlinarith
  have hQ (x) : ‖Q x‖ ≤ ‖x‖ ^ 2 := calc
    ‖Q x‖ = (ofFn m x.1 * ofFn n x.2).supNorm := (supNorm_degreeLTEquiv _).symm
    _ ≤ (ofFn m x.1).supNorm * (ofFn n x.2).supNorm := supNorm_mul_le _ _
    _ = ‖x.1‖ * ‖x.2‖ := by rw [supNorm_ofFn, supNorm_ofFn]
    _ ≤ ‖x‖ ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (norm_fst_le x) (norm_snd_le x) (norm_nonneg _) (norm_nonneg _)
  have hQsub (x y) (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t) :
      ‖Q x - Q y‖ ≤ t * ‖x - y‖ := by
    have hux : (ofFn m x.1 - ofFn m y.1).supNorm ≤ ‖x - y‖ := by
      rw [← map_sub, supNorm_ofFn]
      exact norm_fst_le (x - y)
    have hvx : (ofFn n x.2 - ofFn n y.2).supNorm ≤ ‖x - y‖ := by
      rw [← map_sub, supNorm_ofFn]
      exact norm_snd_le (x - y)
    have huy : (ofFn m y.1).supNorm ≤ t := by
      rw [supNorm_ofFn]
      exact (norm_fst_le y).trans hy
    have hv : (ofFn n x.2).supNorm ≤ t := by
      rw [supNorm_ofFn]
      exact (norm_snd_le x).trans hx
    calc
      ‖Q x - Q y‖ = (ofFn m x.1 * ofFn n x.2 - ofFn m y.1 * ofFn n y.2).supNorm := by
        change ‖C (P x) - C (P y)‖ = _
        rw [← map_sub]
        exact (supNorm_degreeLTEquiv _).symm
      _ ≤ max ((ofFn m x.1 - ofFn m y.1).supNorm * (ofFn n x.2).supNorm)
          ((ofFn m y.1).supNorm * (ofFn n x.2 - ofFn n y.2).supNorm) :=
        supNorm_mul_sub_mul_le _ _ _ _
      _ ≤ t * ‖x - y‖ := by
        apply max_le
        · calc
            _ ≤ ‖x - y‖ * t := mul_le_mul hux hv (supNorm_nonneg _) (norm_nonneg _)
            _ = t * ‖x - y‖ := mul_comm _ _
        · exact mul_le_mul huy hvx (supNorm_nonneg _) ht0
  have hsub (a b : Fin (m + n) → K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg a).trans (le_max_left _ _))).2
    intro i
    change ‖a i - b i‖ ≤ max ‖a‖ ‖b‖
    have hab : ‖a i - b i‖ ≤ max ‖a i‖ ‖b i‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max (a i) (-b i)
    exact hab.trans (max_le_max (norm_le_pi_norm a i) (norm_le_pi_norm b i))
  -- Apply the frozen inverse to the quadratic residual on the coefficient ball.
  let T := fun x => B (e - Q x)
  have hmaps : Set.MapsTo T (Metric.closedBall 0 t) (Metric.closedBall 0 t) := by
    intro x hx
    have hx' : ‖x‖ ≤ t := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hq : ‖Q x‖ ≤ t ^ 2 := (hQ x).trans (by nlinarith [norm_nonneg x])
    have : ‖T x‖ ≤ t := calc
      ‖T x‖ ≤ ‖e - Q x‖ / r := hB _
      _ ≤ max ‖e‖ ‖Q x‖ / r := div_le_div_of_nonneg_right (hsub _ _) hr.le
      _ ≤ max δ (t ^ 2) / r := div_le_div_of_nonneg_right (max_le_max hδ.le hq) hr.le
      _ = max (δ / r) (t ^ 2 / r) := by rw [← max_div_div_right hr.le]
      _ ≤ t := max_le le_rfl htq
    simpa only [Metric.mem_closedBall, dist_zero_right] using this
  let q : ℝ≥0 := ⟨t / r, div_nonneg ht0 hr.le⟩
  have hq1 : q < 1 := by
    change t / r < 1
    exact (div_lt_one hr).2 htr
  have hc : ContractingWith q
      (hmaps.restrict T (Metric.closedBall 0 t) (Metric.closedBall 0 t)) := by
    refine ⟨hq1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist (T x.val) (T y.val) ≤ (t / r) * dist x.val y.val
    have hx : ‖x.val‖ ≤ t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    have hy : ‖y.val‖ ≤ t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using y.property
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖T x.val - T y.val‖ = ‖B (-(Q x.val - Q y.val))‖ := by
        congr 1
        rw [← map_sub]
        congr 1
        abel
      _ ≤ ‖-(Q x.val - Q y.val)‖ / r := hB _
      _ ≤ (t * ‖x.val - y.val‖) / r := by
        rw [norm_neg]
        exact div_le_div_of_nonneg_right (hQsub _ _ hx hy) hr.le
      _ = t / r * ‖x.val - y.val‖ := by ring
  -- The finite coefficient space and its closed ball are complete, also in dimension zero.
  obtain ⟨x, hx, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hc
    (Metric.mem_closedBall_self ht0) (edist_ne_top (0 : (Fin m → K) × (Fin n → K)) (T 0))
  refine ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, ?_⟩
  have hpoly := hright (e - Q x)
  change B (e - Q x) = x at hfix
  rw [hfix] at hpoly
  have hrecon : ((degreeLTEquiv K (m + n)).symm (e - Q x) : K[X]) =
      e₀ - ofFn m x.1 * ofFn n x.2 := by
    change (C.symm (C ⟨e₀, mem_degreeLT.mpr he₀⟩ - C (P x)) : K[X]) = _
    rw [← map_sub, LinearEquiv.symm_apply_apply]
    rfl
  rw [hrecon] at hpoly
  linear_combination -hpoly

/-- Quantitative factor lifting over a complete ultrametric normed field.
This norm formulation of Fesenko–Vostokov, Chapter II, §1, Proposition 1.1 preserves
each initial factor's degree and leading coefficient, and bounds both corrections
by the initial error divided by the resultant norm. The proof uses a fixed inverse
of the initial Sylvester map and Mathlib's Banach fixed-point theorem on finite
coefficient spaces.

The strict error-degree bound expresses the degree and exact leading-coefficient
constraint without a monicity assumption. All strict degree bounds use `degree`
in `WithBot ℕ`, so a correction of degree less than zero is the zero polynomial.
This specifies the zero-constant cases whose degree convention the source leaves
implicit. If both initial natural degrees are zero, the error must be zero,
including when a constant factor is zero. The default resultant at sizes `(0, 0)` is
`1`, not `0`. A zero factor with the other factor of positive degree has zero
resultant and cannot satisfy the strict norm bound. Zero error with nonzero
resultant is allowed, and gives zero corrections. -/
theorem exists_factorization_of_supNorm_lt_resultant_sq
    {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f g₀ h₀ : K[X])
    (hg₀ : g₀.supNorm ≤ 1) (hh₀ : h₀.supNorm ≤ 1)
    (hdegree : (f - g₀ * h₀).degree <
      ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ))
    (hclose : (f - g₀ * h₀).supNorm < ‖g₀.resultant h₀‖ ^ 2) :
    ∃ g h : K[X],
      f = g * h ∧
      g.degree = g₀.degree ∧ h.degree = h₀.degree ∧
      g.leadingCoeff = g₀.leadingCoeff ∧ h.leadingCoeff = h₀.leadingCoeff ∧
      (g - g₀).degree < (g₀.natDegree : WithBot ℕ) ∧
      (h - h₀).degree < (h₀.natDegree : WithBot ℕ) ∧
      g.supNorm ≤ 1 ∧ h.supNorm ≤ 1 ∧
      (g - g₀).supNorm ≤ (f - g₀ * h₀).supNorm / ‖g₀.resultant h₀‖ ∧
      (h - h₀).supNorm ≤ (f - g₀ * h₀).supNorm / ‖g₀.resultant h₀‖ := by
  classical
  by_cases he : f - g₀ * h₀ = 0
  · refine ⟨g₀, h₀, sub_eq_zero.mp he, rfl, rfl, rfl, rfl, ?_, ?_, hg₀, hh₀, ?_, ?_⟩ <;>
      simp [he]
  let m := g₀.natDegree
  let n := h₀.natDegree
  let R := g₀.resultant h₀
  let r := ‖R‖
  have hr : 0 < r := by
    have : 0 < r ^ 2 := (supNorm_nonneg _).trans_lt hclose
    nlinarith [norm_nonneg R]
  have hR : R ≠ 0 := norm_pos_iff.mp hr
  have hr1 : r ≤ 1 := norm_resultant_le_one m n hg₀ hh₀
  let c := (degreeLTEquiv K m).prodCongr (degreeLTEquiv K n)
  let C := degreeLTEquiv K (m + n)
  let a := adjSylvester (m := m) (n := n) g₀ h₀
  let B := c.toLinearMap ∘ₗ (R⁻¹ • a) ∘ₗ C.symm.toLinearMap
  have hB : ∀ z, ‖B z‖ ≤ ‖z‖ / r := by
    intro z
    have hznorm : ((C.symm z : degreeLT K (m + n)) : K[X]).supNorm = ‖z‖ := by
      rw [supNorm_degreeLTEquiv]
      exact congrArg norm (C.apply_symm_apply z)
    rw [Prod.norm_def]
    change max ‖degreeLTEquiv K m (R⁻¹ • a (C.symm z)).1‖
      ‖degreeLTEquiv K n (R⁻¹ • a (C.symm z)).2‖ ≤ _
    rw [← supNorm_degreeLTEquiv, ← supNorm_degreeLTEquiv]
    apply max_le
    · simpa only [hznorm] using supNorm_inv_smul_adjSylvester_fst_le hg₀ hh₀ (C.symm z)
    · simpa only [hznorm] using supNorm_inv_smul_adjSylvester_snd_le hg₀ hh₀ (C.symm z)
  have hright : ∀ z, g₀ * ofFn n (B z).2 + h₀ * ofFn m (B z).1 =
      (C.symm z : K[X]) := by
    intro z
    have hc : c.symm (B z) = R⁻¹ • a (C.symm z) := by
      change c.symm (c (R⁻¹ • a (C.symm z))) = _
      exact c.symm_apply_apply _
    have hid : sylvesterMap g₀ h₀ le_rfl le_rfl (c.symm (B z)) = C.symm z := by
      rw [hc]
      exact LinearMap.congr_fun
        (sylvesterMap_comp_inv_smul_adjSylvester (le_refl m) (le_refl n) hR) (C.symm z)
    have hp := congrArg (fun w : degreeLT K (m + n) => (w : K[X])) hid
    rw [sylvesterMap_apply_coe] at hp
    change g₀ * ((degreeLTEquiv K n).symm (B z).2 : K[X]) +
      h₀ * ((degreeLTEquiv K m).symm (B z).1 : K[X]) = _ at hp
    simpa only [degreeLTEquiv_symm_apply_coe] using hp
  obtain ⟨x, hx, heq⟩ := exists_polynomial_correction
    g₀ h₀ (f - g₀ * h₀) hdegree B r hr hclose hB hright
  let u := ofFn m x.1
  let v := ofFn n x.2
  have hu : u.degree < (g₀.natDegree : WithBot ℕ) := ofFn_degree_lt _
  have hv : v.degree < (h₀.natDegree : WithBot ℕ) := ofFn_degree_lt _
  have hgu := degree_leadingCoeff_add_of_degree_lt_natDegree hu
  have hhv := degree_leadingCoeff_add_of_degree_lt_natDegree hv
  have huNorm : u.supNorm ≤ (f - g₀ * h₀).supNorm / r := by
    rw [supNorm_ofFn]
    exact (norm_fst_le x).trans hx
  have hvNorm : v.supNorm ≤ (f - g₀ * h₀).supNorm / r := by
    rw [supNorm_ofFn]
    exact (norm_snd_le x).trans hx
  have ht : (f - g₀ * h₀).supNorm / r < r :=
    (div_lt_iff₀ hr).2 (by simpa only [pow_two] using hclose)
  refine ⟨g₀ + u, h₀ + v, ?_, hgu.1, hhv.1, hgu.2, hhv.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change f - g₀ * h₀ = g₀ * v + h₀ * u + u * v at heq
    linear_combination heq
  · simpa only [add_sub_cancel_left] using hu
  · simpa only [add_sub_cancel_left] using hv
  · exact (supNorm_add_le_max _ _).trans (max_le hg₀ (huNorm.trans (ht.le.trans hr1)))
  · exact (supNorm_add_le_max _ _).trans (max_le hh₀ (hvNorm.trans (ht.le.trans hr1)))
  · simpa only [add_sub_cancel_left] using huNorm
  · simpa only [add_sub_cancel_left] using hvNorm

end Polynomial
