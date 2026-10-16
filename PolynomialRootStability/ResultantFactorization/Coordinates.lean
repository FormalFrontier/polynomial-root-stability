/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite polynomial coefficients and the sup norm

The finite coefficient equivalence `Polynomial.degreeLTEquiv` and reconstruction
map `Polynomial.ofFn` identify the coefficient sup norm with the usual finite-Pi
norm. All identities include the empty coefficient vector. No norm on the whole
polynomial ring is introduced.

For ultrametric coefficient seminorms, the coefficient sup norm satisfies the
maximum triangle inequality and is submultiplicative. The product estimate uses
the existing Gauss norm with a submultiplicative coefficient function, without
requiring a multiplicative norm.

The constructions and the coefficient sup norm are those of Mathlib, including
Kevin H. Wilson's `Polynomial.supNorm` and Fabrizio Barroero's polynomial Gauss
norm.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R] {n : ℕ}

/-- The finite coefficient equivalence reads the corresponding coefficient. -/
@[simp]
theorem degreeLTEquiv_apply (p : degreeLT R n) (i : Fin n) :
    degreeLTEquiv R n p i = (p : R[X]).coeff i := rfl

variable [DecidableEq R]

/-- The inverse coefficient equivalence reconstructs the polynomial with `ofFn`. -/
theorem degreeLTEquiv_symm_apply_coe (v : Fin n → R) :
    ((degreeLTEquiv R n).symm v : R[X]) = ofFn n v := by
  exact (ofFn_eq_sum_monomial v).symm

/-- A strict degree bound suffices to reconstruct a polynomial, even at bound zero. -/
theorem ofFn_comp_toFn_eq_id_of_degree_lt {p : R[X]} (hp : p.degree < n) :
    ofFn n (toFn n p) = p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp0).mpr hp)

end Semiring

section SeminormedRing

variable [SeminormedRing R] {n : ℕ}

/-- An upper bound for the sup norm is exactly a uniform bound for all coefficients. -/
theorem supNorm_le_iff (p : R[X]) {M : ℝ} :
    p.supNorm ≤ M ↔ ∀ i : ℕ, ‖p.coeff i‖ ≤ M := by
  constructor
  · exact fun h i ↦ (p.le_supNorm i).trans h
  · intro h
    obtain ⟨i, hi⟩ := p.exists_eq_supNorm
    simpa only [hi] using h i

/-- Taking finitely many coefficients does not increase their sup norm. -/
theorem norm_toFn_le (p : R[X]) : ‖toFn n p‖ ≤ p.supNorm := by
  apply (pi_norm_le_iff_of_nonneg p.supNorm_nonneg).mpr
  intro i
  exact p.le_supNorm i

/-- The sup norm of a polynomial reconstructed from a vector is its finite-Pi norm. -/
@[simp]
theorem supNorm_ofFn [DecidableEq R] (v : Fin n → R) :
    (ofFn n v).supNorm = ‖v‖ := by
  apply le_antisymm
  · apply (supNorm_le_iff _).mpr
    intro i
    by_cases hi : i < n
    · simpa only [ofFn_coeff_eq_val_of_lt v hi] using norm_le_pi_norm v ⟨i, hi⟩
    · simp only [ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_gt hi), norm_zero]
      exact norm_nonneg v
  · apply (pi_norm_le_iff_of_nonneg (ofFn n v).supNorm_nonneg).mpr
    intro i
    simpa only [ofFn_coeff_eq_val_of_lt v i.isLt] using (ofFn n v).le_supNorm i

/-- On strictly bounded-degree polynomials, the finite coefficient norm is the sup norm. -/
theorem norm_toFn_eq_supNorm_of_degree_lt {p : R[X]} (hp : p.degree < n) :
    ‖toFn n p‖ = p.supNorm := by
  classical
  rw [← supNorm_ofFn, ofFn_comp_toFn_eq_id_of_degree_lt hp]

/-- The bounded-degree coefficient equivalence preserves the coefficient sup norm. -/
theorem supNorm_degreeLTEquiv (p : degreeLT R n) :
    (p : R[X]).supNorm = ‖degreeLTEquiv R n p‖ := by
  classical
  have h := supNorm_ofFn ((degreeLTEquiv R n) p)
  rw [← degreeLTEquiv_symm_apply_coe, LinearEquiv.symm_apply_apply] at h
  exact h

/-- Negation preserves the coefficient sup norm. -/
@[simp]
theorem supNorm_neg (p : R[X]) : (-p).supNorm = p.supNorm := by
  simp only [supNorm_eq_iSup, coeff_neg, norm_neg]

end SeminormedRing

section Submultiplicative

variable {S F : Type*} [Semiring S] [FunLike F S ℝ] [ZeroHomClass F S ℝ]
  [NonnegHomClass F S ℝ] [SubmultiplicativeHomClass F S ℝ]

/-- The Gauss norm is submultiplicative for nonarchimedean, submultiplicative
coefficient functions. This extends `Polynomial.gaussNorm_mul_le`, which assumes
that the coefficient function is multiplicative. -/
theorem gaussNorm_mul_le_of_submultiplicative (v : F) (hna : IsNonarchimedean v)
    (p q : S[X]) {c : ℝ} (hc : 0 ≤ c) :
    (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  obtain ⟨i, hi⟩ := (p * q).exists_eq_gaussNorm v c
  rw [hi, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨j, hj, hsum⟩ := hna.finset_image_add_of_nonempty
    (fun j ↦ p.coeff j * q.coeff (i - j)) Finset.nonempty_range_add_one
  have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    v (∑ j ∈ Finset.range (i + 1), p.coeff j * q.coeff (i - j)) * c ^ i
        ≤ v (p.coeff j * q.coeff (i - j)) * c ^ i :=
      mul_le_mul_of_nonneg_right hsum (pow_nonneg hc i)
    _ ≤ (v (p.coeff j) * v (q.coeff (i - j))) * c ^ i :=
      mul_le_mul_of_nonneg_right (map_mul_le_mul v _ _) (pow_nonneg hc i)
    _ = (v (p.coeff j) * c ^ j) * (v (q.coeff (i - j)) * c ^ (i - j)) := by
      rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le hji]
    _ ≤ p.gaussNorm v c * q.gaussNorm v c :=
      mul_le_mul (p.le_gaussNorm v hc j) (q.le_gaussNorm v hc (i - j))
        (mul_nonneg (apply_nonneg v _) (pow_nonneg hc _)) (p.gaussNorm_nonneg v hc)

end Submultiplicative

section Multiplicative

variable {S F : Type*} [Semiring S] [FunLike F S ℝ] [ZeroHomClass F S ℝ]
  [NonnegHomClass F S ℝ] [MulHomClass F S ℝ]

/-- Multiplicative coefficient functions recover the Gauss-norm product bound
through their submultiplicative structure. -/
private theorem gaussNorm_mul_le_of_mulHomClass (v : F) (hna : IsNonarchimedean v)
    (p q : S[X]) {c : ℝ} (hc : 0 ≤ c) :
    (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  let : SubmultiplicativeHomClass F S ℝ := ⟨fun v x y ↦ (map_mul v x y).le⟩
  exact gaussNorm_mul_le_of_submultiplicative v hna p q hc

end Multiplicative

section Ultrametric

variable [SeminormedRing R] [IsUltrametricDist R]

/-- The coefficient sup norm satisfies the ultrametric triangle inequality. -/
theorem supNorm_add_le_max (p q : R[X]) :
    (p + q).supNorm ≤ max p.supNorm q.supNorm := by
  exact isNonarchimedean_gaussNorm (SeminormedRing.toRingSeminorm R)
    IsUltrametricDist.isNonarchimedean_norm (by norm_num) p q

/-- The sup norm of a difference is bounded by the larger input sup norm. -/
theorem supNorm_sub_le_max (p q : R[X]) :
    (p - q).supNorm ≤ max p.supNorm q.supNorm := by
  simpa only [sub_eq_add_neg, supNorm_neg] using supNorm_add_le_max p (-q)

/-- The coefficient sup norm is submultiplicative for ultrametric seminormed rings. -/
theorem supNorm_mul_le (p q : R[X]) :
    (p * q).supNorm ≤ p.supNorm * q.supNorm := by
  exact gaussNorm_mul_le_of_submultiplicative (SeminormedRing.toRingSeminorm R)
    IsUltrametricDist.isNonarchimedean_norm p q (by norm_num)

/-- A difference of polynomial products is bounded by its two first-order terms. -/
theorem supNorm_mul_sub_mul_le (p q p' q' : R[X]) :
    (p * q - p' * q').supNorm ≤
      max ((p - p').supNorm * q.supNorm) (p'.supNorm * (q - q').supNorm) := by
  have h : p * q - p' * q' = (p - p') * q + p' * (q - q') := by
    simp only [sub_mul, mul_sub, sub_add_sub_cancel]
  rw [h]
  exact (supNorm_add_le_max _ _).trans (max_le_max (supNorm_mul_le _ _) (supNorm_mul_le _ _))

end Ultrametric

end Polynomial
