/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Ultrametric bounds for the Sylvester adjugate

The determinant and adjugate of a matrix with entries in the closed unit ball
again have entries in that ball. Applied to `Polynomial.sylvester`, this bounds
`Polynomial.resultant` and both outputs of `Polynomial.adjSylvester`.
Dividing the latter map by a nonzero resultant gives degree-controlled linear
corrections, with coefficient bounds independent of the degrees.

The proofs use Mathlib's determinant expansion, adjugate, coefficient bases and
Sylvester composition identities. The ultrametric finite-sum estimate avoids any
factor depending on the matrix size. No completeness or nontrivial norm is needed;
empty matrices and zero-dimensional coefficient spaces are included.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An integral matrix over an ultrametric normed ring has integral determinant. -/
theorem norm_det_le_one (A : Matrix ι ι R) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ≤ 1 := by
  rw [det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro σ _
  rw [norm_units_zsmul]
  have hprod (s : Finset ι) : ‖∏ i ∈ s, A (σ i) i‖ ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (norm_mul_le _ _).trans
        ((mul_le_mul (hA (σ i) i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  exact hprod _

/-- Every entry of the adjugate of an integral ultrametric matrix is integral. -/
theorem norm_adjugate_apply_le_one (A : Matrix ι ι R) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (i j : ι) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [adjugate_apply]
  apply norm_det_le_one
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [updateRow_self]
    by_cases hl : l = i
    · subst l; simp
    · simp [Pi.single_eq_of_ne hl]
  · simpa [updateRow_ne hk] using hA k l

end Matrix

namespace Polynomial

section SeminormedCommRing

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  {f g : R[X]} {m n : ℕ}

omit [NormOneClass R] [IsUltrametricDist R] in
private theorem norm_sylvester_apply_le_one (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (i j : Fin (m + n)) : ‖f.sylvester g m n i j‖ ≤ 1 := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact (g.le_supNorm _).trans hg
    · simp
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact (f.le_supNorm _).trans hf
    · simp

/-- The fixed-size resultant of polynomials with integral coefficients has norm at most one.
The prescribed sizes need not equal their natural degrees. -/
theorem norm_resultant_le_one (m n : ℕ) (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1) :
    ‖f.resultant g m n‖ ≤ 1 :=
  Matrix.norm_det_le_one _ (norm_sylvester_apply_le_one hf hg)

private theorem norm_adjSylvester_repr_le (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (p : degreeLT R (m + n)) (i : Fin (m + n)) :
    ‖(degreeLT.basisProd R m n).repr (adjSylvester f g p) i‖ ≤ (p : R[X]).supNorm := by
  have heq := congrFun (Matrix.repr_toLin (degreeLT.basis R (m + n))
    (degreeLT.basisProd R m n) (f.sylvester g m n).adjugate p) i
  change (degreeLT.basisProd R m n).repr (adjSylvester f g p) i = _ at heq
  rw [heq, Matrix.mulVec, dotProduct]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (supNorm_nonneg _)
  intro j _
  calc
    ‖(f.sylvester g m n).adjugate i j * (degreeLT.basis R (m + n)).repr p j‖
      ≤ ‖(f.sylvester g m n).adjugate i j‖ * ‖(p : R[X]).coeff j‖ := norm_mul_le _ _
    _ ≤ 1 * (p : R[X]).supNorm := mul_le_mul
      (Matrix.norm_adjugate_apply_le_one _ (norm_sylvester_apply_le_one hf hg) i j)
      (le_supNorm _ _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The first polynomial produced by the Sylvester adjugate has coefficients bounded by
those of its input, when the two defining polynomials have integral coefficients. -/
theorem supNorm_adjSylvester_fst_le (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (p : degreeLT R (m + n)) :
    ((adjSylvester f g p).1 : R[X]).supNorm ≤ (p : R[X]).supNorm := by
  obtain ⟨i, hi⟩ := exists_eq_supNorm ((adjSylvester f g p).1 : R[X])
  rw [hi]
  by_cases him : i < m
  · simpa only [degreeLT.basisProd, Module.Basis.repr_reindex_apply,
      finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl, degreeLT.basis_repr] using
      norm_adjSylvester_repr_le hf hg p ((⟨i, him⟩ : Fin m).castAdd n)
  · rw [coeff_eq_zero_of_degree_lt]
    · simpa using supNorm_nonneg (p : R[X])
    · exact (mem_degreeLT.mp (adjSylvester f g p).1.property).trans_le
        (by exact_mod_cast Nat.le_of_not_gt him)

/-- The second polynomial produced by the Sylvester adjugate has coefficients bounded by
those of its input, when the two defining polynomials have integral coefficients. -/
theorem supNorm_adjSylvester_snd_le (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (p : degreeLT R (m + n)) :
    ((adjSylvester f g p).2 : R[X]).supNorm ≤ (p : R[X]).supNorm := by
  obtain ⟨i, hi⟩ := exists_eq_supNorm ((adjSylvester f g p).2 : R[X])
  rw [hi]
  by_cases hin : i < n
  · simpa only [degreeLT.basisProd, Module.Basis.repr_reindex_apply,
      finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_repr_inr, degreeLT.basis_repr] using
      norm_adjSylvester_repr_le hf hg p ((⟨i, hin⟩ : Fin n).natAdd m)
  · rw [coeff_eq_zero_of_degree_lt]
    · simpa using supNorm_nonneg (p : R[X])
    · exact (mem_degreeLT.mp (adjSylvester f g p).2.property).trans_le
        (by exact_mod_cast Nat.le_of_not_gt hin)

end SeminormedCommRing

section Field

variable {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}

/-- Dividing the Sylvester adjugate by the resultant gives a right inverse of the
Sylvester map, if the fixed-size resultant is nonzero. -/
theorem sylvesterMap_comp_inv_smul_adjSylvester (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (hR : f.resultant g m n ≠ 0) :
    sylvesterMap f g hf hg ∘ₗ ((f.resultant g m n)⁻¹ • adjSylvester f g) =
      LinearMap.id := by
  rw [LinearMap.comp_smul, sylveserMap_comp_adjSylvester, smul_smul,
    inv_mul_cancel₀ hR, one_smul]

/-- Dividing the Sylvester adjugate by the resultant gives a left inverse of the
Sylvester map, if the fixed-size resultant is nonzero. -/
theorem inv_smul_adjSylvester_comp_sylvesterMap (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (hR : f.resultant g m n ≠ 0) :
    ((f.resultant g m n)⁻¹ • adjSylvester f g) ∘ₗ sylvesterMap f g hf hg =
      LinearMap.id := by
  rw [LinearMap.smul_comp, adjSylvester_comp_sylveserMap, smul_smul,
    inv_mul_cancel₀ hR, one_smul]

end Field

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {f g : K[X]} {m n : ℕ}

/-- The first correction obtained by dividing the Sylvester adjugate by the resultant
is bounded by the input's coefficient norm divided by the resultant norm. -/
theorem supNorm_inv_smul_adjSylvester_fst_le (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (p : degreeLT K (m + n)) :
    (((f.resultant g m n)⁻¹ • adjSylvester f g p).1 : K[X]).supNorm ≤
      (p : K[X]).supNorm / ‖f.resultant g m n‖ := by
  obtain ⟨i, hi⟩ := exists_eq_supNorm
    (((f.resultant g m n)⁻¹ • adjSylvester f g p).1 : K[X])
  rw [hi]
  simp only [Prod.smul_fst, Submodule.coe_smul, coeff_smul, smul_eq_mul, norm_mul, norm_inv]
  rw [div_eq_mul_inv, mul_comm (p : K[X]).supNorm]
  exact mul_le_mul_of_nonneg_left
    ((le_supNorm _ i).trans (supNorm_adjSylvester_fst_le hf hg p)) (inv_nonneg.mpr (norm_nonneg _))

/-- The second correction obtained by dividing the Sylvester adjugate by the resultant
is bounded by the input's coefficient norm divided by the resultant norm. -/
theorem supNorm_inv_smul_adjSylvester_snd_le (hf : f.supNorm ≤ 1) (hg : g.supNorm ≤ 1)
    (p : degreeLT K (m + n)) :
    (((f.resultant g m n)⁻¹ • adjSylvester f g p).2 : K[X]).supNorm ≤
      (p : K[X]).supNorm / ‖f.resultant g m n‖ := by
  obtain ⟨i, hi⟩ := exists_eq_supNorm
    (((f.resultant g m n)⁻¹ • adjSylvester f g p).2 : K[X])
  rw [hi]
  simp only [Prod.smul_snd, Submodule.coe_smul, coeff_smul, smul_eq_mul, norm_mul, norm_inv]
  rw [div_eq_mul_inv, mul_comm (p : K[X]).supNorm]
  exact mul_le_mul_of_nonneg_left
    ((le_supNorm _ i).trans (supNorm_adjSylvester_snd_le hf hg p)) (inv_nonneg.mpr (norm_nonneg _))

end NormedField

end Polynomial
