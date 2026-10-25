/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
public import PolynomialRootStability.Ultrametric
import Mathlib.Topology.MetricSpace.Contracting
import PolynomialRootStability.RootUniqueness

/-!
# Root existence and bounds under coefficient perturbation

A uniform perturbation of polynomial coefficients bounds the distance between two
given roots in the original polynomial's strict derivative ball. This sharp bound
is scaled by the original derivative norm and holds over ultrametric seminormed
commutative rings with multiplicative norm; no separation assumption is needed.

In a complete ultrametric normed commutative ring with multiplicative norm,
`Polynomial.exists_root_of_norm_coeff_sub_le_of_isUnit` constructs a root of the
perturbed polynomial when the original derivative is a unit and the perturbation
satisfies `M * ε < ‖f.derivative.eval a‖ ^ 2`. The root lies in the original strict
derivative ball and satisfies the sharp scaled distance bound. Uniqueness holds
among all roots of the perturbed polynomial in that ball, without a distance-bound
premise on competing roots.

`Polynomial.exists_root_of_norm_coeff_sub_le` derives the derivative unit from the
strict ball inequality over a complete ultrametric normed field. Neither theorem
requires a root of the perturbed polynomial as input, and `ε = 0` is allowed. Their
existential conclusions provide the root-construction and characterization API,
without choosing a root object.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A coefficient perturbation smaller than the reference derivative norm preserves exact
distance scaling on the original strict derivative ball. -/
theorem norm_eval_sub_eval_eq_of_norm_coeff_sub_le
    {R : Type u} [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f g : R[X]} {M ε : ℝ} {a y z : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hy : M * ‖y - a‖ < ‖f.derivative.eval a‖)
    (hz : M * ‖z - a‖ < ‖f.derivative.eval a‖)
    (hfg : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε)
    (hsmall : ε < ‖f.derivative.eval a‖) :
    ‖g.eval y - g.eval z‖ = ‖f.derivative.eval a‖ * ‖y - z‖ := by
  have hDM : ‖f.derivative.eval a‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hf) ha
  have hgf : ∀ n : ℕ, ‖g.coeff n - f.coeff n‖ ≤ ε := by
    intro n
    rw [norm_sub_rev]
    exact hfg n
  have hgf_coeff : ∀ n : ℕ, ‖(g - f).coeff n‖ ≤ ε := by
    simpa only [coeff_sub] using hgf
  have hg : ∀ n : ℕ, ‖g.coeff n‖ ≤ M := by
    intro n
    calc
      ‖g.coeff n‖ = ‖(g.coeff n - f.coeff n) + f.coeff n‖ := by
        rw [sub_add_cancel]
      _ ≤ max ‖g.coeff n - f.coeff n‖ ‖f.coeff n‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ M := max_le ((hgf n).trans (hsmall.le.trans hDM)) (hf n)
  have hgd : ‖g.derivative.eval a - f.derivative.eval a‖ ≤ ε := by
    have h := norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hgf_coeff) ha
    simpa only [derivative_sub, eval_sub] using h
  have hgD : ‖g.derivative.eval a‖ = ‖f.derivative.eval a‖ := by
    have hnorm := IsUltrametricDist.norm_eq_of_add_norm_lt_max
      (x := g.derivative.eval a) (y := -(f.derivative.eval a))
      (by
        simpa only [sub_eq_add_neg, norm_neg] using
          (hgd.trans_lt hsmall).trans_le
            (le_max_right ‖g.derivative.eval a‖ ‖f.derivative.eval a‖))
    simpa only [norm_neg] using hnorm
  have hscale := norm_eval_sub_eval_eq_of_mul_norm_sub_lt_norm_derivative
    (f := g) (a := a) (b := z) (c := y) hg ha
    (by simpa only [hgD] using hz) (by simpa only [hgD] using hy)
  simpa only [hgD] using hscale

/-- Roots of two polynomials in one reference derivative ball satisfy a bound by their
direct coefficient difference when the first polynomial is close to the reference polynomial. -/
theorem norm_derivative_eval_mul_norm_sub_le_of_norm_coeff_sub_le_on_reference_ball
    {R : Type u} [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f g h : R[X]} {M ε η : ℝ} {a y z : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hy : M * ‖y - a‖ < ‖f.derivative.eval a‖)
    (hz : M * ‖z - a‖ < ‖f.derivative.eval a‖)
    (hfg : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε)
    (hsmall : ε < ‖f.derivative.eval a‖)
    (hgy : g.eval y = 0)
    (hhz : h.eval z = 0)
    (hgh : ∀ n : ℕ, ‖g.coeff n - h.coeff n‖ ≤ η) :
    ‖f.derivative.eval a‖ * ‖y - z‖ ≤ η := by
  have hz_unit : ‖z‖ ≤ 1 := by
    have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
    have hDM : ‖f.derivative.eval a‖ ≤ M :=
      norm_eval_le_of_norm_coeff_le
        (norm_derivative_coeff_le_of_norm_coeff_le hf) ha
    have hMpos : 0 < M :=
      (mul_nonneg hM (norm_nonneg (z - a))).trans_lt (hz.trans_le hDM)
    have hza : ‖z - a‖ < 1 :=
      (mul_lt_mul_iff_right₀ hMpos).mp
        (by simpa only [mul_one] using hz.trans_le hDM)
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (z - a) a).trans (max_le hza.le ha)
  have hcoeff : ∀ n : ℕ, ‖(g - h).coeff n‖ ≤ η := by
    intro n
    simpa only [coeff_sub] using hgh n
  calc
    ‖f.derivative.eval a‖ * ‖y - z‖ = ‖g.eval y - g.eval z‖ :=
      (norm_eval_sub_eval_eq_of_norm_coeff_sub_le hf ha hy hz hfg hsmall).symm
    _ = ‖(g - h).eval z‖ := by
      simp only [eval_sub, hgy, hhz, sub_zero, zero_sub, norm_neg]
    _ ≤ η := norm_eval_le_of_norm_coeff_le hcoeff hz_unit

/-- Coefficientwise perturbations bound the original derivative norm times the
root distance when both roots lie in the original strict derivative ball about a
center in the norm unit ball. -/
theorem norm_derivative_eval_mul_norm_sub_le_of_norm_coeff_sub_le
    {R : Type u} [SeminormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    {f g : R[X]} {M ε : ℝ} {a x y : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hx : f.eval x = 0)
    (hy : g.eval y = 0)
    (hxa : M * ‖x - a‖ < ‖f.derivative.eval a‖)
    (hya : M * ‖y - a‖ < ‖f.derivative.eval a‖)
    (hdiff : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε) :
    ‖f.derivative.eval a‖ * ‖x - y‖ ≤ ε := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hf' : ∀ n : ℕ, ‖f.derivative.coeff n‖ ≤ M :=
    norm_derivative_coeff_le_of_norm_coeff_le hf
  have hd : ‖f.derivative.eval a‖ ≤ M :=
    norm_eval_le_of_norm_coeff_le hf' ha
  have hMpos : 0 < M :=
    (mul_nonneg hM (norm_nonneg (y - a))).trans_lt (hya.trans_le hd)
  have hdist : ‖y - a‖ < 1 :=
    lt_of_mul_lt_mul_left
      (by simpa only [mul_one] using hya.trans_le hd) hMpos.le
  have hy_unit : ‖y‖ ≤ 1 := by
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (y - a) a).trans (max_le hdist.le ha)
  have hcoeff : ∀ n : ℕ, ‖(f - g).coeff n‖ ≤ ε := by
    intro n
    simpa only [coeff_sub] using hdiff n
  calc
    ‖f.derivative.eval a‖ * ‖x - y‖ =
        ‖f.derivative.eval a‖ * ‖y - x‖ := by rw [norm_sub_rev x y]
    _ = ‖f.eval y - f.eval x‖ :=
      (norm_eval_sub_eval_eq_of_mul_norm_sub_lt_norm_derivative hf ha hxa hya).symm
    _ = ‖(f - g).eval y‖ := by simp only [eval_sub, hx, hy, sub_zero]
    _ ≤ ε := norm_eval_le_of_norm_coeff_le hcoeff hy_unit

/-- A coefficient perturbation transports a root to the unique root in the
original strict derivative ball, with a sharp scaled distance bound, when the
original derivative is a unit. The proof applies the contraction mapping theorem
to the correction using that fixed unit derivative. -/
theorem exists_root_of_norm_coeff_sub_le_of_isUnit
    {R : Type u} [NormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
    [CompleteSpace R] {f g : R[X]} {M ε : ℝ} {a x : R}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hx : f.eval x = 0)
    (hxa : M * ‖x - a‖ < ‖f.derivative.eval a‖)
    (hdiff : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε)
    (hsmall : M * ε < ‖f.derivative.eval a‖ ^ 2)
    (hu : IsUnit (f.derivative.eval a)) :
    ∃ y : R, g.eval y = 0 ∧
      M * ‖y - a‖ < ‖f.derivative.eval a‖ ∧
      ‖f.derivative.eval a‖ * ‖x - y‖ ≤ ε ∧
      ∀ z : R, g.eval z = 0 →
        M * ‖z - a‖ < ‖f.derivative.eval a‖ → z = y := by
  classical
  let d : R := f.derivative.eval a
  let D : ℝ := ‖d‖
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hD : 0 < D :=
    (mul_nonneg hM (norm_nonneg (x - a))).trans_lt hxa
  have hDM : D ≤ M :=
    norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hf) ha
  have hMpos : 0 < M := hD.trans_le hDM
  have hε : 0 ≤ ε := (norm_nonneg (f.coeff 0 - g.coeff 0)).trans (hdiff 0)
  have hεD : ε < D := by
    by_contra h
    have hDε : D ≤ ε := le_of_not_gt h
    have hle : D * D ≤ M * ε := mul_le_mul hDM hDε hD.le hM
    exact (not_lt_of_ge hle) (by simpa only [pow_two] using hsmall)
  let r : ℝ := ε / D
  have hr : 0 ≤ r := div_nonneg hε hD.le
  have hr_one : r < 1 := (div_lt_one hD).2 hεD
  have hMr : M * r < D := by
    change M * (ε / D) < D
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hD).2 (by simpa only [pow_two] using hsmall)
  have hsub : ∀ z w : R, ‖z - w‖ ≤ max ‖z‖ ‖w‖ := by
    intro z w
    simpa only [sub_eq_add_neg, norm_neg] using
      (IsUltrametricDist.norm_add_le_max z (-w))
  have hunit : ∀ z : R, M * ‖z - a‖ < D → ‖z‖ ≤ 1 := by
    intro z hz
    have hza : ‖z - a‖ < 1 :=
      (mul_lt_mul_iff_right₀ hMpos).mp (by simpa only [mul_one] using hz.trans_le hDM)
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (z - a) a).trans (max_le hza.le ha)
  have hx_unit : ‖x‖ ≤ 1 := hunit x hxa
  have hball_unit : ∀ z : R, ‖z - x‖ ≤ r → ‖z‖ ≤ 1 := by
    intro z hz
    simpa only [sub_add_cancel] using
      (IsUltrametricDist.norm_add_le_max (z - x) x).trans
        (max_le (hz.trans hr_one.le) hx_unit)
  have hgf : ∀ n : ℕ, ‖g.coeff n - f.coeff n‖ ≤ ε := by
    intro n
    rw [norm_sub_rev]
    exact hdiff n
  have hgf_coeff : ∀ n : ℕ, ‖(g - f).coeff n‖ ≤ ε := by
    simpa only [coeff_sub] using hgf
  have hg : ∀ n : ℕ, ‖g.coeff n‖ ≤ M := by
    intro n
    calc
      ‖g.coeff n‖ = ‖(g.coeff n - f.coeff n) + f.coeff n‖ := by
        rw [sub_add_cancel]
      _ ≤ max ‖g.coeff n - f.coeff n‖ ‖f.coeff n‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ M := max_le ((hgf n).trans (hεD.le.trans hDM)) (hf n)
  have hgd : ‖g.derivative.eval a - d‖ ≤ ε := by
    have h := norm_eval_le_of_norm_coeff_le
      (norm_derivative_coeff_le_of_norm_coeff_le hgf_coeff) ha
    simpa only [derivative_sub, eval_sub] using h
  have hgD : ‖g.derivative.eval a‖ = D := by
    apply le_antisymm
    · calc
        ‖g.derivative.eval a‖ = ‖(g.derivative.eval a - d) + d‖ := by
          rw [sub_add_cancel]
        _ ≤ max ‖g.derivative.eval a - d‖ ‖d‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ ≤ D := max_le (hgd.trans hεD.le) le_rfl
    · by_contra h
      have hlt : ‖g.derivative.eval a‖ < D := lt_of_not_ge h
      have hdle : D ≤ max ‖g.derivative.eval a‖ ‖g.derivative.eval a - d‖ := by
        calc
          D = ‖g.derivative.eval a - (g.derivative.eval a - d)‖ := by
            change ‖d‖ = ‖g.derivative.eval a - (g.derivative.eval a - d)‖
            congr 1; ring
          _ ≤ max ‖g.derivative.eval a‖ ‖g.derivative.eval a - d‖ := hsub _ _
      exact (not_lt_of_ge hdle) (max_lt hlt (hgd.trans_lt hεD))
  -- The inverse is a unit inverse in R, not an inverse operation on R.
  obtain ⟨u, hu⟩ := hu
  let v : R := ↑(u⁻¹)
  have hvd : v * d = 1 := by
    change (↑(u⁻¹) : R) * f.derivative.eval a = 1
    rw [← hu]
    exact u.inv_val
  have hdv : d * v = 1 := by rw [mul_comm]; exact hvd
  have hnorm_one : ‖(1 : R)‖ = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hD)
    simpa only [mul_one] using (norm_mul d (1 : R)).symm
  have hvnorm : ‖v‖ = 1 / D := by
    apply (eq_div_iff (ne_of_gt hD)).2
    calc
      ‖v‖ * D = ‖v * d‖ := (norm_mul v d).symm
      _ = 1 := by rw [hvd, hnorm_one]
  -- Every point of the correction ball stays in the original strict ball.
  have hgeom : ∀ z : R, ‖z - x‖ ≤ r →
      M * ‖z - a‖ ≤ max (M * r) (M * ‖x - a‖) := by
    intro z hz
    have hza : ‖z - a‖ ≤ max r ‖x - a‖ := by
      calc
        ‖z - a‖ = ‖(z - x) + (x - a)‖ := by congr 1; ring
        _ ≤ max ‖z - x‖ ‖x - a‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max r ‖x - a‖ := max_le_max hz le_rfl
    simpa only [mul_max_of_nonneg _ _ hM] using
      (mul_le_mul_of_nonneg_left hza hM)
  have hball : ∀ z : R, ‖z - x‖ ≤ r → M * ‖z - a‖ < D := by
    intro z hz
    exact (hgeom z hz).trans_lt (max_lt hMr hxa)
  let C : ℝ := max (M * ‖x - a‖) (max ε (M * r))
  have hC : 0 ≤ C :=
    (mul_nonneg hM (norm_nonneg (x - a))).trans (le_max_left _ _)
  have hCD : C < D := max_lt hxa (max_lt hεD hMr)
  let q : ℝ := C / D
  have hq : 0 ≤ q := div_nonneg hC hD.le
  have hq_one : q < 1 := (div_lt_one hD).2 hCD
  let T : R → R := fun z => z - v * g.eval z
  have hT : ∀ z w : R, ‖z - x‖ ≤ r → ‖w - x‖ ≤ r →
      ‖T z - T w‖ ≤ q * ‖z - w‖ := by
    intro z w hz hw
    have hzw : ‖z - w‖ ≤ r := by
      calc
        ‖z - w‖ = ‖(z - x) - (w - x)‖ := by congr 1; ring
        _ ≤ max ‖z - x‖ ‖w - x‖ := hsub _ _
        _ ≤ r := max_le hz hw
    have hMrC : M * r ≤ C :=
      (le_max_right ε (M * r)).trans (le_max_right _ _)
    have hwa : M * ‖w - a‖ ≤ C :=
      (hgeom w hw).trans (max_le hMrC (le_max_left _ _))
    have hεC : ε ≤ C := (le_max_left ε (M * r)).trans (le_max_right _ _)
    have hzwC : M * ‖z - w‖ ≤ C :=
      (mul_le_mul_of_nonneg_left hzw hM).trans hMrC
    have hlinear := norm_eval_sub_sub_mul_le_max_of_norm_coeff_le
      hg ha (hball_unit z hz) (hball_unit w hw) hgd
    have hrem : ‖g.eval z - g.eval w - d * (z - w)‖ ≤ C * ‖z - w‖ :=
      hlinear.trans (mul_le_mul_of_nonneg_right
        (max_le hwa (max_le hεC hzwC)) (norm_nonneg (z - w)))
    have hidentity : T z - T w =
        -v * (g.eval z - g.eval w - d * (z - w)) := by
      dsimp only [T]
      calc
        z - v * g.eval z - (w - v * g.eval w) =
            (v * d) * (z - w) - v * (g.eval z - g.eval w) := by rw [hvd]; ring
        _ = -v * (g.eval z - g.eval w - d * (z - w)) := by ring
    calc
      ‖T z - T w‖ = ‖v‖ * ‖g.eval z - g.eval w - d * (z - w)‖ := by
        rw [hidentity, norm_mul, norm_neg]
      _ ≤ (1 / D) * (C * ‖z - w‖) := by
        rw [hvnorm]
        exact mul_le_mul_of_nonneg_left hrem (one_div_nonneg.mpr hD.le)
      _ = q * ‖z - w‖ := by dsimp only [q]; simp only [div_eq_mul_inv]; ring
  have hxres : ‖g.eval x‖ ≤ ε := by
    have h := norm_eval_le_of_norm_coeff_le hgf_coeff hx_unit
    simpa only [eval_sub, hx, sub_zero] using h
  have hTx : ‖T x - x‖ ≤ r := by
    have hidentity : T x - x = -(v * g.eval x) := by dsimp only [T]; ring
    calc
      ‖T x - x‖ = ‖v‖ * ‖g.eval x‖ := by rw [hidentity, norm_neg, norm_mul]
      _ ≤ (1 / D) * ε := by
        rw [hvnorm]
        exact mul_le_mul_of_nonneg_left hxres (one_div_nonneg.mpr hD.le)
      _ = r := by dsimp only [r]; simp only [div_eq_mul_inv]; ring
  have hTball : ∀ z : R, ‖z - x‖ ≤ r → ‖T z - x‖ ≤ r := by
    intro z hz
    have hxx : ‖x - x‖ ≤ r := by simpa only [sub_self, norm_zero] using hr
    have hbound : q * ‖z - x‖ ≤ r := by
      calc
        q * ‖z - x‖ ≤ 1 * ‖z - x‖ :=
          mul_le_mul_of_nonneg_right hq_one.le (norm_nonneg (z - x))
        _ ≤ r := by simpa only [one_mul] using hz
    calc
      ‖T z - x‖ = ‖(T z - T x) + (T x - x)‖ := by congr 1; ring
      _ ≤ max ‖T z - T x‖ ‖T x - x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le ((hT z x hz hxx).trans hbound) hTx
  let F : Metric.closedBall x r → Metric.closedBall x r := fun z =>
    ⟨T z, by
      change dist (T z) x ≤ r
      rw [dist_eq_norm]
      exact hTball z (by simpa only [Metric.mem_closedBall, dist_eq_norm] using z.property)⟩
  let : CompleteSpace (Metric.closedBall x r) :=
    Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let : Nonempty (Metric.closedBall x r) :=
    ⟨⟨x, by simpa only [Metric.mem_closedBall, dist_self] using hr⟩⟩
  have hF : ContractingWith (⟨q, hq⟩ : NNReal) F := by
    refine ⟨hq_one, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    change dist (T z) (T w) ≤ q * dist (z : R) (w : R)
    simp only [dist_eq_norm]
    exact hT z w
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using z.property)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using w.property)
  let y : Metric.closedBall x r := ContractingWith.fixedPoint F hF
  have hyfix : F y = y := hF.fixedPoint_isFixedPt
  have hyT : (y : R) - v * g.eval (y : R) = (y : R) := congrArg Subtype.val hyfix
  have hvg : v * g.eval (y : R) = 0 := by
    calc
      v * g.eval (y : R) = (y : R) - ((y : R) - v * g.eval (y : R)) := by ring
      _ = 0 := by rw [hyT, sub_self]
  have hy : g.eval (y : R) = 0 := by
    calc
      g.eval (y : R) = d * (v * g.eval (y : R)) := by rw [← mul_assoc, hdv, one_mul]
      _ = 0 := by rw [hvg, mul_zero]
  have hyball : M * ‖(y : R) - a‖ < D :=
    hball y (by simpa only [Metric.mem_closedBall, dist_eq_norm] using y.property)
  refine ⟨(y : R), hy, hyball, ?_, ?_⟩
  · exact norm_derivative_eval_mul_norm_sub_le_of_norm_coeff_sub_le
      hf ha hx hy hxa hyball hdiff
  · intro z hz hzball
    apply injOn_eval_of_mul_norm_sub_lt_norm_derivative hg ha
    · simpa only [Set.mem_ofPred_eq, hgD] using hzball
    · simpa only [Set.mem_ofPred_eq, hgD] using hyball
    · exact hz.trans hy.symm

/-- Over a complete ultrametric normed field, a coefficient perturbation transports
a root to the unique root in the original strict derivative ball, with a sharp
scaled distance bound. The strict ball inequality makes the original derivative
a unit, so no unit hypothesis is needed. Uniqueness applies to every root of the
perturbed polynomial in that ball, not only those satisfying the distance bound. -/
theorem exists_root_of_norm_coeff_sub_le
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {f g : K[X]} {M ε : ℝ} {a x : K}
    (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ M)
    (ha : ‖a‖ ≤ 1)
    (hx : f.eval x = 0)
    (hxa : M * ‖x - a‖ < ‖f.derivative.eval a‖)
    (hdiff : ∀ n : ℕ, ‖f.coeff n - g.coeff n‖ ≤ ε)
    (hsmall : M * ε < ‖f.derivative.eval a‖ ^ 2) :
    ∃ y : K, g.eval y = 0 ∧
      M * ‖y - a‖ < ‖f.derivative.eval a‖ ∧
      ‖f.derivative.eval a‖ * ‖x - y‖ ≤ ε ∧
      ∀ z : K, g.eval z = 0 →
        M * ‖z - a‖ < ‖f.derivative.eval a‖ → z = y := by
  have hM : 0 ≤ M := (norm_nonneg (f.coeff 0)).trans (hf 0)
  have hD : 0 < ‖f.derivative.eval a‖ :=
    (mul_nonneg hM (norm_nonneg (x - a))).trans_lt hxa
  have hunit : IsUnit (f.derivative.eval a) :=
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hD)
  exact exists_root_of_norm_coeff_sub_le_of_isUnit hf ha hx hxa hdiff hsmall hunit

end Polynomial
