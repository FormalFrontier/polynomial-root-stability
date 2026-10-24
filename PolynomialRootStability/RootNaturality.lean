/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Newton
public import PolynomialRootStability.NewtonNaturality
public import PolynomialRootStability.RootUniqueness

/-!
# Naturality of quantitative Newton lifting

An isometric field embedding carries a root obtained by quantitative Newton
lifting, together with the Newton limit and its bounds, to the target field.
The image root is unique among all target roots in the strict derivative-radius
ball. Only the source field is required to be complete.
-/

@[expose] public section

universe u v

open Filter
open scoped Topology

namespace Polynomial

/-- Quantitative Newton lifting commutes with an isometric field embedding.
Both conclusions have the full form of
`Polynomial.exists_root_tendsto_iterate_newtonMap`, with the target root equal
to the image of the source root. Target uniqueness ranges over the entire
strict derivative-radius ball, not merely the image of the source ball. -/
theorem exists_root_tendsto_iterate_newtonMap_map
    {K : Type u} {L : Type v}
    [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
    (ι : K →+* L) (hι : Isometry ι)
    {f : K[X]} {a₀ : K} (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ 1) (ha₀ : ‖a₀‖ ≤ 1)
    (hclose : ‖f.eval a₀‖ < ‖f.derivative.eval a₀‖ ^ 2) :
    ∃ a : K,
      (f.eval a = 0 ∧ ‖a‖ ≤ 1 ∧
        ‖a - a₀‖ = ‖f.eval a₀‖ / ‖f.derivative.eval a₀‖ ∧
        ‖a - a₀‖ < ‖f.derivative.eval a₀‖ ∧
        ‖f.derivative.eval a‖ = ‖f.derivative.eval a₀‖ ∧
        Tendsto (fun n : ℕ => f.newtonMap^[n] a₀) atTop (𝓝 a) ∧
        (∀ n : ℕ, ‖f.newtonMap^[n] a₀‖ ≤ 1 ∧
          f.derivative.eval (f.newtonMap^[n] a₀) ≠ 0 ∧
          ‖f.derivative.eval (f.newtonMap^[n] a₀)‖ = ‖f.derivative.eval a₀‖) ∧
        ∀ b : K, f.eval b = 0 → ‖b - a₀‖ < ‖f.derivative.eval a₀‖ → b = a) ∧
      ((f.map ι).eval (ι a) = 0 ∧ ‖ι a‖ ≤ 1 ∧
        ‖ι a - ι a₀‖ = ‖(f.map ι).eval (ι a₀)‖ /
          ‖(f.map ι).derivative.eval (ι a₀)‖ ∧
        ‖ι a - ι a₀‖ < ‖(f.map ι).derivative.eval (ι a₀)‖ ∧
        ‖(f.map ι).derivative.eval (ι a)‖ =
          ‖(f.map ι).derivative.eval (ι a₀)‖ ∧
        Tendsto (fun n : ℕ => (f.map ι).newtonMap^[n] (ι a₀)) atTop (𝓝 (ι a)) ∧
        (∀ n : ℕ, ‖(f.map ι).newtonMap^[n] (ι a₀)‖ ≤ 1 ∧
          (f.map ι).derivative.eval ((f.map ι).newtonMap^[n] (ι a₀)) ≠ 0 ∧
          ‖(f.map ι).derivative.eval ((f.map ι).newtonMap^[n] (ι a₀))‖ =
            ‖(f.map ι).derivative.eval (ι a₀)‖) ∧
        ∀ b : L, (f.map ι).eval b = 0 →
          ‖b - ι a₀‖ < ‖(f.map ι).derivative.eval (ι a₀)‖ → b = ι a) := by
  obtain ⟨a, ha⟩ := exists_root_tendsto_iterate_newtonMap hf ha₀ hclose
  refine ⟨a, ha, ?_⟩
  rcases ha with ⟨hroot, ha, hdist, hstrict, hderiv, hlim, hiter, huniq⟩
  have hnorm (x : K) : ‖ι x‖ = ‖x‖ := by
    simpa only [map_zero, dist_zero_right] using hι.dist_eq x 0
  have hnormsub (x y : K) : ‖ι x - ι y‖ = ‖x - y‖ := by
    rw [← map_sub, hnorm]
  have heval (x : K) : (f.map ι).eval (ι x) = ι (f.eval x) := by
    rw [eval_map_apply]
  have hD (x : K) : (f.map ι).derivative.eval (ι x) =
      ι (f.derivative.eval x) := by
    rw [derivative_map, eval_map_apply]
  have hDnorm (x : K) : ‖(f.map ι).derivative.eval (ι x)‖ =
      ‖f.derivative.eval x‖ := by
    rw [hD, hnorm]
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (by
      intro n
      have hn : ‖ι (n : K)‖ ≤ 1 := by
        rw [hnorm]
        exact IsUltrametricDist.norm_natCast_le_one K n
      simpa only [map_natCast] using hn)
  have hfL : ∀ n : ℕ, ‖(f.map ι).coeff n‖ ≤ 1 := by
    intro n
    simpa only [coeff_map, hnorm] using hf n
  have haL : ‖ι a‖ ≤ 1 := by simpa only [hnorm] using ha
  have hrootL : (f.map ι).eval (ι a) = 0 := by
    rw [heval, hroot, map_zero]
  have hstrictL : ‖ι a - ι a₀‖ < ‖(f.map ι).derivative.eval (ι a₀)‖ := by
    simpa only [hnormsub, hDnorm] using hstrict
  have hderivL : ‖(f.map ι).derivative.eval (ι a)‖ =
      ‖(f.map ι).derivative.eval (ι a₀)‖ := by
    simpa only [hDnorm] using hderiv
  have hiter_map (n : ℕ) : (f.map ι).newtonMap^[n] (ι a₀) =
      ι (f.newtonMap^[n] a₀) :=
    ((f.newtonMap_map_semiconj ι).iterate_right n a₀).symm
  refine ⟨hrootL, haL, ?_, hstrictL, hderivL, ?_, ?_, ?_⟩
  · simpa only [hnormsub, heval, hnorm, hDnorm] using hdist
  · simpa only [Function.comp_def, hiter_map] using
      (hι.continuous.tendsto a).comp hlim
  · intro n
    rcases hiter n with ⟨hi, hn, he⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hiter_map, hnorm] using hi
    · rw [hiter_map, hD]
      intro hzero
      apply hn
      apply hι.injective
      simpa only [map_zero] using hzero
    · simpa only [hiter_map, hDnorm] using he
  · intro b hbroot hbclose
    have htri (x y z : L) : ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖ := by
      simpa only [sub_add_sub_cancel] using
        IsUltrametricDist.norm_add_le_max (x - y) (y - z)
    have hba : ‖b - ι a‖ < ‖(f.map ι).derivative.eval (ι a₀)‖ := by
      refine lt_of_le_of_lt (htri b (ι a₀) (ι a)) (max_lt hbclose ?_)
      rw [norm_sub_rev]
      exact hstrictL
    exact eq_of_eval_eq_zero_of_mul_norm_sub_lt_norm_derivative hfL haL
      hbroot hrootL (by simpa only [one_mul, hderivL] using hba)

end Polynomial
