/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import PolynomialRootStability.Newton
public import PolynomialRootStability.NewtonNaturality
public import PolynomialRootStability.RootNaturality

/-!
# Newton iteration from the 3-adic field to the 3-adic complex field

For `X ^ 2 - 4`, Newton iteration starting at `1` converges to `-2` over the
3-adic field and to its image over the 3-adic complex field. The first iterate
is `5 / 2`, and the other root `2` lies outside the strict uniqueness ball.
The canonical embedding preserves membership in this radius-one ball and
identifies the source root with the root specified by a target uniqueness
certificate.
-/

@[expose] public section

universe u v

open Filter Polynomial
open scoped Topology

/-- A source root in the strict derivative-radius ball maps to the root
specified by a target uniqueness certificate. -/
example {K : Type u} {L : Type v} [NormedField K] [NormedField L]
    (ι : K →+* L) (hι : Isometry ι) (p : K[X]) (a₀ a : K) (b : L)
    (ha : p.eval a = 0)
    (ha_close : ‖a - a₀‖ < ‖p.derivative.eval a₀‖)
    (hb_unique : ∀ c : L, (p.map ι).eval c = 0 →
      ‖c - ι a₀‖ < ‖(p.map ι).derivative.eval (ι a₀)‖ → c = b) :
    ι a = b := by
  have hnorm (x : K) : ‖ι x‖ = ‖x‖ := by
    simpa only [dist_eq_norm, map_zero, sub_zero] using hι.dist_eq x 0
  apply hb_unique (ι a)
  · rw [eval_map_apply, ha, map_zero]
  · simpa only [← map_sub, derivative_map, eval_map_apply, hnorm] using ha_close

/-- The Newton trajectories of `X ^ 2 - 4` at `1` are compatible with the
canonical embedding of the 3-adic field into the 3-adic complex field. -/
example [Fact (Nat.Prime 3)] :
    let p : (Padic 3)[X] := X ^ 2 - C 4
    let ι : Padic 3 →+* PadicComplex 3 := algebraMap (Padic 3) (PadicComplex 3)
    Isometry ι ∧
      (∀ n : ℕ, ‖p.coeff n‖ ≤ 1) ∧
      ‖(1 : Padic 3)‖ = 1 ∧
      IsUnit (p.derivative.eval (1 : Padic 3)) ∧
      ‖p.eval (1 : Padic 3)‖ = (1 / 3 : ℝ) ∧
      ‖p.derivative.eval (1 : Padic 3)‖ = 1 ∧
      ‖p.eval (1 : Padic 3)‖ < ‖p.derivative.eval (1 : Padic 3)‖ ^ 2 ∧
      Function.Semiconj ι (p.newtonMap : Padic 3 → Padic 3)
        ((p.map ι).newtonMap : PadicComplex 3 → PadicComplex 3) ∧
      p.newtonMap (1 : Padic 3) = (5 / 2 : Padic 3) ∧
      p.newtonMap (1 : Padic 3) ≠ 1 ∧
      p.eval (-2 : Padic 3) = 0 ∧
      ‖(-2 : Padic 3) - 1‖ = (1 / 3 : ℝ) ∧
      (-2 : Padic 3) ∈ Metric.ball (1 : Padic 3) 1 ∧
      p.eval (2 : Padic 3) = 0 ∧
      (2 : Padic 3) ∉ Metric.ball (1 : Padic 3) 1 ∧
      (∀ b : Padic 3, p.eval b = 0 →
        b ∈ Metric.ball (1 : Padic 3) 1 → b = -2) ∧
      (p.map ι).eval (ι (-2)) = 0 ∧
      ι (-2) ∈ Metric.ball (ι 1) 1 ∧
      (∀ b : PadicComplex 3, (p.map ι).eval b = 0 →
        b ∈ Metric.ball (ι 1) 1 → b = ι (-2)) ∧
      (∀ x : Padic 3,
        ι x ∈ Metric.ball (ι 1) 1 ↔ x ∈ Metric.ball (1 : Padic 3) 1) ∧
      Tendsto (fun n : ℕ => p.newtonMap^[n] (1 : Padic 3)) atTop (𝓝 (-2)) ∧
      Tendsto (fun n : ℕ => (p.map ι).newtonMap^[n] (ι 1)) atTop (𝓝 (ι (-2))) := by
  let p : (Padic 3)[X] := X ^ 2 - C 4
  let ι : Padic 3 →+* PadicComplex 3 := algebraMap (Padic 3) (PadicComplex 3)
  have hnorm (x : Padic 3) : ‖ι x‖ = ‖x‖ := by
    exact PadicComplex.norm_extends' (p := 3) x
  have hι : Isometry ι := by
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]
  have htwo : ‖(2 : Padic 3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 2)).2 (by norm_num)
  have hfour : ‖(4 : Padic 3)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff (p := 3) (n := 4)).2 (by norm_num)
  have hthree : ‖(3 : Padic 3)‖ = (1 / 3 : ℝ) := by
    simpa only [Nat.cast_ofNat, one_div] using (Padic.norm_p (p := 3))
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ 1 := by
    intro n
    by_cases h0 : n = 0
    · subst n
      simp [p, coeff_X_pow, hfour]
    by_cases h2 : n = 2
    · subst n
      simp [p, coeff_X_pow]
    · simp [p, coeff_X_pow, coeff_C, h0, h2]
  have heval : p.eval (1 : Padic 3) = -3 := by
    norm_num [p]
  have hderiv : p.derivative.eval (1 : Padic 3) = 2 := by
    norm_num [p, derivative_pow]
  have herror : ‖p.eval (1 : Padic 3)‖ = (1 / 3 : ℝ) := by
    rw [heval, norm_neg, hthree]
  have hderivnorm : ‖p.derivative.eval (1 : Padic 3)‖ = 1 := by
    rw [hderiv, htwo]
  have hunit : IsUnit (p.derivative.eval (1 : Padic 3)) := by
    rw [hderiv]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hclose : ‖p.eval (1 : Padic 3)‖ < ‖p.derivative.eval (1 : Padic 3)‖ ^ 2 := by
    rw [herror, hderivnorm]
    norm_num
  have hsem : Function.Semiconj ι (p.newtonMap : Padic 3 → Padic 3)
      ((p.map ι).newtonMap : PadicComplex 3 → PadicComplex 3) :=
    p.newtonMap_map_semiconj ι
  have hfirst : p.newtonMap (1 : Padic 3) = (5 / 2 : Padic 3) := by
    norm_num [p, newtonMap_apply, Ring.inverse_eq_inv, derivative_pow]
  have hfirst_ne : p.newtonMap (1 : Padic 3) ≠ 1 := by
    rw [hfirst]
    norm_num
  have hroot : p.eval (-2 : Padic 3) = 0 := by
    norm_num [p]
  have hminus : ‖(-2 : Padic 3) - 1‖ = (1 / 3 : ℝ) := by
    have hsub : (-2 : Padic 3) - 1 = -3 := by ring
    rw [hsub, norm_neg, hthree]
  have hminus_lt : ‖(-2 : Padic 3) - 1‖ < 1 := by
    rw [hminus]
    norm_num
  have hroot_ball : (-2 : Padic 3) ∈ Metric.ball (1 : Padic 3) 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hminus_lt
  have hother_root : p.eval (2 : Padic 3) = 0 := by
    norm_num [p]
  have hother_ball : (2 : Padic 3) ∉ Metric.ball (1 : Padic 3) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    norm_num
  obtain ⟨a, ⟨_, _, _, _, hsource_deriv, hsource_limit, _, hsource_unique⟩,
      ⟨_, _, _, _, _, _, _, htarget_unique⟩⟩ :=
    Polynomial.exists_root_tendsto_iterate_newtonMap_map
      ι hι (f := p) hcoeff (by simp) hclose
  have ha : a = (-2 : Padic 3) :=
    (hsource_unique (-2) hroot (by simpa only [hderivnorm] using hminus_lt)).symm
  subst a
  have hsource_ball_unique : ∀ b : Padic 3, p.eval b = 0 →
      b ∈ Metric.ball (1 : Padic 3) 1 → b = -2 := by
    intro b hb hball
    apply Polynomial.eq_of_eval_eq_zero_of_mul_norm_sub_lt_norm_derivative
      (y := (-2 : Padic 3)) hcoeff
      (by simpa only [norm_neg, htwo] using (le_refl (1 : ℝ))) hb hroot
    rw [one_mul, hsource_deriv, hderivnorm]
    calc
      ‖b - (-2 : Padic 3)‖ ≤ max ‖b - 1‖ ‖(1 : Padic 3) - (-2)‖ := by
        simpa only [sub_add_sub_cancel] using
          IsUltrametricDist.norm_add_le_max (b - 1) ((1 : Padic 3) - (-2))
      _ < 1 := max_lt
        (by simpa only [Metric.mem_ball, dist_eq_norm] using hball)
        (by rw [norm_sub_rev]; exact hminus_lt)
  have htderivnorm : ‖(p.map ι).derivative.eval (ι 1)‖ = 1 := by
    rw [derivative_map, eval_map_apply, hnorm, hderivnorm]
  have htroot : (p.map ι).eval (ι (-2)) = 0 := by
    rw [eval_map_apply, hroot, map_zero]
  have htminus_lt : ‖ι (-2) - ι 1‖ < 1 := by
    simpa only [← map_sub, hnorm] using hminus_lt
  have htroot_ball : ι (-2) ∈ Metric.ball (ι 1) 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using htminus_lt
  have htarget_ball_unique : ∀ b : PadicComplex 3, (p.map ι).eval b = 0 →
      b ∈ Metric.ball (ι 1) 1 → b = ι (-2) := by
    intro b hb hball
    apply htarget_unique b hb
    simpa only [Metric.mem_ball, dist_eq_norm, htderivnorm] using hball
  have hball_iff : ∀ x : Padic 3,
      ι x ∈ Metric.ball (ι 1) 1 ↔ x ∈ Metric.ball (1 : Padic 3) 1 := by
    intro x
    simp only [Metric.mem_ball, hι.dist_eq]
  have hiter (n : ℕ) : ι (p.newtonMap^[n] (1 : Padic 3)) =
      (p.map ι).newtonMap^[n] (ι 1) :=
    hsem.iterate_right n (1 : Padic 3)
  have htarget_limit : Tendsto (fun n : ℕ => (p.map ι).newtonMap^[n] (ι 1))
      atTop (𝓝 (ι (-2))) := by
    have hlim := (hι.continuous.tendsto (-2)).comp hsource_limit
    simpa only [Function.comp_def, hiter] using hlim
  exact ⟨hι, hcoeff, norm_one, hunit, herror, hderivnorm, hclose, hsem,
    hfirst, hfirst_ne, hroot, hminus, hroot_ball, hother_root, hother_ball,
    hsource_ball_unique, htroot, htroot_ball, htarget_ball_unique, hball_iff,
    hsource_limit, htarget_limit⟩

example [Fact (Nat.Prime 3)] :
    let p : (Padic 3)[X] := X ^ 2 - C 4
    Function.Semiconj (Algebra.ofId (Padic 3) (PadicComplex 3))
      (p.newtonMap : Padic 3 → Padic 3)
      (p.newtonMap : PadicComplex 3 → PadicComplex 3) := by
  exact (X ^ 2 - C 4 : (Padic 3)[X]).newtonMap_semiconj
    (Algebra.ofId (Padic 3) (PadicComplex 3))
