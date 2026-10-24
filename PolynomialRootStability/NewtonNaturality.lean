/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Dynamics.Newton
public import Mathlib.Logic.Function.Iterate

/-!
# Naturality of the Newton map

The Newton map commutes with algebra homomorphisms that reflect units. The same
compatibility holds when the coefficients of a polynomial are mapped by a
unit-reflecting ring homomorphism. Semiconjugacy of all iterates follows from
`Function.Semiconj.iterate_right`.
-/

@[expose] public section

universe u v w

namespace Ring

/-- A homomorphism that reflects units commutes with the inverse extended by zero. -/
theorem map_inverse_of_isUnit_reflecting {M : Type u} {N : Type v} {F : Type w}
    [MonoidWithZero M] [MonoidWithZero N] [FunLike F M N]
    [MonoidWithZeroHomClass F M N] (f : F)
    (hf : ∀ a, IsUnit (f a) → IsUnit a) (a : M) :
    f (inverse a) = inverse (f a) := by
  by_cases ha : IsUnit a
  · rcases ha with ⟨u, rfl⟩
    rw [inverse_unit]
    exact (inverse_unit (Units.map (f : M →* N) u)).symm
  · rw [inverse_non_unit _ ha, map_zero,
      inverse_non_unit _ (fun h => ha (hf a h))]

/-- A local homomorphism commutes with the inverse extended by zero. -/
theorem map_inverse {M : Type u} {N : Type v} {F : Type w}
    [MonoidWithZero M] [MonoidWithZero N] [FunLike F M N]
    [MonoidWithZeroHomClass F M N] (f : F) [IsLocalHom f] (a : M) :
    f (inverse a) = inverse (f a) :=
  map_inverse_of_isUnit_reflecting f (fun a h => IsUnit.of_map f a h) a

end Ring

namespace Polynomial

/-- A unit-reflecting algebra homomorphism semiconjugates the Newton maps of a
polynomial on its source and target algebras. -/
theorem newtonMap_semiconj {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (p : R[X]) (φ : A →ₐ[R] B) [IsLocalHom φ] :
    Function.Semiconj φ (p.newtonMap : A → A) (p.newtonMap : B → B) := by
  intro x
  simp only [newtonMap_apply, map_sub, map_mul, Ring.map_inverse, aeval_algHom_apply]

/-- Mapping coefficients by a unit-reflecting ring homomorphism semiconjugates
the corresponding Newton maps. -/
theorem newtonMap_map_semiconj {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (p : R[X]) (ι : R →+* S) [IsLocalHom ι] :
    Function.Semiconj ι (p.newtonMap : R → R) ((p.map ι).newtonMap : S → S) := by
  intro x
  simp only [newtonMap_apply, coe_aeval_eq_eval, derivative_map, eval_map_apply,
    map_sub, map_mul, Ring.map_inverse]

end Polynomial
