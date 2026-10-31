/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.CoefficientPerturbation
public import PolynomialRootStability.Krasner
public import PolynomialRootStability.Normalization
public import PolynomialRootStability.Newton
public import PolynomialRootStability.RootUniqueness
public import PolynomialRootStability.ResultantFactorization
public import PolynomialRootStability.ScaleRoots
public import PolynomialRootStability.Ultrametric
public import PolynomialRootStability.Valuation

/-!
# Polynomial root stability

Import this module for all the root-generated-field stability results. For
monic polynomials, see `IsKrasner.exists_pos_adjoin_rootSet_eq_of_monic_separable`;
for arbitrary nonzero separable polynomials, use
`IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable` or its scale-invariant
normalized-coefficient variant. Both the reference and comparison polynomial
must split in a fixed ambient `IsKrasner K L` normed extension and have equal
`natDegree`. The comparison polynomial is proved separable in the resulting
coefficient neighbourhood.

The Newton module additionally proves quantitative root lifting and convergence
of Mathlib's polynomial Newton iterates in a complete ultrametric normed field.
The ultrametric module provides coefficient-controlled evaluation, derivative,
Lipschitz and Taylor estimates on the norm unit ball. The valuation module gives
coefficient-controlled value scaling, derivative-value stability and injectivity
on strict derivative balls over commutative rings, with values in any linearly
ordered commutative monoid with zero.

The root-scaling module proves joint continuity of scaled evaluation over a
topological semiring and scale-relative nonvanishing over any normed field for
polynomials with no zero of norm at least one.
-/
