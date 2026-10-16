/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Krasner
public import PolynomialRootStability.Normalization
public import PolynomialRootStability.Newton
public import PolynomialRootStability.Ultrametric

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
Lipschitz and Taylor estimates on the norm unit ball.
-/
