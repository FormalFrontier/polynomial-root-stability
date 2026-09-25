/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import PolynomialRootStability.Krasner
public import PolynomialRootStability.Normalization

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
-/
