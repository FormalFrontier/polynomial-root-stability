# Credits

Authors: Formal Frontier Agents. License: Apache-2.0; see [LICENSE](LICENSE).
The collective author credit does not assert copyright ownership.

## Root-generated-field stability

The mathematical development, module organization, named clients and API
documentation are authored collectively by Formal Frontier Agents. The Markdown
adapter builds on the documentation-tooling design of the ideal-completion
library.

Mathematical motivation includes Neukirch, Schmidt and Wingberg,
*Cohomology of Number Fields*, corrected second edition 2.3 (May 2020), §12.1.1.
The fixed-ambient-field results have explicit splitting and equal-degree
hypotheses; no passage-to-theorem identification or complete source coverage is
asserted. The proofs reuse Mathlib's Krasner lemma and polynomial-root continuity.

## Polynomial Newton iteration

The polynomial Newton material is authored collectively by Formal Frontier
Agents. It comprises coefficient-controlled ultrametric polynomial estimates,
the field-target quotient formula, quantitative lifting and convergence, and
examples. The proof restricts the stock Newton map to the closed ball of radius
`δ / d` and proves contraction with constant `δ / d²`, using derivative stability,
a Lipschitz bound and a quadratic Taylor remainder on the norm unit ball. The
coefficient estimates use polynomial `divX` induction at seminormed-ring
generality; they require neither completeness nor a norm-one hypothesis.

The statement and 2-adic example are motivated by I. B. Fesenko and S. V. Vostokov,
*Local Fields and Their Extensions*, second edition (2002), Chapter II, §1,
Corollary 3 and Exercise 1. Newton iteration reuses Mathlib's
`Polynomial.newtonMap` by Antoine Chambert-Loir and Oliver Nash and stock function
iteration. The quantitative statement extends the scope of Mathlib's p-adic
`hensels_lemma`, following Robert Y. Lewis's formalization and Keith Conrad's
exposition. No upstream Newton or Hensel proof is copied.

The contraction argument uses Mathlib’s Banach fixed point API by Rohan Mitta,
Kevin Buzzard, Alistair Tucker, Johannes Hölzl and Yury Kudryashov. The ultrametric
norm API is due to Yakov Pechersky and David Loeffler. Upstream author notices
and licenses remain with Mathlib.

The 2-adic input calculation uses Mathlib's p-adic numbers and integers,
including their complete ultrametric field structure, integer norm bound and
valuation-integer unit criterion. Relevant p-adic development is due to Robert
Y. Lewis, Mario Carneiro and Johan Commelin.

Lean, Mathlib and doc-gen4 retain their upstream credit and licenses. No source
PDFs, scans, figures or substantial source excerpts are bundled. AI agents
assisted with proofs, tests and prose; Lean checks proofs, while mathematical
review assesses the statements and their meaning.
