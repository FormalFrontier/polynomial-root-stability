# Native Markdown API reference

[API.md](API.md) is a locally generated, self-contained reference to all **23
named public theorems defined here**. Fourteen production theorems belong to
`PolynomialRootStability.Krasner` (11) and
`PolynomialRootStability.Normalization` (three). Nine *publicly named* checked-use
client theorems belong to the separate `PolynomialRootStabilityTest.Krasner`
(two) and `PolynomialRootStabilityTest.Normalization` (seven) leaves. The
`PolynomialRootStability` root reexports both production leaves and defines no
declarations of its own. The clients are **not** additional production theorems
and the root does not import either test leaf. Imported mathlib declarations and
compiler-generated helpers are not substituted for these 23 named results;
the full raw-body/helper audit remains separate.

The reference preserves the *displayed* native doc-gen4 signature, including
implicit universes, parameters and instances, plus the exact source docstring
and a link to its source line in this checkout. Independent universes for base
and ambient fields are visible; the finite separation theorems lack an
`IsKrasner` assumption. The theorems about nearby root-field equality require
splitting in one fixed ambient extension, equal `natDegree` and separability of
the reference; normalized coefficients require a **nonzero comparison** whereas
the ordinary-coefficient theorem derives comparison nonzeroness. See the
[mathematical overview](../README.md) for limitations: these are root-generated
intermediate fields, not canonical splitting-field equivalences or a claim of
complete coverage of a motivating source. Native display signatures may
abbreviate imported names and do not include proof bodies.

## Reproduction from pinned inputs

The historical **accepted mathematical input** is commit
`8c48c711e29f8f8fe8db633ee065ea4dd8e78081`, tree
`c2324d38fa6caaa5e05cc7c702067b93c6bfdc9f`. These are provenance labels;
**you do not need that Git object or internal development history**. Analyze
the five Lean modules, `lean-toolchain`, `lakefile.toml` and nine-package
`lake-manifest.json` shipped in this checkout. The adapter verifies their
complete inventory and exact reviewed SHA-256 hashes, also recorded in the
manifest. This works in a source archive or parentless release checkout.
This is Lean `v4.34.0-rc2` with mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. Obtain unchanged
`leanprover/doc-gen4` at `97d4ecdfc8e09e7f511724c25e303d448de6a3db`
(tree `ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`) in a **separate**
checkout with its committed manifest. Build its core-only executable with
`lake build doc-gen4`; do not add it to this library's pinned dependencies.
If the native C compiler is not on `PATH`, prepend the directory containing
`elan which lean` to the tool build's process `PATH`. The tool's own build does
not depend on mathlib. Set `LEAN_NUM_THREADS=2` only as a Lean runtime setting,
not as a guaranteed total process or memory limit.

From this repository root, first fetch the matching precompiled mathlib cache
**successfully before building**, then check the production root and both test
leaves. For documentation, run `single` in *this project's* `lake env`, so the
separate pinned executable resolves the actual library imports:

```bash
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
lake env lean -T0 PolynomialRootStabilityTest/Krasner.lean
lake env lean -T0 PolynomialRootStabilityTest/Normalization.lean
TOOL=/absolute/path/to/doc-gen4/.lake/build/bin/doc-gen4
OUT=/fresh/temporary/polynomial-docs
REV=8c48c711e29f8f8fe8db633ee065ea4dd8e78081
mkdir -p "$OUT/build" "$OUT/render"
for module in PolynomialRootStability.Krasner PolynomialRootStability.Normalization \
              PolynomialRootStability PolynomialRootStabilityTest.Krasner \
              PolynomialRootStabilityTest.Normalization; do
  path="${module//.//}.lean"
  lake env "$TOOL" single --build "$OUT/build" "$module" "$OUT/build/api.db" \
    "https://example.invalid/commit/$REV/$path"
done
"$TOOL" bibPrepass --build "$OUT/render" --none
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/api.db" PolynomialRootStability.Krasner \
  PolynomialRootStability.Normalization PolynomialRootStability \
  PolynomialRootStabilityTest.Krasner PolynomialRootStabilityTest.Normalization
python3 -B scripts/test_generate_api.py
python3 -B scripts/generate_api.py --native-data "$OUT/render/doc-data" --source-revision "$REV" --check
```

The `REV` value is the fixed historical mathematical-input label, not a Git
lookup. The `example.invalid` URI is **only an inert native record-binding identifier**;
it is neither a verified remote address nor a source link shipped in API.md.
The generated Markdown links exclusively to local shipped `.lean` files. Omit
`--check` to regenerate `API.md` and `api-manifest.json`; `--check` compares
their bytes without writing. Source/pin bytes are compared against the frozen
eight-file digest inventory, even in a later documentation-only candidate.
No internal commit is fetched or required. The release acceptance record binds
the exact final commit/tree to these source hashes and this generated reference;
these historical labels do not certify a future changed snapshot. The manifest records
those hashes, five **raw** native record hashes and the Markdown hash, but it
cannot authenticate its own inputs or certify proofs. Keep the actual native
database, five raw declaration records, native command receipts and diagnostic
logs separately for independent review; temporary HTML, database, JavaScript,
fonts and styles are not part of the shipped documentation.

In one fresh-checkout worker-b run on September 25, 2026, the matching 8,892
mathlib artifacts were fetched successfully (50.510 s elapsed), the pinned
doc-gen4 executable built separately (103.453 s), and the library's warning-fatal
default build completed 2,582 jobs (9.105 s). Both public test leaves compiled
with `lean -T0` (2.249 and 2.537 s). All five `single` commands completed;
the native database has five modules and 23 named declarations. The no-reference
`bibPrepass` reports `INFO: reference page disabled`; no warning is hidden or
relabelled. These timings are local context, not a portable performance claim.

This bounded adapter adapts Anchor's unaccepted ideal-completion Markdown recipe
at `f0c8c34386109116e4912fb425a8ad15d9dc42a4` for this library's **actual**
five-module/23-theorem surface; worker-b performed this adaptation. It copies the
project's Apache-2.0 docstrings and native displayed signatures only, not a
third-party website, implementation, asset bundle or dependency documentation.
Lean/mathlib and doc-gen4 retain their upstream attribution and rights. Neither
the previous recipe nor this candidate has independent review or release
acceptance by virtue of generation, builds or this documentation.
