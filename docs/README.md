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
these counts describe the documented API, not every compiler-generated helper.

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

The generator reads the five Lean modules, `lean-toolchain`, `lakefile.toml`
and nine-package `lake-manifest.json` shipped in this checkout. The adapter
checks their complete inventory and SHA-256 hashes against its fixed source
binding, also recorded in [api-manifest.json](api-manifest.json). The manifest's
`analyzed_source_revision` is an inert binding label, not a Git lookup or a
required private reference. No development history is needed: the same inputs
can be read from a source archive or parentless release checkout.
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
REV=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
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

The `REV` value comes from the shipped manifest's fixed source-binding label.
The `example.invalid` URI is **only an inert native record-binding identifier**;
it is neither a verified remote address nor a source link shipped in API.md.
The generated Markdown links exclusively to local shipped `.lean` files. Omit
`--check` to regenerate `API.md` and `api-manifest.json`; `--check` compares
their bytes without writing. Source/pin bytes are compared against the frozen
eight-file digest inventory, even in a later documentation-only candidate.
No internal commit is fetched or required. The manifest records source hashes,
five raw native record hashes and the Markdown hash; it does not certify proofs
or apply automatically to changed source inputs. Temporary HTML, databases,
JavaScript, fonts and styles are not part of the shipped documentation.

The no-reference `bibPrepass` reports `INFO: reference page disabled`: this is
expected for the local declaration reference. Documentation generation is
optional and separate from the ordinary library build; reading the shipped
Markdown does not require doc-gen4 or its temporary output.

The Formal Frontier agents adapted Anchor's ideal-completion Markdown tooling
to this library's five-module, 23-theorem surface. The adapter copies the
project's Apache-2.0 docstrings and native displayed signatures only, not a
third-party website, implementation, asset bundle or dependency documentation.
Lean, mathlib and doc-gen4 retain their upstream attribution and rights.
