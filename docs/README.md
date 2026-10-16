# Historical root-field API snapshot

[API.md](API.md) is the preserved, locally generated reference for the historical
Krasner/Normalization surface: **23 named public theorems**. Its original bytes,
[manifest](api-manifest.json), eight input hashes and generator binding are unchanged.
The current checkout additionally exports `PolynomialRootStability.Newton` and
`PolynomialRootStability.Ultrametric`. Both are outside this snapshot; use their
[Newton](../PolynomialRootStability/Newton.lean) and
[Ultrametric](../PolynomialRootStability/Ultrametric.lean) sources and the
[current mathematical overview](../README.md) for its statement and status.
The snapshot is not a fresh documentation or proof check of the current pins.

Within the historical snapshot, fourteen production theorems belong to
`PolynomialRootStability.Krasner` (11) and
`PolynomialRootStability.Normalization` (three). Nine *publicly named* checked-use
client theorems belong to the separate `PolynomialRootStabilityTest.Krasner`
(two) and `PolynomialRootStabilityTest.Normalization` (seven) leaves. The
historical `PolynomialRootStability` root reexports both production leaves and
defines no declarations of its own. The current root reexports Newton and Ultrametric as well.
The clients are **not** additional production theorems
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

## Reproduction from historical pinned inputs

Run the preserved generator only in a historical checkout or source archive
containing the exact eight inputs listed by `api-manifest.json`: the five Lean
modules, `lean-toolchain`, `lakefile.toml` and nine-package `lake-manifest.json`.
The current checkout has changed those inputs (including the mathlib pin and
root exports), so generation against it must fail closed rather than silently
rebinding the historical snapshot. The commands below refer to that matching
historical source tree, not the current branch. The adapter
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

From the matching historical repository root, first fetch the matching
precompiled mathlib cache **successfully before building**, then check the
production root and both test leaves. For documentation, run `single` in that
historical project's `lake env`, so the separate pinned executable resolves
the actual library imports:

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
eight-file digest inventory. It is deliberately not rebound to current sources.
No internal commit is fetched or required. The manifest records source hashes,
five raw native record hashes and the Markdown hash; it does not certify proofs
or apply automatically to changed source inputs. Temporary HTML, databases,
JavaScript, fonts and styles are not part of the shipped documentation.

The no-reference `bibPrepass` reports `INFO: reference page disabled`: this is
expected for the local declaration reference. Documentation generation is
optional and separate from the ordinary library build; reading the shipped
Markdown does not require doc-gen4 or its temporary output.

Formal Frontier Agents adapted the ideal-completion library's Markdown tooling
to this library's five-module, 23-theorem surface. The adapter copies the
project's Apache-2.0 docstrings and native displayed signatures only, not a
third-party website, implementation, asset bundle or dependency documentation.
Lean, mathlib and doc-gen4 retain their upstream attribution and rights.

## Current compatibility maintenance

The current library retains all 23 named root-field theorem/client interfaces,
while moving to mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5` on the same
Lean `v4.34.0-rc2` toolchain. It adds explicit Lake implicit-variable/linter
options and exposed public sections. The Normalization universe declarations
are now explicit at file scope. These changes do not regenerate this snapshot.
Its displayed mathematical signatures and declaration docstrings remain useful,
but its configuration hashes and two-module root description are historical.
The adapter’s data tests check the preserved manifest/Markdown binding and reject
current inputs as a mismatch; they are not Lean or fresh native-record checks.
