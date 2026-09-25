#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded native doc-gen4 Markdown adapter for polynomial-root-stability.

Adapted from Anchor's ideal-completion documentation recipe by worker-b.
This checks the fixed public surface and source bytes, not proofs or native provenance.
The separately retained native records and commands remain necessary review inputs.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
SOURCE = "8c48c711e29f8f8fe8db633ee065ea4dd8e78081"
SOURCE_TREE = "c2324d38fa6caaa5e05cc7c702067b93c6bfdc9f"
# Reviewed mathematical input bytes, independent of development Git ancestry.
# SOURCE/TREE remain historical provenance labels, not remotely fetched inputs.
# The exact release commit/tree is bound by the external acceptance record.
SOURCE_INPUT_SHA256 = {
    "PolynomialRootStability.lean": "b57d287c62e1ac0b7cf4ff8afb4078876abed14d6cf3407a288a468017a6bb67",
    "PolynomialRootStability/Krasner.lean": "b96e20b42fcd28dc238eb45f3f6fe145a69ddad12fbef40ba95d3a8defcc9854",
    "PolynomialRootStability/Normalization.lean": "2400a99caa0019de6834e848f6cf55f84efddc919d9ba2dcf93ee968525ad421",
    "PolynomialRootStabilityTest/Krasner.lean": "d73f1797dacc82b88f6500639c884d9bf0c6a2182dfaada6d03514a266078a63",
    "PolynomialRootStabilityTest/Normalization.lean": "73cf12efefc974c22969d8570f22d40a04197275fcdd454b2996a77185031218",
    "lake-manifest.json": "b2e6a11ce14954af0eb88b270acc06a3dea36236ed1e8b92cf8a0ed1e5ba0c85",
    "lakefile.toml": "dc91923a50fbe38a213c78cb54582f3a6eacf4a08fbd2a4b82e231f25a8ecc81",
    "lean-toolchain": "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
}
MODULES = (
    "PolynomialRootStability.Krasner",
    "PolynomialRootStability.Normalization",
    "PolynomialRootStability",
    "PolynomialRootStabilityTest.Krasner",
    "PolynomialRootStabilityTest.Normalization",
)
INPUTS = tuple(module.replace(".", "/") + ".lean" for module in MODULES) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
)
PRODUCTION = {
    MODULES[0]: (
        "IsKrasner.adjoin_le_adjoin_of_forall_exists_close",
        "IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_forall_exists_close",
        "IsKrasner.exists_pos_le_norm_sub_of_isConjRoot",
        "IsKrasner.exists_pos_le_norm_sub_of_distinct_roots",
        "IsKrasner.exists_pos_root_continuity_bound_lt_of_monic",
        "IsKrasner.exists_pos_two_add_root_continuity_bounds_lt_of_monic",
        "IsKrasner.separable_of_norm_coeff_sub_lt",
        "IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt",
        "IsKrasner.adjoin_rootSet_eq_of_norm_coeff_sub_lt",
        "IsKrasner.exists_pos_adjoin_rootSet_le_of_monic_separable",
        "IsKrasner.exists_pos_adjoin_rootSet_eq_of_monic_separable",
    ),
    MODULES[1]: (
        "IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable_normalized",
        "Polynomial.exists_pos_norm_mul_leadingCoeff_inv_coeff_sub_lt",
        "IsKrasner.exists_pos_adjoin_rootSet_eq_of_separable",
    ),
}
CLIENTS = {
    MODULES[3]: (
        "PolynomialRootStabilityTest.direct_distinct_root_separation",
        "PolynomialRootStabilityTest.direct_monic_stability",
    ),
    MODULES[4]: (
        "PolynomialRootStabilityTest.aggregate_ordinary_stability",
        "PolynomialRootStabilityTest.aggregate_normalized_stability",
        "PolynomialRootStabilityTest.aggregate_scalar_normalized_invariance",
        "PolynomialRootStabilityTest.rational_constant_normalization",
        "PolynomialRootStabilityTest.padic_constant_stability",
        "PolynomialRootStabilityTest.padic_constant_rootSet_empty",
        "PolynomialRootStabilityTest.padic_nonmonic_linear_stability",
    ),
}
EXPECTED = {**PRODUCTION, MODULES[2]: (), **CLIENTS}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Extract visible header text without discarding implicit arguments."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes), "duplicate native header attribute")
        require(set(attributes) <= {"class", "href"}, "active/unknown header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected header link")
        require("href" not in attributes or not re.match(r"(?i)\s*(?:javascript|data):", attributes["href"]),
                "active header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def check_signature(module, name, text):
    """Check source-specific essential binders in addition to retaining all text."""
    first = EXPECTED[MODULES[0]]
    if module == MODULES[0] and name in first[:4]:
        binders = ("{K : Type u_1}", "{L : Type u_2}", "[Field K]",
                   "[NormedField L]", "[Algebra K L]")
        has_krasner = name in first[:2]
    elif module == MODULES[0]:
        binders = ("{K₀ : Type u_3}", "{L₀ : Type u_4}", "[NormedField K₀]",
                   "[NormedField L₀]", "[NormedAlgebra K₀ L₀]")
        has_krasner = name in first[7:]
    elif name == "Polynomial.exists_pos_norm_mul_leadingCoeff_inv_coeff_sub_lt":
        binders = ("{K : Type u}", "[NormedField K]", "(hf0 : f ≠ 0)")
        has_krasner = False
    elif module == MODULES[1] or (module == MODULES[4] and name in CLIENTS[MODULES[4]][:3]):
        binders = ("{K : Type u}", "{L : Type v}", "[NormedField K]",
                   "[NormedField L]", "[NormedAlgebra K L]", "(hf0 : f ≠ 0)")
        has_krasner = True
    elif module == MODULES[3]:
        binders = ("{K : Type u}", "{L : Type v}", "[NormedField L]", "[Algebra K L]") \
            if name.endswith("direct_distinct_root_separation") else \
            ("{K : Type u}", "{L : Type v}", "[NormedField K]",
             "[NormedField L]", "[NormedAlgebra K L]")
        has_krasner = name.endswith("direct_monic_stability")
    else:
        binders = ()
        has_krasner = False
    for binder in binders:
        require(binder in text, "missing signature binder: " + name + " / " + binder)
    if module == MODULES[3] and name.endswith("direct_distinct_root_separation"):
        require("[Field K]" in text, "missing finite-separation field assumption")
    instance = "[IsKrasner K₀ L₀]" if module == MODULES[0] and name in first[4:] else "[IsKrasner K L]"
    require((instance in text) == has_krasner, "wrong Krasner instance: " + name)
    if name in (EXPECTED[MODULES[1]][0], CLIENTS[MODULES[4]][1]):
        require("g ≠ 0 →" in text and "leadingCoeff⁻¹" in text,
                "normalized comparison hypothesis absent")
    if name in (EXPECTED[MODULES[1]][2], CLIENTS[MODULES[4]][0]):
        require("g.natDegree = f.natDegree" in text and "‖g.coeff i - f.coeff i‖" in text,
                "ordinary coefficient hypothesis absent")
    principal = (first[9], first[10], *EXPECTED[MODULES[1]][::2],
                 CLIENTS[MODULES[3]][1], *CLIENTS[MODULES[4]][:2])
    if name in principal:
        require("(hfsep : f.Separable)" in text and "(hfsplit :" in text
                and "g.natDegree = f.natDegree" in text and ").Splits →" in text,
                "reference separability, equal degree or splitting hypothesis absent")
    if name == CLIENTS[MODULES[4]][2]:
        require("(c : K)" in text and "(hc : c ≠ 0)" in text,
                "scalar invariance hypothesis absent")


def check_source_line(raw, line, short_name, doc):
    lines = raw.decode("utf-8").splitlines()
    require(type(line) is int and 0 < line <= len(lines), "invalid native source line")
    remainder = "\n".join(lines[line - 1:])
    require(remainder.startswith("/--"), "native line is not the source docstring")
    source_doc, closing, after = remainder.partition("-/")
    require(bool(closing) and source_doc[3:].strip() == doc.strip(), "native docstring/source mismatch")
    following = re.search(r"^\s*theorem\s+(\S+)", after, re.MULTILINE)
    require(following is not None and following.group(1) == short_name,
            "native line does not precede the named source theorem")
    require("/--" not in after[:following.start()], "intervening source declaration")


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale source revision")
    require(set(sources) == set(INPUTS) == set(SOURCE_INPUT_SHA256),
            "source/pin inventory differs")
    for path, raw in sources.items():
        require(digest(raw) == SOURCE_INPUT_SHA256[path],
                "source/pin drift from accepted input: " + path)


def render(records, revision, sources, raw_records):
    require(revision == SOURCE, "unexpected/stale source revision")
    require(set(records) == set(MODULES) == set(raw_records), "native module inventory differs")
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    sections = {"production": [], "clients": []}
    found = set()
    for module in MODULES:
        record = records[module]
        require(json.loads(raw_records[module]) == record, "native record bytes/JSON differ")
        require(record["name"] == module, "native module name differs")
        require(type(record["declarations"]) is list and record["instances"] == [],
                "unexpected native declarations/instances shape")
        expected = set(EXPECTED[module])
        path = module.replace(".", "/") + ".lean"
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in expected and kind == "theorem", "unexpected module/name/kind: " + name)
            require(name not in found, "duplicate public declaration: " + name)
            require(info["sourceLink"] == "https://example.invalid/commit/" + revision + "/" + path,
                    "native record source revision/path differs")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            require(type(info["doc"]) is str and bool(info["doc"].strip()), "public docstring absent")
            require("```" not in info["doc"] and
                    re.search(r"<\s*/?\s*(?:script|iframe|style|img|object)\b", info["doc"], re.I) is None,
                    "unsupported/active docstring")
            check_source_line(sources[path], info["line"], name.rsplit(".", 1)[-1], info["doc"])
            header = Header(row["header"])
            require("".join(header.names) == name and "".join(header.kinds) == kind,
                    "native header identity differs")
            text = header.rendered()
            require(text.startswith(kind + " " + name) and "```" not in text,
                    "malformed/unsupported native signature")
            check_signature(module, name, text)
            found.add(name)
            section = "production" if module in PRODUCTION else "clients"
            sections[section].append(dict(name=name, header=text, doc=info["doc"].strip(),
                                          path=path, line=info["line"]))
        require({row["info"]["name"] for row in record["declarations"]} == expected,
                "missing public declaration in " + module)
    require(len(found) == 23 and len(sections["production"]) == 14 and len(sections["clients"]) == 9,
            "public API/client count differs")
    lines = ["# Generated API reference", "",
             "Native doc-gen4 signatures and source docstrings for all 23 named public theorems",
             "defined by this library: 14 production results and nine checked-use clients.",
             "Import `PolynomialRootStability` for the production results; the",
             "`PolynomialRootStabilityTest` leaves are separate publicly named clients.",
             "The root `PolynomialRootStability` module reexports the two production",
             "leaves and defines no additional declarations.", "",
             "Headers display every native implicit argument and typeclass; the generated",
             "signature is not a proof body. Native universe identifiers may be renamed by",
             "Lean; `K` and `L` (or `K₀` and `L₀`) can have independent universes.",
             "Source links point to lines in the unchanged source shipped alongside this file.",
             "See [the manifest](api-manifest.json), [reproduction](README.md), and the",
             "[mathematical overview](../README.md).", ""]
    for section, heading in (("production", "Production API (14 theorems)"),
                             ("clients", "Public checked-use clients (nine theorems)")):
        lines.extend(["## " + heading, ""])
        for row in sorted(sections[section], key=lambda item: (MODULES.index(item["path"].removesuffix(".lean").replace("/", ".")), item["line"])):
            lines.extend(["### " + row["name"], "", "```lean", row["header"], "```", "",
                          row["doc"], "",
                          f"[Source](../{row['path']}#L{row['line']}) (docstring begins on line {row['line']}).", ""])
    markdown = "\n".join(lines).encode("utf-8")
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_source_revision=revision, analyzed_source_tree=SOURCE_TREE,
                    modules=list(MODULES), inputs={path: digest(raw) for path, raw in sorted(sources.items())},
                    production_declarations=[row["name"] for row in sections["production"]],
                    public_client_declarations=[row["name"] for row in sections["clients"]],
                    native_record_sha256={module: digest(raw_records[module]) for module in MODULES},
                    api_sha256=digest(markdown), proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True, help="native fromDb doc-data directory")
    parser.add_argument("--source-revision", required=True,
                        help="historical mathematical input label; no Git object is needed")
    parser.add_argument("--check", action="store_true", help="compare generated bytes without writing")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    check_snapshot(args.source_revision, sources)
    raw_records = {module: (args.native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
                   for module in MODULES}
    records = {module: json.loads(raw) for module, raw in raw_records.items()}
    api, manifest = render(records, args.source_revision, sources, raw_records)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          production=14, clients=9, api_sha256=digest(api), release_acceptance=False)))


if __name__ == "__main__":
    main()
