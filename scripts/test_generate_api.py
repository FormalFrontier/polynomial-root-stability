#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only corruption tests for the native Markdown adapter, not Lean checks."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import generate_api as api


def header_for(module, name):
    krasner = api.EXPECTED[api.MODULES[0]]
    if module == api.MODULES[0] and name in krasner[:4]:
        binders = "{K : Type u_1} {L : Type u_2} [Field K] [NormedField L] [Algebra K L]"
        instance = name in krasner[:2]
        class_name = "[IsKrasner K L]"
    elif module == api.MODULES[0]:
        binders = "{K₀ : Type u_3} {L₀ : Type u_4} [NormedField K₀] [NormedField L₀] [NormedAlgebra K₀ L₀]"
        instance = name in krasner[7:]
        class_name = "[IsKrasner K₀ L₀]"
    elif name == api.EXPECTED[api.MODULES[1]][1]:
        binders = "{K : Type u} [NormedField K] (hf0 : f ≠ 0)"
        instance = False
        class_name = ""
    elif module == api.MODULES[1] or name in api.CLIENTS[api.MODULES[4]][:3]:
        binders = "{K : Type u} {L : Type v} [NormedField K] [NormedField L] [NormedAlgebra K L] (hf0 : f ≠ 0)"
        instance = True
        class_name = "[IsKrasner K L]"
    elif module == api.MODULES[3] and name.endswith("direct_distinct_root_separation"):
        binders = "{K : Type u} {L : Type v} [Field K] [NormedField L] [Algebra K L]"
        instance = False
        class_name = ""
    elif module == api.MODULES[3]:
        binders = "{K : Type u} {L : Type v} [NormedField K] [NormedField L] [NormedAlgebra K L]"
        instance = True
        class_name = "[IsKrasner K L]"
    else:
        binders = ""
        instance = False
        class_name = ""
    conclusion = ("(hfsep : f.Separable) (hfsplit : (Polynomial.map f).Splits) "
                  "(c : K) (hc : c ≠ 0) g ≠ 0 → leadingCoeff⁻¹ "
                  "g.natDegree = f.natDegree ‖g.coeff i - f.coeff i‖ "
                  "(Polynomial.map g).Splits → True")
    parts = [binders, class_name if instance else "", conclusion]
    return ('<div class="decl_header"><span class="decl_kind">theorem</span> '
            f'<span class="decl_name">{name}</span> '
            f'<div class="decl_type">{" ".join(parts)}</div></div>')


def fixture():
    records = {module: dict(name=module, imports=[], instances=[], declarations=[])
               for module in api.MODULES}
    sources = {path: b"fixture pin\n" for path in api.INPUTS}
    for module in api.MODULES:
        source_lines = []
        path = module.replace(".", "/") + ".lean"
        for name in api.EXPECTED[module]:
            short_name = name.rsplit(".", 1)[-1]
            doc = "Fixture for " + name + "."
            line = len(source_lines) + 1
            source_lines += ["/-- " + doc + " -/", "theorem " + short_name + " : True := by trivial"]
            records[module]["declarations"].append(dict(header=header_for(module, name), info=dict(
                name=name, kind="theorem", doc=doc, line=line,
                sourceLink="https://example.invalid/commit/" + api.SOURCE + "/" + path,
                docLink="./" + module.replace(".", "/") + ".html#" + name)))
        sources[path] = ("\n".join(source_lines) + "\n").encode()
    raw = {module: json.dumps(record).encode() for module, record in records.items()}
    return records, sources, raw


def run_fixture(records, sources, raw=None):
    if raw is None:
        raw = {module: json.dumps(record).encode() for module, record in records.items()}
    return api.render(records, api.SOURCE, sources, raw)


class Controls(unittest.TestCase):
    def test_exact_five_modules_23_public_theorems_and_hashes(self):
        records, sources, raw = fixture()
        markdown, manifest_bytes = run_fixture(records, sources, raw)
        manifest = json.loads(manifest_bytes)
        self.assertEqual(len(manifest["production_declarations"]), 14)
        self.assertEqual(len(manifest["public_client_declarations"]), 9)
        self.assertEqual(set(manifest["production_declarations"]),
                         set(api.PRODUCTION[api.MODULES[0]] + api.PRODUCTION[api.MODULES[1]]))
        self.assertEqual(set(manifest["public_client_declarations"]),
                         set(api.CLIENTS[api.MODULES[3]] + api.CLIENTS[api.MODULES[4]]))
        self.assertEqual(manifest["modules"], list(api.MODULES))
        self.assertEqual(set(manifest["inputs"]), set(api.INPUTS))
        self.assertEqual(manifest["api_sha256"], api.digest(markdown))
        self.assertEqual(manifest["native_record_sha256"],
                         {module: api.digest(raw[module]) for module in api.MODULES})
        self.assertEqual(markdown.count(b"\n### "), 23)
        self.assertIn(b"Production API (14 theorems)", markdown)
        self.assertIn(b"Public checked-use clients (nine theorems)", markdown)
        self.assertNotIn(b"example.invalid", markdown + manifest_bytes)
        self.assertFalse(manifest["proof_certification"])
        self.assertFalse(manifest["release_acceptance"])

    def test_visible_entities_and_independent_universes(self):
        header = api.Header('<div><span>{K : Type u} {L : Type v} '
                            '[NormedField K] [NormedField L]</span>'
                            '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>')
        self.assertEqual(header.rendered(),
                         '{K : Type u} {L : Type v} [NormedField K] [NormedField L] x < y ∧ x ≤ y')
        self.assertEqual(api.Header('<span><span>IsKrasner</span>.<span>adjoin</span></span>').rendered(),
                         'IsKrasner.adjoin')

    def test_fail_closed_inventory_source_docstring_and_native_record(self):
        def row(records):
            return records[api.MODULES[0]]["declarations"][0]

        operations = [
            lambda records, sources, raw: records.pop(api.MODULES[2]),
            lambda records, sources, raw: records[api.MODULES[0]]["declarations"].pop(),
            lambda records, sources, raw: records[api.MODULES[0]]["declarations"].append(copy.deepcopy(row(records))),
            lambda records, sources, raw: records[api.MODULES[1]]["declarations"].append(copy.deepcopy(row(records))),
            lambda records, sources, raw: records[api.MODULES[2]]["declarations"].append(copy.deepcopy(row(records))),
            lambda records, sources, raw: records[api.MODULES[0]].update(name="Wrong.Module"),
            lambda records, sources, raw: records[api.MODULES[0]].update(instances=["unexpected"]),
            lambda records, sources, raw: row(records)["info"].update(name="IsKrasner.unexpected"),
            lambda records, sources, raw: row(records)["info"].update(kind="axiom"),
            lambda records, sources, raw: row(records)["info"].update(doc=""),
            lambda records, sources, raw: row(records)["info"].update(doc="not the source docstring"),
            lambda records, sources, raw: row(records)["info"].update(line=0),
            lambda records, sources, raw: row(records)["info"].update(line=True),
            lambda records, sources, raw: row(records)["info"].update(line=999),
            lambda records, sources, raw: row(records)["info"].update(sourceLink="main"),
            lambda records, sources, raw: row(records)["info"].update(docLink="different"),
            lambda records, sources, raw: row(records).update(header="<script>bad</script>"),
            lambda records, sources, raw: row(records).update(header="<div><span></div>"),
            lambda records, sources, raw: row(records).update(header="<span onclick='bad'>x</span>"),
            lambda records, sources, raw: row(records).update(header="<a href='javascript:bad'>bad</a>"),
            lambda records, sources, raw: row(records).update(header=row(records)["header"].replace("{L : Type u_2}", "")),
            lambda records, sources, raw: row(records).update(header=row(records)["header"].replace("[IsKrasner K L]", "")),
            lambda records, sources, raw: sources.pop("lean-toolchain"),
            lambda records, sources, raw: raw.__setitem__(api.MODULES[0], b'{}'),
        ]
        for index, operation in enumerate(operations):
            with self.subTest(corruption=index):
                records, sources, raw = fixture()
                operation(records, sources, raw)
                if index != len(operations) - 1:
                    raw = {module: json.dumps(record).encode() for module, record in records.items()}
                with self.assertRaises(ValueError):
                    run_fixture(records, sources, raw)

    def test_other_implicit_binder_and_normalization_corruption(self):
        for module, name, token in [
            (api.MODULES[0], api.EXPECTED[api.MODULES[0]][3], "[Algebra K L]"),
            (api.MODULES[0], api.EXPECTED[api.MODULES[0]][5], "{L₀ : Type u_4}"),
            (api.MODULES[0], api.EXPECTED[api.MODULES[0]][6], "[NormedAlgebra K₀ L₀]"),
            (api.MODULES[1], api.EXPECTED[api.MODULES[1]][0], "g ≠ 0 →"),
            (api.MODULES[1], api.EXPECTED[api.MODULES[1]][1], "(hf0 : f ≠ 0)"),
            (api.MODULES[1], api.EXPECTED[api.MODULES[1]][2], "‖g.coeff i - f.coeff i‖"),
            (api.MODULES[3], api.EXPECTED[api.MODULES[3]][0], "[Field K]"),
            (api.MODULES[4], api.EXPECTED[api.MODULES[4]][1], "{L : Type v}"),
            (api.MODULES[4], api.EXPECTED[api.MODULES[4]][2], "(hc : c ≠ 0)"),
        ]:
            with self.subTest(declaration=name, token=token):
                records, sources, _ = fixture()
                target = next(row for row in records[module]["declarations"] if row["info"]["name"] == name)
                target["header"] = target["header"].replace(token, "")
                with self.assertRaises(ValueError):
                    run_fixture(records, sources)

    def test_stale_revision_source_pin_inventory_and_optimized_entry(self):
        records, sources, raw = fixture()
        with self.assertRaises(ValueError):
            api.render(records, "main", sources, raw)
        with self.assertRaises(ValueError):
            api.render(records, "a" * 40, sources, raw)
        hashes = {path: api.digest(raw) for path, raw in sources.items()}
        with patch.object(api, "SOURCE_INPUT_SHA256", hashes):
            api.check_snapshot(api.SOURCE, sources)
            for path in api.INPUTS:
                with self.subTest(drift=path):
                    changed = dict(sources)
                    changed[path] += b"drift"
                    with self.assertRaises(ValueError):
                        api.check_snapshot(api.SOURCE, changed)
                with self.subTest(missing=path):
                    changed = dict(sources)
                    changed.pop(path)
                    with self.assertRaises(ValueError):
                        api.check_snapshot(api.SOURCE, changed)
            with self.assertRaises(ValueError):
                api.check_snapshot(api.SOURCE, {**sources, "extra.lean": b""})
            with self.assertRaises(ValueError):
                api.check_snapshot("main", sources)
            with self.assertRaises(ValueError):
                api.check_snapshot("a" * 40, sources)
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run([sys.executable, "-O", str(Path(api.__file__).resolve()),
                                     "--native-data", temporary, "--source-revision", api.SOURCE],
                                    capture_output=True, text=True, cwd=temporary, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("optimized Python", result.stderr)
            self.assertEqual(list(Path(temporary).iterdir()), [])

    def test_actual_source_bytes_without_git_or_historical_objects(self):
        root = Path(api.__file__).resolve().parent.parent
        sources = {path: (root / path).read_bytes() for path in api.INPUTS}
        with patch.object(subprocess, "check_output", side_effect=AssertionError("no Git allowed")):
            api.check_snapshot(api.SOURCE, sources)
        self.assertEqual({path: api.digest(raw) for path, raw in sources.items()},
                         api.SOURCE_INPUT_SHA256)


if __name__ == "__main__":
    unittest.main()
