#!/usr/bin/env python3
"""Assemble a source-only overlay; never invokes Lean, Lake, git, or the network."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import unicodedata

UPSTREAM_BLOB = "59b6ed7eb42e11b208b09539c245da4d3f11ed00"
UPSTREAM_PATH = Path("FormalConjectures/Wikipedia/MovingSofa.lean")
TARGET = "volume_eq_sofaConstant_iff_congruent_gerversSofa"
SIGNATURE = """theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by"""
ORIGINAL = "@[category research open, AMS 49]\n" + SIGNATURE + "\n  sorry"
DOC_ANCHOR = "/--\nGerver's sofa is the unique sofa that attains the sofa constant, up to a rigid motion."
IMPORT_ANCHOR = "public import FormalConjecturesUtil\n"
EXTRA_IMPORTS = """public import SofaUniqueness.Draft.ShapeUniqueness
public import SofaUniqueness.AffineRecovery
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
"""
DRAFT_FILES = (
    "SetRecovery.lean", "AffineRecovery.lean", "SquareGap.lean",
    "Draft/Rigid.lean", "Draft/CapKernel.lean", "Draft/CapGeometry.lean",
    "Draft/Selection.lean", "Draft/PaperReductions.lean", "Draft/ShapeUniqueness.lean",
)
LAKE_APPEND = """
# Source-only uniqueness draft. No additional default build targets.
[[lean_lib]]
name = "SofaLegacy"
globs = ["SofaLegacy.+"]
[lean_lib.leanOptions]
maxSynthPendingDepth = 3

[[lean_lib]]
name = "SofaUniqueness"
globs = ["SofaUniqueness.+"]
[lean_lib.leanOptions]
maxSynthPendingDepth = 3
"""


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'" or unicodedata.category(c).startswith("M")


def transform_lean(text: str, *, relocate: bool = False, mask: bool = False) -> str:
    """Rewrite identifier tokens, preserving nested comments and string literals.

    This is a lexical source transform, not a Lean parser or a proof checker.
    `mask` removes comments and strings for the static token checks below.
    """
    out: list[str] = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unterminated Lean string literal")
        else:
            if text[i].isalpha() or text[i] == "_":
                i += 1
                while i < len(text) and ident_char(text[i]):
                    i += 1
                token = text[start:i]
                out.append("SofaLegacy" if relocate and token == "MovingSofa" else token)
            else:
                out.append(text[i])
                i += 1
            continue
        chunk = text[start:i]
        out.append("".join("\n" if c == "\n" else " " for c in chunk) if mask else chunk)
    return "".join(out)


def assemble(upstream: str, coordinates: str, motions: str, target: str) -> str:
    for anchor in (IMPORT_ANCHOR, DOC_ANCHOR, ORIGINAL):
        if upstream.count(anchor) != 1:
            raise ValueError("upstream declaration/anchor differs from inspected source")
    if target.count(SIGNATURE) != 1:
        raise ValueError("replacement changes or duplicates the requested statement")
    support = coordinates + "\n\n" + motions
    if TARGET in transform_lean(support, mask=True):
        raise ValueError("adapter refers to the target theorem before its declaration")
    code = transform_lean(support + "\n" + target, mask=True)
    if re.search(r"\b(?:axiom|unsafe|admit)\b", code):
        raise ValueError("unexpected axiom/unsafe/admit in insertion")
    if re.search(r"\bsorry\b", transform_lean(target, mask=True)):
        raise ValueError("the replacement body is still a bare admission")
    result = upstream.replace(IMPORT_ANCHOR, IMPORT_ANCHOR + EXTRA_IMPORTS, 1)
    result = result.replace(DOC_ANCHOR, support + "\n\n" + DOC_ANCHOR, 1)
    result = result.replace(ORIGINAL, target.strip(), 1)
    if len(re.findall(r"\btheorem\s+" + TARGET + r"\b", transform_lean(result, mask=True))) != 1:
        raise ValueError("target theorem must be declared exactly once")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--formal-conjectures", type=Path, required=True,
                        help="existing local formal-conjectures checkout; read only")
    parser.add_argument("--output", type=Path, required=True,
                        help="new directory for the source overlay; must not already exist")
    args = parser.parse_args(argv)
    repo = Path(__file__).resolve().parents[1]
    fc = args.formal_conjectures.resolve()
    output = args.output.resolve()
    if output.exists():
        raise ValueError("output already exists; refusing to overwrite it")
    upstream_bytes = (fc / UPSTREAM_PATH).read_bytes()
    if git_blob_sha(upstream_bytes) != UPSTREAM_BLOB:
        raise ValueError("upstream blob changed: review it and update the explicit pin first")
    fragment_dir = repo / "drafts/formal-conjectures"
    fragments = [(fragment_dir / name).read_text(encoding="utf-8") for name in
                 ("Coordinates.lean.inc", "Motions.lean.inc", "Target.lean.inc")]
    files: dict[Path, str] = {}
    origins: dict[str, str] = {}
    legacy = sorted((repo / "MovingSofa").rglob("*.lean"))
    if not legacy:
        raise ValueError("legacy Lean source tree not found")
    for src in legacy:
        dest = Path("SofaLegacy") / src.relative_to(repo / "MovingSofa")
        files[dest] = transform_lean(src.read_text(encoding="utf-8"), relocate=True)
        origins[str(dest)] = str(src.relative_to(repo))
    for rel in DRAFT_FILES:
        dest = Path("SofaUniqueness") / rel
        src = repo / dest
        files[dest] = transform_lean(src.read_text(encoding="utf-8"), relocate=True)
        origins[str(dest)] = str(dest)
    files[UPSTREAM_PATH] = assemble(upstream_bytes.decode("utf-8"), *fragments)
    lake = (fc / "lakefile.toml").read_text(encoding="utf-8")
    if re.search(r'^name\s*=\s*"(?:SofaLegacy|SofaUniqueness)"', lake, re.MULTILINE):
        raise ValueError("upstream Lake configuration already registers the draft libraries")
    files[Path("lakefile.toml")] = lake + LAKE_APPEND
    files[Path("SOFA_LEGACY_LICENSE")] = (repo / "LICENSE").read_text(encoding="utf-8")
    manifest = {
        "status": "UNCOMPILED; contains explicit proof admissions",
        "upstream_git_blob": UPSTREAM_BLOB,
        "source_toolchain": (repo / "lean-toolchain").read_text().strip(),
        "upstream_toolchain": (fc / "lean-toolchain").read_text().strip(),
        "toolchain_compatibility": "NOT CHECKED; neither pin is changed",
        "executed_lean_or_lake": False,
        "namespace_relocation": {"MovingSofa": "SofaLegacy"},
        "origins": origins,
        "files": {str(p): {"sha256": hashlib.sha256(s.encode()).hexdigest(),
                   "sorry_tokens": len(re.findall(r"\bsorry\b", transform_lean(s, mask=True)))}
                  for p, s in files.items()},
    }
    output.mkdir(parents=True)
    for path, text in files.items():
        dest = output / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding="utf-8")
    (output / "DRAFT_MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Wrote {len(files)} source/configuration files to {output}")
    print("No Lean/Lake execution. This overlay remains incomplete and uncompiled.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
