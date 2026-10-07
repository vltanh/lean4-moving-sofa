#!/usr/bin/env python3
"""Static source audit for MovingSofaQuantitative (never invokes Lean/Lake/CI).

This audit is advisory: it catches missing *project-owned* identifiers, duplicate
top-level declarations, absent import modules, and stale theorem mappings.
Passing it would not establish Lean elaboration, mathematical correctness,
certificate replay, or kernel verification.

Run from any directory:
    python3 scripts/audit_quantitative_source_static.py --root .
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import sys

# Only project-specific names. Do not pretend to resolve Mathlib's symbol table.
# Each entry should remain here until a theorem/definition with this spelling
# exists in the checked branch, or all callers have been refactored away.
CRITICAL_INTERFACES: dict[str, tuple[str, ...]] = {
    "MovingSofaQuantitative/ReferenceExplicitMargins.lean": (
        "innerSlack_down_more",
        "gerver_niche_envelope",
        "roof_value_of_envelope",
    ),
    "MovingSofaQuantitative/NormalRecovery.lean": (
        "inner_slack_taylor_U",
        "inner_slack_taylor_V",
        "envelope_B_inactive_margin",
        "envelope_D_inactive_margin",
        "envelope_B_nearest_active_slack",
        "envelope_D_nearest_active_slack",
        "envelope_core_inward_segment",
        "frontier_shape_off_envelope",
        "segment_from_niche_to_outer_crosses_envelope",
    ),
    "MovingSofaQuantitative/EffectiveRegularizationSupport.lean": (
        "integral_penalty_limsup_of_dyadic",
        "quantitative_curvature_from_penalized_variation",
        "approximate_arm_integrals",
        "robust_lower_sequence_iteration",
        "isKi_of_approx_curvature",
    ),
    "MovingSofaQuantitative/ExplicitReferenceScales.lean": (
        "explicit_reference_contact_certificate",
        "explicit_fixed_floor_terminal",
        "reference_adaptive_remainder_bound",
        "explicit_normal_and_deep_niche_recovery",
        "roof_interior_balls",
    ),
    "MovingSofaQuantitative/EffectiveAngleEntry.lean": (
        "partial_inner_triangle_area_lower",
        "high_angle_tan_lower",
        "partialIntegralQuadratureSamples",
        "bounded_partial_penalized_subsequence",
        "partial_quadrature_tendsto_integral",
        "floating_defect_budget",
        "completed_boundary_defect_identity",
        "partial_pin_sine_lower",
        "solve_two_pinned_defects",
        "large_outer_extent_of_area",
        "triangle_inner_of_support_witnesses",
        "prepend_missing_rotation",
    ),
    "MovingSofaQuantitative/CoarseAngleCertificate.lean": (
        "rational_polygon_clip_contains",
        "candidateInBox",
        "support_quantile_contraction_safe",
        "area_mono_polygons",
        "support_box_split_complete",
        "terminal_candidate_of_motion",
        "exists_hundredth_slab",
        "contract_none_excludes",
    ),
}

# Source-shape blockers which cannot be resolved by finding an identifier.
# These require an actual proof rewrite; removing or renaming the marker without
# supplying the missing argument must not be counted as progress.
PROOF_REVIEW_GATES: dict[str, tuple[tuple[str, str], ...]] = {
    "MovingSofaQuantitative/EffectiveRegularizationSupport.lean": (
        (
            r"subset\s*:\s*∀r≥0,interval\s+r⊆Icc",
            "A one-sided interval of length r stays in [0, pi] only for a "
            "bounded radius. Require r <= pi/2 or truncate the interval.",
        ),
        (
            r"theorem\s+sup_le_of_L2_lipschitz[\s\S]{0,350}"
            r"\(hD\s*:\s*∀t∈Icc",
            "An L2-to-sup bound proportional only to the Lipschitz constant "
            "is false for a nonzero constant function. An anchored zero "
            "of the support difference is required.",
        ),
    ),
    "MovingSofaQuantitative/EffectiveRightAngle.lean": (
        (
            r"theorem\s+penalized_cap_radius_bound[\s\S]{0,600}"
            r"∀p∈C,norm2\s+p<26",
            "An absolute origin-centred radius bound contradicts the "
            "horizontal translation invariance of cap area and penalty. "
            "Measure the radius relative to the input midpoint.",
        ),
    ),
    "MovingSofaQuantitative/ReferenceSector.lean": (
        (
            r"rcases\s+gs_cases\s+\(P\s*:=\s*P\)\s+p\.1",
            "The boundary point's horizontal coordinate is not a turning "
            "parameter. A genuine boundary contact/envelope chart is required.",
        ),
        (
            r"refine\s+⟨π\s*/\s*2,\s*\?_⟩[\s\S]*?have\s+hconv:Convex",
            "A vertical-centered sector cannot be inferred for an entire "
            "convex wing, especially at its outer horizontal endpoint. "
            "Prove a location-dependent wedge using the actual boundary.",
        ),
    ),
}

DECL = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|opaque)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|axiom)\s+"
    r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\b",
    re.M,
)
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z_][\w.]*)", re.M)
CHEAT = re.compile(r"\b(?:sorry|admit|axiom)\b")
QUANT = "MovingSofaQuantitative"


def strip_lean_comments(source: str) -> str:
    """Conservatively erase nested Lean block comments and line comments."""
    out: list[str] = []
    i, n, depth, quoted = 0, len(source), 0, False
    while i < n:
        if not quoted and source.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
            continue
        if depth and source.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
            continue
        if depth:
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
            continue
        if not quoted and source.startswith("--", i):
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if source[i] == '"' and (i == 0 or source[i - 1] != "\\"):
            quoted = not quoted
        out.append(source[i] if not quoted else " ")
        i += 1
    return "".join(out)


def source_audit(root: Path) -> dict:
    lean_files = sorted(root.rglob("*.lean"))
    # Skip vendored dependencies (not project source).
    lean_files = [p for p in lean_files if ".lake" not in p.parts and ".git" not in p.parts]
    contents = {p.relative_to(root).as_posix(): strip_lean_comments(
        p.read_text(encoding="utf-8")) for p in lean_files}
    declared: dict[str, list[str]] = defaultdict(list)
    quant_decls: dict[str, list[str]] = defaultdict(list)
    errors: list[dict] = []
    warnings: list[dict] = []
    for path, src in contents.items():
        for name in DECL.findall(src):
            short = name.rsplit(".", 1)[-1]
            declared[short].append(path)
            if path.startswith(QUANT + "/"):
                quant_decls[short].append(path)
        for m in CHEAT.finditer(src):
            # "axiom" also occurs legitimately in quotations; only a true
            # declaration is a definite violation.
            if m.group() in ("sorry", "admit") or re.search(
                r"^\s*axiom\s+", src[:m.end()].splitlines()[-1]):
                errors.append({"kind": "hole_or_axiom", "file": path, "token": m.group()})
        if path.startswith(QUANT + "/"):
            for module in IMPORT.findall(src):
                if module.startswith(QUANT + "."):
                    target = module.replace(".", "/") + ".lean"
                    if target not in contents:
                        errors.append({"kind": "missing_quantitative_import",
                                       "file": path, "import": module})
    for name, paths in sorted(quant_decls.items()):
        if len(set(paths)) > 1:
            warnings.append({"kind": "same_short_declaration_name",
                             "name": name, "files": sorted(set(paths)),
                             "note": "confirm namespaces before treating as a collision"})
    for path, symbols in CRITICAL_INTERFACES.items():
        src = contents.get(path)
        if src is None:
            errors.append({"kind": "missing_audited_source", "file": path})
            continue
        for symbol in symbols:
            if not re.search(r"\b" + re.escape(symbol) + r"\b", src):
                continue  # refactored away
            short = symbol.rsplit(".", 1)[-1]
            if not declared.get(short):
                errors.append({"kind": "undeclared_project_helper",
                               "file": path, "symbol": symbol})
    for path, gates in PROOF_REVIEW_GATES.items():
        src = contents.get(path)
        if src is None:
            errors.append({"kind": "missing_audited_source", "file": path})
            continue
        for pattern, explanation in gates:
            if re.search(pattern, src):
                errors.append({"kind": "unresolved_proof_structure",
                               "file": path, "explanation": explanation})
    manifest_path = root / "docs/paper/quantitative_manifest.json"
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        for row in manifest.get("results", []):
            module = row.get("module")
            name = str(row.get("declaration", "")).rsplit(".", 1)[-1]
            path = module.replace(".", "/") + ".lean" if module else ""
            if path not in contents:
                errors.append({"kind": "manifest_missing_source", "result": row.get("id"),
                               "module": module})
            elif not re.search(r"^\s*theorem\s+" + re.escape(name) + r"\b", contents[path], re.M):
                errors.append({"kind": "manifest_missing_theorem", "result": row.get("id"),
                               "file": path, "declaration": name})
    else:
        errors.append({"kind": "manifest_missing", "file": str(manifest_path)})
    return {
        "scope": "source-only; no Lean/CI/certificate execution",
        "lean_files": len(contents),
        "quantitative_files": sum(p.startswith(QUANT + "/") for p in contents),
        "errors": errors,
        "warnings": warnings,
        "complete": not errors,
        "note": "Even a passing result cannot establish Lean type correctness or soundness.",
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    result = source_audit(args.root.resolve())
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"Scanned {result['lean_files']} Lean sources "
              f"({result['quantitative_files']} quantitative).")
        for error in result["errors"]:
            print("ERROR:", json.dumps(error, sort_keys=True))
        for warning in result["warnings"]:
            print("WARNING:", json.dumps(warning, sort_keys=True))
        print("PASS (static only)" if result["complete"] else "FAIL (static; unresolved sources)")
    return 0 if result["complete"] else 1


if __name__ == "__main__":
    sys.exit(main())
