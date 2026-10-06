#!/usr/bin/env python3
"""Exact-statement/axiom gate for the quantitative extension (not the whole paper).

--inventory reports declared progress without compiling. --emit writes a Lean
check but does not execute it. --verify invokes local Lake/Lean and produces a
source-bound receipt only after successful kernel elaboration. No CI calls.
A JSON status field, a Python test, or an uncompiled .lean file is not evidence
that a theorem has been checked. Planned targets block the full gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
PREFIX = "MovingSofaQuantitative.Targets."
LIBRARIES = ("MovingSofaOptimality", "MovingSofaUniqueness", "MovingSofaBridge",
             "MovingSofaStability", "MovingSofaExtremal", "MovingSofaQuantitative")


class GateError(ValueError):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_path(root: Path, relative: str) -> Path:
    p = (root / relative).resolve()
    try:
        p.relative_to(root.resolve())
    except ValueError as exc:
        raise GateError(f"path escapes repository: {relative}") from exc
    if not p.is_file():
        raise GateError(f"missing file: {relative}")
    return p


def load_manifest(root: Path, path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema") != 1 or data.get("scope") != "quantitative_extension":
        raise GateError("unsupported manifest; this gate covers the quantitative extension only")
    entries = data.get("results")
    required = data.get("required_ids")
    if not isinstance(entries, list) or not entries or not isinstance(required, list):
        raise GateError("nonempty results and required_ids are required")
    seen: set[str] = set()
    targets: set[str] = set()
    proofs: set[str] = set()
    for item in entries:
        key, target, proof = item.get("id"), item.get("target"), item.get("declaration")
        if not isinstance(key, str) or not key or key in seen:
            raise GateError(f"duplicate or invalid result id: {key!r}")
        seen.add(key)
        if not isinstance(target, str) or not IDENT.fullmatch(target) or not target.startswith(PREFIX):
            raise GateError(f"invalid target name: {target!r}")
        if target in targets:
            raise GateError(f"duplicate target: {target}")
        targets.add(target)
        status = item.get("status")
        if status not in {"planned", "source"}:
            raise GateError("manifest status is planning metadata; use a fresh Lean receipt for checked status")
        if status == "planned":
            if proof is not None or item.get("module") is not None:
                raise GateError(f"planned result {key} must not pretend to name an existing proof")
        else:
            module = item.get("module")
            if not isinstance(proof, str) or not IDENT.fullmatch(proof):
                raise GateError(f"invalid proof name: {proof!r}")
            if not isinstance(module, str) or not IDENT.fullmatch(module):
                raise GateError(f"invalid module: {module!r}")
            if proof in proofs:
                raise GateError(f"duplicate proof mapping: {proof}")
            proofs.add(proof)
            checked_path(root, module.replace(".", "/") + ".lean")
    if set(required) != seen or len(required) != len(seen):
        raise GateError("the required inventory and result inventory disagree")
    if "explicit-cutoff" not in seen:
        raise GateError("mandatory 10^-600 target was removed")
    cutoff = next(x for x in entries if x["id"] == "explicit-cutoff")
    if cutoff["target"] != PREFIX + "ExplicitCutoff":
        raise GateError("mandatory cutoff points at a different proposition")
    checked_path(root, "MovingSofaQuantitative/Targets.lean")
    return data


def source_snapshot(root: Path, manifest_path: Path) -> dict[str, str]:
    files = {manifest_path.resolve(), Path(__file__).resolve()}
    for library in LIBRARIES:
        files.update((root / library).rglob("*.lean"))
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "ChallengeDefs.lean"):
        p = root / name
        if p.is_file():
            files.add(p)
    out: dict[str, str] = {}
    for p in sorted(files):
        try:
            name = p.resolve().relative_to(root.resolve()).as_posix()
        except ValueError as exc:
            raise GateError("run the committed gate inside the repository being checked") from exc
        out[name] = digest(p.read_bytes())
    return out


AUDIT_BODY = r'''
open Lean Elab Command

namespace QuantitativePublicationGate

elab "#quantitative_statement " t:ident " := " p:ident : command => do
  let target ← liftCoreM <| getConstInfo t.getId
  let proof ← liftCoreM <| getConstInfo p.getId
  unless target.levelParams.isEmpty && proof.levelParams.isEmpty do
    throwError "this statement contract requires closed, non-universe-polymorphic types"
  match target with
  | .defnInfo _ => pure ()
  | _ => throwError "the expected statement must be a named proposition definition"
  match proof with
  | .thmInfo _ => pure ()
  | _ => throwError "the result must be a theorem, not an axiom, target definition, or status flag"
  let targetIsProp ← liftTermElabM <| Meta.isDefEq target.type (mkSort .zero)
  unless targetIsProp do throwError "expected target is not a proposition"
  let same ← liftTermElabM <| Meta.isDefEq proof.type (mkConst t.getId)
  unless same do throwError m!"statement mismatch: {p.getId} does not prove {t.getId}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← liftCoreM <| collectAxioms p.getId
  if axioms.any (!allowed.contains ·) then
    throwError m!"nonstandard axiom dependency: {p.getId}: {axioms}"
  logInfo m!"QUANTITATIVE_STATEMENT_OK {t.getId} {p.getId}"

elab "#quantitative_library_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for m in env.header.moduleNames, d in env.header.moduleData do
    if (`MovingSofaQuantitative).isPrefixOf m then
      for n in d.constNames do
        let axioms ← liftCoreM <| collectAxioms n
        if axioms.any (!allowed.contains ·) then
          throwError m!"nonstandard axioms in quantitative declaration {n}: {axioms}"
        count := count + 1
  if count == 0 then throwError "no quantitative declarations were inspected"
  logInfo m!"QUANTITATIVE_AXIOMS_OK {count}"

elab "#quantitative_negative_control" : command => do
  let wrong ← liftTermElabM <| Meta.isDefEq (mkConst ``True) (mkConst ``False)
  if wrong then throwError "type comparison negative control failed"

end QuantitativePublicationGate

#quantitative_negative_control
'''


def lean_program(root: Path, entries: list[dict[str, Any]], nonce: str) -> str:
    modules = set()
    # Expose repository proof bodies for the transitive axiom audit.
    for library in LIBRARIES:
        for p in (root / library).rglob("*.lean"):
            module = p.relative_to(root).with_suffix("").as_posix().replace("/", ".")
            if not IDENT.fullmatch(module):
                raise GateError(f"invalid source module name {module}")
            modules.add(module)
    imports = "\n".join(f"import all {m}" for m in sorted(modules))
    commands = "\n".join(f'#quantitative_statement {e["target"]} := {e["declaration"]}' for e in entries)
    return ('module\n\npublic meta import Lean\n' + imports + '\n' + AUDIT_BODY + '\n' + commands
            + '\n#quantitative_library_axioms\n'
            + f'run_cmd logInfo "QUANTITATIVE_GATE_COMPLETE {nonce}"\n')


def dependency_state(root: Path) -> dict[str, str]:
    """Require the installed package revisions to match the pinned manifest."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    out = {}
    for package in manifest.get("packages", []):
        if package.get("type") != "git":
            raise GateError(f"unhandled dependency type: {package.get('name')}")
        name, revision = package["name"], package["rev"]
        path = root / ".lake" / "packages" / name
        if not path.is_dir():
            raise GateError(f"missing pinned dependency {name}; install it before verification")
        head = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
                               check=True, capture_output=True, text=True).stdout.strip()
        if head != revision or dirty:
            raise GateError(f"dependency {name} does not match its clean pinned revision")
        out[name] = head
    return out


def verify(root: Path, manifest_path: Path, manifest: dict[str, Any], allow_partial: bool,
           output: Path) -> dict[str, Any]:
    pending = [x["id"] for x in manifest["results"] if x["status"] != "source"]
    if pending and not allow_partial:
        raise GateError("full gate blocked by unproved targets: " + ", ".join(pending))
    entries = [x for x in manifest["results"] if x["status"] == "source"]
    if not entries:
        raise GateError("no proof source is available")
    lake = shutil.which("lake")
    if lake is None:
        raise GateError("Lake is unavailable; no elaboration, axiom audit, or verification receipt exists")
    before = source_snapshot(root, manifest_path)
    source_hash = digest(json.dumps(before, sort_keys=True).encode())
    nonce = digest((source_hash + json.dumps(entries, sort_keys=True)).encode())
    deps = dependency_state(root)
    version = subprocess.run([lake, "env", "lean", "--version"], cwd=root, check=True,
                             capture_output=True, text=True).stdout.strip()
    expected = (root / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    if expected not in version:
        raise GateError(f"toolchain mismatch: expected {expected}, got {version}")
    # Never dispatch or rerun a workflow. Both commands are local.
    subprocess.run([lake, "build", "MovingSofaQuantitative"], cwd=root, check=True)
    work = root / ".lake" / "build" / "quantitative-audit"
    work.mkdir(parents=True, exist_ok=True)
    audit = work / "Statements.lean"
    audit.write_text(lean_program(root, entries, nonce), encoding="utf-8")
    result = subprocess.run([lake, "env", "lean", str(audit)], cwd=root, check=True,
                            capture_output=True, text=True)
    for entry in entries:
        marker = f'QUANTITATIVE_STATEMENT_OK {entry["target"]} {entry["declaration"]}'
        if marker not in result.stdout:
            raise GateError(f"missing statement-check output for {entry['id']}")
    if f"QUANTITATIVE_GATE_COMPLETE {nonce}" not in result.stdout or "QUANTITATIVE_AXIOMS_OK" not in result.stdout:
        raise GateError("Lean did not complete the generated audit")
    if source_snapshot(root, manifest_path) != before or dependency_state(root) != deps:
        raise GateError("source or dependency revision changed during verification")
    receipt = {"schema": 1, "scope": "quantitative_extension_only",
               "status": "partial_kernel_checked" if pending else "extension_kernel_checked",
               "checked_ids": [x["id"] for x in entries], "pending_ids": pending,
               "source_digest": source_hash, "source_files": before,
               "lean_version": version, "dependency_revisions": deps,
               "audit_source_sha256": digest(audit.read_bytes()),
               "lean_output_sha256": digest(result.stdout.encode()),
               "not_claimed": ["complete main-paper/appendix correspondence",
                               "manual interpretation of the geometric definitions"]}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path.cwd())
    p.add_argument("--manifest", type=Path, default=Path("docs/paper/quantitative_manifest.json"))
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--inventory", action="store_true")
    mode.add_argument("--emit", type=Path)
    mode.add_argument("--verify", action="store_true")
    p.add_argument("--allow-partial", action="store_true")
    p.add_argument("--receipt", type=Path, default=Path(".lake/build/quantitative-audit/receipt.json"))
    args = p.parse_args()
    root = args.root.resolve()
    try:
        path = checked_path(root, str(args.manifest))
        manifest = load_manifest(root, path)
        if args.inventory:
            report = {"status": "source_inventory_only", "kernel_checked": False,
                      "source_ids": [x["id"] for x in manifest["results"] if x["status"] == "source"],
                      "pending_ids": [x["id"] for x in manifest["results"] if x["status"] == "planned"],
                      "scope": "quantitative_extension_only"}
        elif args.emit:
            entries = [x for x in manifest["results"] if x["status"] == "source"]
            if not entries:
                raise GateError("no source declarations to include in an audit")
            program = lean_program(root, entries, "EMITTED_NOT_EXECUTED")
            args.emit.write_text(program, encoding="utf-8")
            report = {"status": "audit_source_only", "kernel_checked": False, "output": str(args.emit)}
        else:
            report = verify(root, path, manifest, args.allow_partial, root / args.receipt)
        print(json.dumps(report, indent=2))
        return 0
    except (GateError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"quantitative gate BLOCKED: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
