#!/usr/bin/env python3
"""Inventory literal TeX theorem environments; this is NOT a Lean proof audit.

Follows literal input/include paths, preserves source locations, excludes comments
and verbatim text, and rejects cycles/path escapes. Prose claims and custom TeX
macros still require a human inventory review. No theorem is marked verified.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterator

CLAIM_ENVS = frozenset({"theorem", "lemma", "proposition", "corollary", "fact",
                        "remark", "definition", "claim", "conjecture"})
VERBATIM_ENVS = frozenset({"verbatim", "verbatim*", "Verbatim", "lstlisting",
                           "minted", "lean", "comment"})
TOKEN = re.compile(r"\\(?:(begin|end)\s*\{([^{}]+)\}|label\s*\{([^{}]+)\}|"
                   r"(input|include)\s*\{([^{}]*)\})")
BEGIN = re.compile(r"\\begin\s*\{([^{}]+)\}")
INLINE = re.compile(r"\\(?:verb\*?|lstinline\*?)(?![A-Za-z])")


class InventoryError(ValueError):
    pass


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def mask_tex(text: str) -> str:
    """Blank comments/code without removing newlines or shifting offsets."""
    out = list(text)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    i = 0
    while i < len(text):
        if text[i] == "%":
            k = i - 1
            while k >= 0 and text[k] == "\\":
                k -= 1
            if (i - 1 - k) % 2 == 0:
                end = text.find("\n", i)
                end = len(text) if end == -1 else end
                blank(i, end)
                i = end
                continue
        if text[i] == "\\":
            # An escaped backslash is not the start of a TeX command.
            k = i - 1
            while k >= 0 and text[k] == "\\":
                k -= 1
            if (i - 1 - k) % 2:
                i += 1
                continue
            m = BEGIN.match(text, i)
            if m and m.group(1) in VERBATIM_ENVS:
                end_marker = re.compile(r"\\end\s*\{" + re.escape(m.group(1)) + r"\}")
                end = end_marker.search(text, m.end())
                if not end:
                    raise InventoryError(f"unterminated code environment {m.group(1)}")
                blank(i, end.end())
                i = end.end()
                continue
            m = INLINE.match(text, i)
            if m:
                pos = m.end()
                if pos < len(text) and text[pos] == "[":
                    pos = text.find("]", pos) + 1
                    if pos == 0:
                        raise InventoryError("unterminated inline-code options")
                if pos >= len(text) or text[pos].isspace() or text[pos] == "{":
                    raise InventoryError("unsupported inline-code delimiter")
                end = text.find(text[pos], pos + 1)
                if end < 0 or "\n" in text[pos:end]:
                    raise InventoryError("unterminated inline code")
                blank(i, end + 1)
                i = end + 1
                continue
        i += 1
    return "".join(out)


def tokens(text: str) -> Iterator[re.Match[str]]:
    """Ignore command-looking text preceded by an odd escaped-backslash count."""
    for match in TOKEN.finditer(text):
        k = match.start() - 1
        while k >= 0 and text[k] == "\\":
            k -= 1
        if (match.start() - 1 - k) % 2 == 0:
            yield match


def safe_path(root: Path, path: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError as exc:
        raise InventoryError(f"path escapes repository: {path}") from exc
    if not resolved.is_file():
        raise InventoryError(f"missing source: {path}")
    return resolved


def inventory(root: Path, entry: Path) -> dict[str, Any]:
    root = root.resolve()
    entry = safe_path(root, root / entry)
    document_root = entry.parent
    sources: dict[str, str] = {}
    # Each segment is literal source text with its original path/line.
    segments: list[tuple[str, str, int]] = []

    def expand(path: Path, stack: tuple[Path, ...]) -> None:
        path = safe_path(root, path)
        if path in stack:
            raise InventoryError("cyclic TeX input: " + " -> ".join(p.name for p in (*stack, path)))
        raw = path.read_text(encoding="utf-8")
        name = path.relative_to(root).as_posix()
        sources[name] = sha(raw.encode())
        masked = mask_tex(raw)
        matched_inputs = {m.start() for m in tokens(masked) if m.group(4)}
        for command in re.finditer(r"(?<!\\)\\(?:input|include)(?![A-Za-z])", masked):
            if command.start() not in matched_inputs:
                raise InventoryError(f"unsupported unbraced or dynamic input in {name}")
        at = 0
        for m in tokens(masked):
            if not m.group(4):
                continue
            value = m.group(5).strip()
            if not value or any(c in value for c in "\\#{}$"):
                raise InventoryError(f"nonliteral TeX input in {name}: {value!r}")
            # TeX resolves input paths relative to the document working directory.
            rel = Path(value)
            if rel.is_absolute():
                raise InventoryError(f"absolute TeX input in {name}")
            if not rel.suffix:
                rel = rel.with_suffix(".tex")
            segments.append((masked[at:m.start()], name, raw.count("\n", 0, at) + 1))
            expand(document_root / rel, (*stack, path))
            at = m.end()
        segments.append((masked[at:], name, raw.count("\n", 0, at) + 1))

    expand(entry, ())
    text = "".join(piece for piece, _, _ in segments)
    offsets: list[tuple[int, int, str, int]] = []
    end = 0
    for piece, name, line in segments:
        offsets.append((end, end + len(piece), name, line))
        end += len(piece)

    def location(pos: int) -> tuple[str, int]:
        for a, b, name, line in offsets:
            if a <= pos < b:
                return name, line + text.count("\n", a, pos)
        raise InventoryError("missing source location")

    environments: list[tuple[str, dict[str, Any] | None]] = []
    claims: list[dict[str, Any]] = []
    seen_labels: dict[str, tuple[str, int]] = {}
    for m in tokens(text):
        event, env, label = m.group(1), m.group(2), m.group(3)
        name, line = location(m.start())
        if event == "begin":
            claim = None
            if env.removesuffix("*") in CLAIM_ENVS:
                claim = {"environment": env, "file": name, "line": line,
                         "labels": [], "status": "unmapped", "_start": m.start()}
            environments.append((env, claim))
        elif event == "end":
            if not environments or environments[-1][0] != env:
                raise InventoryError(f"unmatched end of {env} at {name}:{line}")
            _, claim = environments.pop()
            if claim is not None:
                start = claim.pop("_start")
                body = re.sub(r"\s+", " ", text[start:m.end()]).strip()
                claim["statement_source_sha256"] = sha(body.encode())
                claim["primary_label"] = claim["labels"][0] if claim["labels"] else None
                claims.append(claim)
        elif label is not None:
            if label in seen_labels:
                raise InventoryError(f"duplicate label {label} at {name}:{line}; first {seen_labels[label]}")
            seen_labels[label] = name, line
            for _, claim in reversed(environments):
                if claim is not None:
                    claim["labels"].append(label)
                    break
    if environments:
        raise InventoryError(f"unclosed TeX environment: {environments[-1][0]}")
    return {"schema": 1, "scope": "literal TeX inventory only; no verification claim",
            "entry": entry.relative_to(root).as_posix(), "sources": sources,
            "claims": claims, "unlabelled": sum(c["primary_label"] is None for c in claims),
            "all_labels": sorted(seen_labels),
            "limitations": ["custom macros and unnumbered prose require manual review",
                            "source hashes do not prove correspondence with Lean"]}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path.cwd())
    p.add_argument("--entry", type=Path, default=Path("docs/paper/main.tex"))
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    try:
        report = inventory(args.root, args.entry)
    except (InventoryError, OSError) as exc:
        print(f"inventory failed: {exc}", file=sys.stderr)
        return 2
    result = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
