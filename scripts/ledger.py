# /// script
# requires-python = ">=3.11"
# ///
"""Ledger of Ramanujan's results.

The source of truth is one TOML file per result in data/entries/.
This script checks the entries against the Lean library and writes
data/ledger.db (SQLite, generated, not committed).

  uv run scripts/ledger.py check   # validate entries and link them to Lean
  uv run scripts/ledger.py build   # check, then write data/ledger.db

Run after `lake build`. The axiom allowlist check of the whole library is
done separately by axiom-audit (lean-action `axiom-audit: true`); `check`
re-runs `#print axioms` for each theorem the ledger names, so a ledger entry
cannot point at a missing theorem or at one that depends on sorryAx.
"""

from __future__ import annotations

import json
import re
import sqlite3
import subprocess
import sys
import tomllib
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENTRIES = ROOT / "data" / "entries"
DB = ROOT / "data" / "ledger.db"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATES = ["registered", "formalized", "proved", "verified", "rejected"]
VERDICTS = {"pending", "match", "mismatch"}
# B<part>.<chapter>.<entry>[.<sub-part in roman numerals>]
ID_RE = re.compile(r"^B[1-5]\.\d+\.\d+(\.[ivx]+)?$")
REQUIRED = {
    "source": ["book", "part", "chapter", "entry", "page", "citations", "original_checked"],
    "statement": ["latex", "domain", "meaning"],
    "lean": ["file", "theorems"],
    "status": ["state", "depends_on"],
    "semantic_audit": ["verdict", "author", "reviewer"],
}


def load_entries() -> list[dict]:
    entries = []
    for path in sorted(ENTRIES.glob("*.toml")):
        with path.open("rb") as f:
            e = tomllib.load(f)
        e["_path"] = path
        entries.append(e)
    return entries


def validate(entries: list[dict]) -> list[str]:
    errors: list[str] = []
    ids = {e.get("id") for e in entries}
    seen: set[str] = set()
    for e in entries:
        p = e["_path"].name
        eid = e.get("id", "")
        if not ID_RE.match(eid):
            errors.append(f"{p}: id {eid!r} does not match {ID_RE.pattern}")
        if p != f"{eid}.toml":
            errors.append(f"{p}: file name must be {eid}.toml")
        if eid in seen:
            errors.append(f"{p}: duplicate id {eid}")
        seen.add(eid)
        for table, keys in REQUIRED.items():
            for k in keys:
                if k not in e.get(table, {}):
                    errors.append(f"{p}: missing [{table}].{k}")
        state = e.get("status", {}).get("state")
        if state not in STATES:
            errors.append(f"{p}: state {state!r} not in {STATES}")
        verdict = e.get("semantic_audit", {}).get("verdict")
        if verdict not in VERDICTS:
            errors.append(f"{p}: verdict {verdict!r} not in {sorted(VERDICTS)}")
        theorems = e.get("lean", {}).get("theorems", [])
        if state in ("proved", "verified"):
            if not theorems:
                errors.append(f"{p}: state {state} needs [lean].theorems")
            lean_file = e.get("lean", {}).get("file", "")
            if not lean_file or not (ROOT / lean_file).is_file():
                errors.append(f"{p}: [lean].file {lean_file!r} does not exist")
        if state == "verified":
            sa = e["semantic_audit"]
            if verdict != "match":
                errors.append(f"{p}: verified needs semantic_audit.verdict = match")
            if not sa.get("reviewer") or sa.get("reviewer") == sa.get("author"):
                errors.append(f"{p}: verified needs a reviewer different from the author")
        if verdict == "mismatch" and state in ("proved", "verified"):
            errors.append(f"{p}: statement judged mismatch but state is {state}")
        for dep in e.get("status", {}).get("depends_on", []):
            if dep not in ids:
                errors.append(f"{p}: depends_on {dep} is not a ledger id")
    return errors


AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOM_LINE = re.compile(r"'([^']+)' does not depend on any axioms")


def print_axioms(names: list[str]) -> tuple[dict[str, set[str]], str]:
    """Run `#print axioms` on each name. Returns axioms per name and raw output."""
    if not names:
        return {}, ""
    src = ["import RamanujanLean"] + [f"#print axioms {n}" for n in names]
    tmp = ROOT / ".lake" / "ledger_axioms.lean"
    tmp.parent.mkdir(exist_ok=True)
    tmp.write_text("\n".join(src) + "\n")
    proc = subprocess.run(
        ["lake", "env", "lean", str(tmp)], cwd=ROOT, capture_output=True, text=True
    )
    out = proc.stdout + proc.stderr
    found: dict[str, set[str]] = {}
    for m in AXIOM_LINE.finditer(out):
        found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in NO_AXIOM_LINE.finditer(out):
        found[m.group(1)] = set()
    return found, out


def check_lean(entries: list[dict]) -> tuple[list[str], dict[str, set[str]]]:
    errors: list[str] = []
    names = [t for e in entries for t in e.get("lean", {}).get("theorems", [])]
    found, out = print_axioms(names)
    for e in entries:
        for t in e.get("lean", {}).get("theorems", []):
            if t not in found:
                errors.append(f"{e['_path'].name}: theorem {t} not found in RamanujanLean")
                continue
            bad = found[t] - ALLOWED_AXIOMS
            if bad:
                errors.append(f"{e['_path'].name}: {t} uses disallowed axioms {sorted(bad)}")
    if errors and "error" in out:
        errors.append("lean output:\n" + out.strip())
    return errors, found


def write_db(entries: list[dict], axioms: dict[str, set[str]]) -> None:
    DB.unlink(missing_ok=True)
    con = sqlite3.connect(DB)
    con.executescript(
        """
        CREATE TABLE entries (
          id TEXT PRIMARY KEY, title TEXT,
          book TEXT, part INTEGER, chapter INTEGER, entry TEXT, page INTEGER,
          original_checked INTEGER, citations TEXT,
          latex TEXT, domain TEXT, meaning TEXT, known_proofs TEXT,
          lean_file TEXT, formulation_notes TEXT, reuses TEXT,
          state TEXT, depends_on TEXT,
          audit_verdict TEXT, audit_author TEXT, audit_reviewer TEXT, audit_notes TEXT,
          cost_measured INTEGER, cost_notes TEXT
        );
        CREATE TABLE lean_theorems (
          entry_id TEXT REFERENCES entries(id), name TEXT, axioms TEXT
        );
        CREATE TABLE runs (checked_at TEXT, git_commit TEXT, ok INTEGER);
        """
    )
    for e in entries:
        s, st, ln = e["source"], e["statement"], e["lean"]
        sa, cost = e["semantic_audit"], e.get("cost", {})
        con.execute(
            "INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                e["id"], e.get("title"),
                s["book"], s["part"], s["chapter"], s["entry"], s["page"],
                int(s["original_checked"]), json.dumps(s["citations"], ensure_ascii=False),
                st["latex"], st["domain"], st["meaning"],
                json.dumps(st.get("known_proofs", []), ensure_ascii=False),
                ln["file"], ln.get("formulation_notes", ""),
                json.dumps(ln.get("reuses", []), ensure_ascii=False),
                e["status"]["state"], json.dumps(e["status"]["depends_on"]),
                sa["verdict"], sa["author"], sa["reviewer"], sa.get("notes", ""),
                int(cost.get("measured", False)), cost.get("notes", ""),
            ),
        )
        for t in ln["theorems"]:
            con.execute(
                "INSERT INTO lean_theorems VALUES (?,?,?)",
                (e["id"], t, json.dumps(sorted(axioms.get(t, set())))),
            )
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True
    ).stdout.strip()
    con.execute(
        "INSERT INTO runs VALUES (?,?,?)",
        (datetime.now(timezone.utc).isoformat(), commit, 1),
    )
    con.commit()
    con.close()


def summary(entries: list[dict]) -> str:
    counts = {s: 0 for s in STATES}
    for e in entries:
        counts[e["status"]["state"]] += 1
    return f"{len(entries)} entries: " + ", ".join(f"{k}={v}" for k, v in counts.items())


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd not in ("check", "build"):
        print(__doc__)
        return 2
    entries = load_entries()
    if not entries:
        print("no entries in data/entries")
        return 1
    errors = validate(entries)
    lean_errors, axioms = check_lean(entries)
    errors += lean_errors
    if errors:
        print("ledger check failed:")
        for err in errors:
            print("  " + err)
        return 1
    print("ledger check ok. " + summary(entries))
    if cmd == "build":
        write_db(entries, axioms)
        print(f"wrote {DB.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
