"""Check the v6 build record that paper/v6/README.md presents as current.

The README's first link line names the current manuscript PDF and its build
record under paper/v6/builds/. Build records are written by hand after each
typeset, so this check guards the facts a reader relies on.

Errors (exit 1): the record does not describe its own PDF (SHA-256, size or
page count), lacks a required field, or lists a changed page that its visual
check does not cover or that lies outside the document.

Staleness (warning; exit 1 only with --strict): the record's TeX and
status.json hashes no longer match the current sources, so the linked PDF no
longer typesets the tree. Publishing a new build, or relabelling the link,
resolves it. The check reads files only and needs no TeX installation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
V6 = ROOT / "paper" / "v6"
LINKS = re.compile(r"\[Current manuscript\]\((builds/[^)]+\.pdf)\).*?"
                   r"\[Build record\]\((builds/[^)]+\.json)\)")
STATUS_KEYS = ("status_manifest_sha256", "status_source_sha256")
REQUIRED = ("pages", "pdf_sha256", "pdf_bytes", "tex_sources", "source_commit")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def current_links(readme: Path = V6 / "README.md") -> tuple[Path, Path]:
    for line in readme.read_text(encoding="utf-8").splitlines():
        match = LINKS.search(line)
        if match:
            return readme.parent / match[1], readme.parent / match[2]
    raise ValueError(f"{readme} has no 'Current manuscript' and 'Build record' link line")


def pdf_pages(pdf: Path) -> int | None:
    """The page count from pdfinfo, or None when poppler is not installed."""
    try:
        out = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return None
    match = re.search(r"^Pages:\s+(\d+)", out, re.M)
    return int(match[1]) if match else None


def record_errors(record: dict, pdf: Path, pages: int | None) -> list[str]:
    errors = [f"missing field {key!r}" for key in REQUIRED if key not in record]
    if not any(key in record for key in STATUS_KEYS):
        errors.append("missing status hash (status_manifest_sha256)")
    if errors:
        return errors
    if not pdf.is_file():
        return [f"PDF {pdf.name} does not exist"]
    data = pdf.read_bytes()
    if sha(data) != record["pdf_sha256"]:
        errors.append(f"pdf_sha256 does not match {pdf.name}")
    if len(data) != record["pdf_bytes"]:
        errors.append(f"pdf_bytes {record['pdf_bytes']} != actual {len(data)}")
    if pages is not None and pages != record["pages"]:
        errors.append(f"pages {record['pages']} != actual {pages}")
    total = record["pages"]
    changed = record.get("changed_pages", [])
    visual = record.get("visual_pages_checked")
    for page in changed + list(visual or []):
        if not (isinstance(page, int) and 1 <= page <= total):
            errors.append(f"page {page!r} lies outside 1..{total}")
    if visual is not None and set(changed) - set(visual):
        errors.append("changed pages not visually checked: "
                      + ", ".join(map(str, sorted(set(changed) - set(visual)))))
    for new, old in record.get("relocated_pages", {}).items():
        if not (str(new).isdigit() and 1 <= int(new) <= total and isinstance(old, int) and old >= 1):
            errors.append(f"relocated_pages entry {new!r}: {old!r} is not a page mapping")
    return errors


def staleness(record: dict, sources: Path = V6) -> list[str]:
    current = {p.name: sha(p.read_bytes()) for p in sorted(sources.glob("*.tex"))}
    recorded = record["tex_sources"]
    notes = [f"{name} changed since the build" for name in sorted(current)
             if name in recorded and current[name] != recorded[name]]
    notes += [f"{name} is new since the build" for name in sorted(set(current) - set(recorded))]
    notes += [f"{name} was removed since the build" for name in sorted(set(recorded) - set(current))]
    status = next(record[key] for key in STATUS_KEYS if key in record)
    if sha((sources / "status.json").read_bytes()) != status:
        notes.append("status.json changed since the build")
    return notes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--strict", action="store_true",
                        help="also fail when the current build no longer matches the sources")
    args = parser.parse_args(argv)
    pdf, record_path = current_links()
    record = json.loads(record_path.read_text(encoding="utf-8"))
    name = record_path.relative_to(ROOT).as_posix()
    errors = record_errors(record, pdf, pdf_pages(pdf))
    if errors:
        print("\n".join(f"::error::{name}: {error}" for error in errors))
        return 1
    notes = staleness(record)
    for note in notes:
        print(f"::warning::{name}: the current manuscript is stale: {note}")
    if notes and args.strict:
        return 1
    print(f"{name} describes its PDF" + ("" if notes else " and matches the current v6 sources") + ".")
    return 0


if __name__ == "__main__":
    sys.exit(main())
