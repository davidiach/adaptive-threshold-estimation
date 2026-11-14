"""Verify every hash-manifest lock in one read-only pass.

`tools/freeze.py --verify` checks the lines present in FROZEN.sha256 only, so
a deleted line, with the file it named then edited, still prints OK; freeze.py
is itself frozen and cannot be changed. This check also requires the manifest
to list exactly the files freeze.py freezes, and verifies the Tier 3 to Tier 6
locks (Tier 6 pins FROZEN.sha256 and the earlier manifests) and the checksum
manifests of the published manuscripts and records.

The specification freeze records under tools/ are checked by the audits that
read them. Prints a summary; writes nothing.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import sys

import freeze

ROOT = Path(__file__).resolve().parents[1]
TIER_LOCKS = ["TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256", "TIER5_FROZEN.sha256",
              "TIER6_FROZEN.sha256"]
CHECKSUM_MANIFESTS = [
    "paper/finite-gap-rare-events/SHA256SUMS",
    "paper/finite-gap-rare-events/revision-2/SHA256SUMS",
    "paper/rare-event/v2/MANIFEST.sha256",
    "paper/rare-event/audit/MANIFEST.sha256",
    "results/selection-approximation-20261106/SHA256SUMS",
]
LINE = re.compile(r"^([0-9a-f]{64})\s+\*?(\S.*?)\s*$")


def entries(manifest: Path) -> list[tuple[str, str]]:
    """The (hash, path) lines of a manifest; any other non-comment line is an error."""
    found = []
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        match = LINE.match(line)
        if match is None:
            raise ValueError(f"{manifest.name}: unreadable line {line!r}")
        found.append((match[1], match[2]))
    if not found:
        raise ValueError(f"{manifest.name}: no entries")
    return found


def mismatches(manifest: Path, base: Path) -> list[str]:
    label = manifest.relative_to(ROOT).as_posix() if manifest.is_relative_to(ROOT) else manifest.name
    bad = []
    for digest, name in entries(manifest):
        path = base / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            bad.append(f"{label}: {name}")
    return bad


def frozen_coverage(manifest: Path, expected: list[str]) -> list[str]:
    listed = [name for _, name in entries(manifest)]
    problems = [f"FROZEN.sha256 no longer lists {name}" for name in expected if name not in listed]
    problems += [f"FROZEN.sha256 lists {name}, which freeze.py does not freeze"
                 for name in listed if name not in expected]
    if len(listed) != len(set(listed)):
        problems.append("FROZEN.sha256 lists a file twice")
    return problems


def main() -> int:
    problems = frozen_coverage(ROOT / "FROZEN.sha256", freeze.FROZEN)
    problems += mismatches(ROOT / "FROZEN.sha256", ROOT)
    for lock in TIER_LOCKS:
        problems += mismatches(ROOT / lock, ROOT)
    for manifest in CHECKSUM_MANIFESTS:
        path = ROOT / manifest
        problems += mismatches(path, path.parent)
    if problems:
        print("Lock verification failed:")
        print("\n".join("  " + problem for problem in problems))
        return 1
    count = sum(len(entries(ROOT / m)) for m in ["FROZEN.sha256", *TIER_LOCKS, *CHECKSUM_MANIFESTS])
    print(f"Verified {count} locked hashes in {1 + len(TIER_LOCKS) + len(CHECKSUM_MANIFESTS)} "
          f"manifests; FROZEN.sha256 lists exactly the {len(freeze.FROZEN)} files freeze.py freezes.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
