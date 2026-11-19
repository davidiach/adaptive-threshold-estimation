"""Verify every hash-manifest lock in one read-only pass.

`tools/freeze.py --verify` checks the lines present in FROZEN.sha256 only, so
a deleted line, with the file it named then edited, still prints OK; freeze.py
is itself frozen and cannot be changed. This check also requires the manifest
to list exactly the files freeze.py freezes, and verifies the Tier 3 to Tier 6
locks (Tier 6 pins FROZEN.sha256 and the earlier manifests) and the checksum
manifests of the published manuscripts and records.

A line deleted from a manifest that no other manifest lists would pass the same
way. The Tier 6 lock and the five checksum manifests are such manifests, so
their own digests are pinned here (PINNED_MANIFESTS), and every checked
manifest must be pinned here or listed by a checked tier lock. A deliberate
change to one of them updates its digest here in the same commit; changing a
frozen lock still needs the owner's authorization and a FREEZE_LOG entry.

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
PINNED_MANIFESTS = {
    "TIER6_FROZEN.sha256":
        "08a5ec35f7ac05fd6f7f4f123489eec54f0beeaee469edf3858553f9abb32e2a",
    "paper/finite-gap-rare-events/SHA256SUMS":
        "bea2060927beddfe4af594a5df6593326d377578af5c14a18687f1bb05b42119",
    "paper/finite-gap-rare-events/revision-2/SHA256SUMS":
        "4e51caefce8b7b03743fe461aed1a7bc29e1b42ca092f1d859ac0e4c9a044759",
    "paper/rare-event/v2/MANIFEST.sha256":
        "86befae37419490110fe4d1fb753d8776373e27e8fab2294696f4e83caed2612",
    "paper/rare-event/audit/MANIFEST.sha256":
        "27d741a487c45841b58bd14f392d78b6ce9adabf65e845cbc72b3d7a5f96c31e",
    "results/selection-approximation-20261106/SHA256SUMS":
        "1c972374f67a4c5061961592886f2b4852dbc73e0140dee8983ea61c8ca8dd16",
}
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


def pinned_problems(root: Path = ROOT, pinned: dict[str, str] = PINNED_MANIFESTS,
                    manifests: list[str] | None = None) -> list[str]:
    """Pinned manifests that changed, and checked manifests that nothing pins.

    A manifest counts as pinned when its digest is in `pinned` or a checked tier
    lock lists it; otherwise a line deleted from it would go unnoticed.
    """
    checked = ["FROZEN.sha256", *TIER_LOCKS, *CHECKSUM_MANIFESTS] if manifests is None else manifests
    listed = {name for lock in TIER_LOCKS if (root / lock).is_file() for _, name in entries(root / lock)}
    problems = [f"{name}: neither pinned in verify_locks.py nor listed by a tier lock"
                for name in checked if name not in pinned and name not in listed]
    for name, digest in pinned.items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            problems.append(f"{name}: changed since its digest was pinned in verify_locks.py")
    return problems


def main() -> int:
    problems = frozen_coverage(ROOT / "FROZEN.sha256", freeze.FROZEN)
    problems += pinned_problems()
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
          f"manifests; FROZEN.sha256 lists exactly the {len(freeze.FROZEN)} files freeze.py freezes; "
          f"the {len(PINNED_MANIFESTS)} manifests no tier lock lists match their pinned digests.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
