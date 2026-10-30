"""Output handling shared by this package's replay scripts.

By default a replay writes into a new directory under .runtime/ and compares
its records with the tracked evidence/ files, which it leaves untouched.
--write-evidence rewrites the tracked files instead. Apache-2.0.
"""
from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import argparse

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
EVIDENCE = PACKAGE / 'evidence'


def output_directory(description: str | None) -> tuple[Path, bool]:
    """Return the directory to write and whether it is the tracked evidence."""
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--output-dir', type=Path,
                        help='new directory for regenerated records (default: under .runtime/)')
    parser.add_argument('--write-evidence', action='store_true',
                        help='rewrite the tracked evidence/ files instead of comparing with them')
    args = parser.parse_args()
    if args.write_evidence:
        return EVIDENCE, True
    out = args.output_dir or ROOT / '.runtime/certified-selection' / datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out.mkdir(parents=True, exist_ok=False)
    return out, False


def compare(out: Path, names: list[str]) -> int:
    """Return 0 when every regenerated record matches its tracked bytes."""
    different = [name for name in names
                 if not (EVIDENCE / name).is_file()
                 or (out / name).read_bytes() != (EVIDENCE / name).read_bytes()]
    for name in different:
        print(f'DIFFERS from tracked evidence: {name}')
    print(f'{len(names) - len(different)}/{len(names)} records match evidence/; '
          f'regenerated copies are in {out}')
    return 1 if different else 0
