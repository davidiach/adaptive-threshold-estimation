"""Restore only missing audited Tier5 dependency sources in a clean checkout.

By default verify snapshots and report missing files. Pass --restore to copy
missing files. Existing files must already match the audited bytes; conflicts
abort before any writes. No historical result, lock, or git state is modified.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SNAPSHOTS = HERE / "tier5-sources"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--restore", action="store_true")
    args = parser.parse_args()
    hashes = json.loads((HERE / "tier5_replay.json").read_text(encoding="utf-8"))["source_sha256_before"]
    missing = []
    for rel, expected in hashes.items():
        if not rel.startswith("lean/ThresholdHC/") or not rel.endswith(".lean"):
            raise ValueError(f"Unexpected snapshot path: {rel}")
        original, saved = (ROOT / rel).resolve(), (SNAPSHOTS / rel).resolve()
        if not original.is_relative_to(ROOT.resolve()) or not saved.is_relative_to(SNAPSHOTS.resolve()):
            raise ValueError(f"Path escapes intended directory: {rel}")
        if not saved.is_file() or sha(saved) != expected:
            raise ValueError(f"Snapshot missing or hash-conflicting: {rel}")
        if original.exists():
            if not original.is_file() or sha(original) != expected:
                raise ValueError(f"Refusing to replace existing conflicting source: {rel}")
        else:
            missing.append((original, saved, expected))
    # All snapshots and all existing destination files have passed before writing.
    if args.restore:
        for original, saved, expected in missing:
            original.parent.mkdir(parents=True, exist_ok=True)
            with original.open("xb") as out:
                out.write(saved.read_bytes())
            if sha(original) != expected:
                raise ValueError(f"Restored hash mismatch: {original}")
    print(json.dumps({"verified_snapshots": len(hashes), "missing_before": len(missing),
                      "restored": len(missing) if args.restore else 0,
                      "existing_files_overwritten": 0}))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
