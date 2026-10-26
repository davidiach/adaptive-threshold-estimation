"""Verify the supplied research package against its original manifest."""
from hashlib import sha256
from pathlib import Path

root = Path(__file__).resolve().parents[1] / "inputs" / "next-phase"
count = 0
for line in (root / "MANIFEST_SHA256.txt").read_text().splitlines():
    if not line.strip() or line.startswith("#"):
        continue
    expected, name = line.split(maxsplit=1)
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()):
        raise SystemExit(f"Manifest path outside input package: {name}")
    actual = sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Input modified: {name}")
    count += 1
print(f"Verified {count} original input files.")
