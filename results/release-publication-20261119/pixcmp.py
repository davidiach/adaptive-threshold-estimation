"""Compare two PDFs page by page by rendered body pixels.

Each page is rendered with Poppler pdftoppm at 100 dpi in 8-bit grey. The
body pixels, leaving out a 60 pt band at the top and at the bottom of the page
(running header and page number), are hashed with SHA-256. A page of the new
PDF is unchanged if its body hash equals that of the baseline page with the
same number, relocated if it equals that of another baseline page, and
changed otherwise.

usage: python pixcmp.py BASELINE.pdf NEW.pdf  (prints JSON)
"""
import hashlib, json, subprocess, sys, tempfile
from pathlib import Path

DPI, BAND_PT = 100, 60
BAND = round(BAND_PT / 72 * DPI)


def body_hashes(pdf: str) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["/usr/bin/pdftoppm", "-r", str(DPI), "-gray", pdf, f"{tmp}/p"], check=True)
        hashes = []
        for page in sorted(Path(tmp).glob("p-*.pgm"), key=lambda p: int(p.stem.split("-")[1])):
            data = page.read_bytes()
            # binary PGM: "P5\n<w> <h>\n<max>\n" then w*h bytes
            parts = data.split(b"\n", 3)
            width, height = map(int, parts[1].split())
            pixels = parts[3]
            assert len(pixels) == width * height, page
            hashes.append(hashlib.sha256(pixels[BAND * width:(height - BAND) * width]).hexdigest())
        return hashes


def main() -> None:
    base, new = body_hashes(sys.argv[1]), body_hashes(sys.argv[2])
    where = {}
    for number, digest in enumerate(base, 1):
        where.setdefault(digest, []).append(number)
    same, relocated, changed = [], {}, []
    for number, digest in enumerate(new, 1):
        if number <= len(base) and base[number - 1] == digest:
            same.append(number)
        elif digest in where:
            relocated[number] = where[digest][0]
        else:
            changed.append(number)
    print(json.dumps({"baseline_pages": len(base), "pages": len(new), "band_px": BAND,
                      "unchanged_pages_same_number": len(same), "relocated_pages": relocated,
                      "changed_pages": changed}, indent=1))


if __name__ == "__main__":
    main()
