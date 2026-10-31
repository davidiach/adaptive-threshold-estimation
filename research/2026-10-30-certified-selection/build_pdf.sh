#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT
pandoc "$HERE/NOTE.md" -f markdown+tex_math_dollars -s --number-sections \
  -V fontsize=11pt -V papersize=a4 -V geometry:margin=0.82in \
  -V urlcolor=black -V linkcolor=black -V documentclass=article \
  -H "$HERE/pdf-header.tex" -o "$BUILD/NOTE.tex"
(cd "$BUILD" && pdflatex -interaction=nonstopmode -halt-on-error NOTE.tex > build.log) || { cat "$BUILD/build.log"; exit 1; }
(cd "$BUILD" && pdflatex -interaction=nonstopmode -halt-on-error NOTE.tex >> build.log) || { cat "$BUILD/build.log"; exit 1; }
cp "$BUILD/NOTE.tex" "$HERE/NOTE.tex"
cp "$BUILD/NOTE.pdf" "$HERE/NOTE.pdf"
grep -E 'Overfull|Undefined|LaTeX Warning' "$BUILD/build.log" || true
printf 'Built %s\n' "$HERE/NOTE.pdf"
