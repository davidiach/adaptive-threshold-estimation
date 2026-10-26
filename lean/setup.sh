#!/usr/bin/env bash
# Phase 0 setup for the Lean track.
# Needs network access to github.com, raw.githubusercontent.com and Mathlib's
# build-cache host. Without the cache, building Mathlib takes hours.
set -euo pipefail
cd "$(dirname "$0")"

if ! command -v lake >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

if [ ! -f lakefile.toml ]; then
  # Use Mathlib's own toolchain so the two always match.
  curl -sSfL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain \
    -o lean-toolchain
  cat > lakefile.toml <<'TOML'
name = "ThresholdHC"
defaultTargets = ["ThresholdHC"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "master"

[[lean_lib]]
name = "ThresholdHC"
TOML
  lake update          # pins Mathlib in lake-manifest.json
fi

lake exe cache get     # downloads prebuilt Mathlib
lake build             # builds Statements.lean and the sorry stubs
echo
echo "Phase 0 next steps:"
echo "  1. If Statements.lean failed to elaborate, apply ONLY meaning-preserving fixes"
echo "     and log each one (before/after/why) in FREEZE_LOG.md."
echo "  2. python tools/check_targets_numeric.py"
echo "  3. python tools/freeze.py --init"
echo "  4. python tools/score.py   (expect 0/60, all targets 'sorry')"
