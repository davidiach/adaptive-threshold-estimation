"""Hash lock for the stopping-program specification and its dependencies.

The three full targets in lean/ThresholdHC/StoppingProgram/Specification.lean
are checked for exact type by verify_stopping_dual.py,
verify_stopping_program_upper.py and verify_finite_risk_certificate.py. Those
checks name the target definitions, so this lock fixes what the definitions
say. tools/stopping_program_specification_freeze.json records its chronology.
"""
from __future__ import annotations

import json
from pathlib import Path

from verify_blind_upper_components import sha, validate_dependency_freeze

ROOT = Path(__file__).resolve().parents[1]
SPECIFICATION = ROOT / "lean/ThresholdHC/StoppingProgram/Specification.lean"
FREEZE = ROOT / "tools/stopping_program_specification_freeze.json"
FROZEN = {
    "lean/ThresholdHC/StoppingProgram/Specification.lean":
        "c9eb621ce2bde7507c2e662fbf5d5d1c29815393cf925444590cab5c0ebec871",
}


def validate_stopping_specification() -> None:
    freeze = json.loads(FREEZE.read_text(encoding="utf-8"))
    if freeze["source_sha256"] != FROZEN or any(sha(ROOT / p) != h for p, h in FROZEN.items()):
        raise ValueError("Frozen stopping-program specification changed")
    validate_dependency_freeze(SPECIFICATION, freeze)
