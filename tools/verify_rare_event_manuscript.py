"""Verify the v2 rare-event package and replay its finite checks without mutation.

This checks artifact identity, exact finite certificates, and falsification
computations. It is not a formal proof of the manuscript's general theorems.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / 'paper/rare-event'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest(folder, exempt=()):
    manifest = folder / 'MANIFEST.sha256'
    entries = {}
    for line in manifest.read_text(encoding='utf-8').splitlines():
        require(bool(re.fullmatch(r'[0-9a-f]{64}  .+', line)), 'Malformed manifest line')
        expected, name = line.split('  ', 1)
        path = (folder / name).resolve()
        require(path.is_relative_to(folder.resolve()), f'Manifest path escapes package: {name}')
        require(name not in entries, f'Duplicate manifest entry: {name}')
        require(path.is_file() and digest(path) == expected, f'Identity mismatch: {path}')
        entries[name] = expected
    require(bool(entries), 'Empty manifest')
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
    expected_names = set(entries) | {'MANIFEST.sha256'} | set(exempt)
    require(actual == expected_names, f'Unregistered/missing package files: {actual ^ expected_names}')
    return len(entries)


def run(script, cwd):
    result = subprocess.run([sys.executable, '-B', str(script)], cwd=cwd,
                            capture_output=True, text=True, encoding='utf-8')
    require(result.returncode == 0, f'{script.name} failed:\n{result.stdout}\n{result.stderr}')


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def main():
    require(sys.flags.optimize == 0,
            'Run without -O: historical audit routines use assertion checks')
    payload = PACKAGE / 'v2'
    audit = PACKAGE / 'audit'
    publication = read_json(PACKAGE / 'PUBLICATION.json')
    require(digest(payload / 'MANIFEST.sha256') == publication['payload_manifest_sha256'],
            'Delivered payload manifest changed')
    require(digest(audit / 'MANIFEST.sha256') == publication['audit_manifest_sha256'],
            'Historical audit manifest changed')
    counts = {'payload_files': verify_manifest(payload),
              'historical_audit_files': verify_manifest(audit, exempt=('README.md',))}
    require(digest(payload / 'main.pdf') == publication['delivered_pdf_sha256'], 'PDF identity changed')
    before = {p: digest(p) for p in PACKAGE.rglob('*') if p.is_file()}
    with tempfile.TemporaryDirectory(prefix='rare-event-v2-') as tmp:
        copy = Path(tmp) / 'v2'
        shutil.copytree(payload, copy)
        checks = copy / 'checks'
        run(checks / 'self_check_certificates.py', copy)
        run(checks / 'verify_revisions.py', copy)
        certificate = read_json(checks / 'certificate_self_check.json')
        require(certificate == read_json(payload / 'checks/certificate_self_check.json'),
                'Certificate replay disagrees with published result')
        revisions = read_json(checks / 'revision_checks.json')
        require(revisions == read_json(payload / 'checks/revision_checks.json'),
                'Revision checker disagrees with published result')
        # Import only the independent mathematical routines. The unchanged
        # historical main() points to its original PDF and result locations.
        source = audit / 'revision/revised_changes_adversarial_audit.py'
        temporary_source = Path(tmp) / source.name
        shutil.copyfile(source, temporary_source)
        spec = importlib.util.spec_from_file_location('rare_event_revision_audit', temporary_source)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        replay = {
            'new_examples_and_constants': module.new_examples_and_constants(),
            'selection_and_variational_optimizer': module.numerical_selection_trials(),
            'continuous_genie_counterexample': module.continuous_genie_counterexample(),
            'finite_divergence_genie': module.finite_genie_trials(),
        }
        require(replay['new_examples_and_constants']['unique_winner_mask'] == 5,
                'Noninterval example changed')
        require(replay['finite_divergence_genie']['cap_comparisons'] == 288,
                'Genie replay incomplete')
    after = {p: digest(p) for p in PACKAGE.rglob('*') if p.is_file()}
    require(before == after, 'Verification modified the publication package')
    print(json.dumps({
        'status': 'PASS', **counts,
        'v2_pdf_sha256': publication['delivered_pdf_sha256'],
        'exact_certificates': certificate['exact_certificates_rechecked'],
        'exact_stopping_decisions': certificate['exact_stopping_decisions_rechecked'],
        'corruptions_rejected': len(certificate['targeted_corruptions_rejected']),
        'revision_checks': revisions['status'],
        'selection_laws': replay['selection_and_variational_optimizer']['laws'],
        'hard_assignments': replay['selection_and_variational_optimizer']['enumerated_hard_assignments'],
        'genie_comparisons': replay['finite_divergence_genie']['cap_comparisons'],
        'published_records_unchanged': True,
        'scope': 'Artifact identity and finite checks, not formal verification of general theorems.',
    }, indent=2))


if __name__ == '__main__':
    main()
