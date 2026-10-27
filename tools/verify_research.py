"""Replay integrated research locks and diagnostics without replacing old evidence.

This checks source identity and finite examples, not the continuum paper proofs.
Historical validators retain their original checkout snapshots; this entry point
checks the integrated tree and all current frozen manifests instead.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RESEARCH = ROOT / 'research'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def verify_mapping(base, mapping):
    require(bool(mapping), f'Empty identity lock: {base}')
    for rel, expected in mapping.items():
        path = (base / rel).resolve()
        require(path.is_relative_to(ROOT), f'Lock path escapes repository: {rel}')
        require(path.is_file() and digest(path) == expected, f'Identity mismatch: {path}')
    return len(mapping)


def run(script, *args):
    subprocess.run([sys.executable, str(script), *map(str, args)], cwd=ROOT, check=True)


def copied_replay(script, out, result_name):
    folder = out / script.parent.name
    folder.mkdir()
    target = folder / script.name
    shutil.copyfile(script, target)
    run(target)
    return read(folder / result_name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    if args.output_dir:
        out = args.output_dir.resolve()
        out.mkdir(parents=True, exist_ok=False)
    else:
        out = Path(tempfile.mkdtemp(prefix='threshold-research-'))

    entries = 0
    for name in ('FROZEN.sha256', 'TIER3_FROZEN.sha256', 'TIER4_FROZEN.sha256',
                 'TIER5_FROZEN.sha256', 'TIER6_FROZEN.sha256'):
        mapping = {}
        for line in (ROOT / name).read_text(encoding='utf-8').splitlines():
            if line.strip() and not line.lstrip().startswith('#'):
                expected, rel = line.split(maxsplit=1)
                mapping[rel.strip()] = expected
        entries += verify_mapping(ROOT, mapping)

    critical = RESEARCH / '2026-10-27-nonlinear-critical'
    earlier = RESEARCH / '2026-10-27-critical-two'
    audit = RESEARCH / '2026-10-27-minimax-audit'
    locks = [
        (ROOT / 'lean/ThresholdHC/ResearchRouteA/SPEC_LOCK_v1.json', ROOT),
        (earlier / 'CHECKPOINT_LOCK_v1.json', ROOT),
        (audit / 'PAPER_CHECKPOINT_LOCK_v1.json', audit),
        (audit / 'formal/MODEL_EXTENSION_LOCK_v1.json', audit / 'formal'),
        (critical / 'CHECKPOINT_LOCK_v1.json', critical),
    ]
    for path, base in locks:
        lock = read(path)
        entries += verify_mapping(base, lock.get('sha256', lock.get('locked_sha256')))

    current = read(critical / 'CHECKPOINT_LOCK_v1.json')['sha256']
    inputs = set(re.findall(r'\\input\{([^}]+)\}', (critical / 'unrestricted.tex').read_text(encoding='utf-8')))
    require(inputs == set(current) - {'unrestricted.tex'}, 'Incomplete TeX input lock')
    for name in ('review.md', 'second-review.md'):
        review = (critical / name).read_text(encoding='utf-8')
        require(all(value in review for value in current.values()), f'Review source mismatch: {name}')
    compilation = read(critical / 'compilation.json')
    require(compilation['kind'] == 'success' and compilation['source_sha256'] == current,
            'Compilation identity mismatch')

    scalar = runpy.run_path(str(critical / 'validate.py'))['scalar_checks']()
    earlier_scalar = runpy.run_path(str(earlier / 'validate.py'))['scalar_checks']()
    run(critical / 'check_prefix.py', '--output', out / 'check_prefix_results.json')
    require(read(out / 'check_prefix_results.json') == read(critical / 'check_prefix_results.json'),
            'Finite-prefix replay differs from published evidence')

    route = RESEARCH / '2026-10-27-route-a'
    replay = copied_replay(route / 'check_construction.py', out, 'construction-checks.json')
    original = read(route / 'construction-checks.json')
    for key in ('rows', 'second_moment_coefficient'):
        require(replay[key] == original[key], f'Route A replay mismatch: {key}')
    exact = copied_replay(audit / 'check_exact.py', out, 'EXACT_CHECKS.json')
    require(exact == read(audit / 'EXACT_CHECKS.json'), 'Finite-support replay mismatch')

    fisher = runpy.run_path(str(earlier / 'fisher.py'))
    fisher['sanity_checks']()
    cases = read(earlier / 'fisher.json')['cases']
    for old in cases:
        new = fisher['run_case'](old['K'], old['horizon'])
        require(new['policy_sha256'] == old['policy_sha256'], 'Fisher policy differs')
        for key in ('expected_work', 'fisher_information', 'fisher_per_expected_work'):
            require(abs(new[key] - old[key]) <= 1e-12 * max(1.0, abs(old[key])),
                    f'Fisher replay mismatch: {key}')

    result = dict(valid=True, scope='Source identities and finite diagnostics; no new paper-proof certification',
                  lock_entries=entries, scalar_checks=len(scalar) + len(earlier_scalar),
                  fisher_cases=len(cases), route_cases=len(replay['rows']),
                  head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    (out / 'summary.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    print(f'Fresh evidence: {out}')


if __name__ == '__main__':
    main()
