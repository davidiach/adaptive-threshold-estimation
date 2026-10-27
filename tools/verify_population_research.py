"""Replay population and feedback evidence in disposable copies.

Preserves the original paper checkpoints and all recorded outputs. Exact finite
certificates and seeded replay are not proofs of unrestricted minimax claims.
"""
from pathlib import Path
import json
import shutil
import tempfile

from verify_research import ROOT, RESEARCH, digest, read, require, run, verify_mapping


def main():
    names = ['2026-10-27-population-step', '2026-10-27-nonlinear-population']
    entries = 0
    for name in names:
        package = RESEARCH / name
        seal = package / 'CHECKPOINT_SHA256.json'
        acceptance = read(package / 'ACCEPTANCE.json')
        require(acceptance['valid'] and all(acceptance['checks'].values()),
                f'Historical acceptance failed: {name}')
        require(digest(seal) == acceptance['checkpoint_sha256'], f'Checkpoint identity differs: {name}')
        entries += verify_mapping(package, read(seal)['files'])

    runtime = ROOT / '.runtime'
    runtime.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix='population-replay-', dir=runtime)).resolve()
    require(scratch.is_relative_to(runtime.resolve()), 'Replay directory escaped runtime')
    pop, feedback = [scratch / 'research' / name for name in names]
    shutil.copytree(RESEARCH / names[0], pop,
                    ignore=shutil.ignore_patterns('__pycache__', 'FINITE_RESULTS.json', 'FINITE_VERIFY.json'))
    shutil.copytree(RESEARCH / names[1], feedback,
                    ignore=shutil.ignore_patterns('__pycache__', 'REPLAY.json'))

    for script in ('audit/check_arithmetic.py', 'audit/check_small_bias.py',
                   'audit/check_population.py', 'upper/check_exact.py'):
        run(pop / script)
    run(pop / 'finite_bayes.py', 'run')
    run(pop / 'verify_finite.py')
    original_pop = RESEARCH / names[0]
    require(read(pop / 'FINITE_RESULTS.json')['rows'] == read(original_pop / 'FINITE_RESULTS.json')['rows'],
            'Finite Bayes replay differs')
    for case in ('two_scales', 'three_scales'):
        require(read(pop / f'{case}_policy.json') == read(original_pop / f'{case}_policy.json'),
                f'Finite policy replay differs: {case}')

    for script in ('audit/replay.py', 'audit/replay_v2.py', 'audit/check_experiment.py'):
        run(feedback / script, 'integration_replay_' + Path(script).stem + '.json')
    run(feedback / 'replay_experiment.py')
    sampled = read(feedback / 'REPLAY.json')
    require(sampled['valid'] and sampled['cells'] == 240, 'Incomplete feedback experiment replay')
    for name in names:
        package = RESEARCH / name
        verify_mapping(package, read(package / 'CHECKPOINT_SHA256.json')['files'])

    result = dict(valid=True, package_lock_entries=entries, finite_bayes_cases=16,
                  independent_finite_comparisons=10, feedback_replay_cells=sampled['cells'],
                  scope='Source identities, exact finite certificates, and frozen experiment replay; no new theorem certification')
    (scratch / 'summary.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    print(f'Fresh evidence: {scratch}')


if __name__ == '__main__':
    main()
