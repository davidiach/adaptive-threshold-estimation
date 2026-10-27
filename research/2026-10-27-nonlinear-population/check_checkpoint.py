"""Check the scoped evidence and seal it without rewriting historical outputs."""
from pathlib import Path
from datetime import datetime, timezone
import csv, hashlib, json, platform, subprocess, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '3897d390d2fdd66d6f3f4b84fabfe523b0e031ba'
START = 'd75c775633df545b892e69fc876930d6d2dcc329'
BRANCH = 'research/nonlinear-feedback-20261027'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((HERE / name).read_text(encoding='utf-8'))
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True, encoding='utf-8').strip()
def matches(hashes): return all(sha(HERE / p) == value for p, value in hashes.items())

def main():
    output, seal = HERE / 'ACCEPTANCE.json', HERE / 'CHECKPOINT_SHA256.json'
    if output.exists() or seal.exists():
        raise RuntimeError('Refuse to overwrite a completed checkpoint')
    checks = {}
    for name in ['audit/replay_final.json', 'audit/replay_v2.json', 'audit/experiment_audit_final.json']:
        record = read(name)
        checks[name + ':status'] = record['status'].startswith('PASS:')
        checks[name + ':source_closure'] = (record['source_sha256_before'] == record['source_sha256_after']
            and matches(record['source_sha256_after']))
    v2 = read('audit/replay_v2.json')
    checks['prior_review_sources_unchanged'] = matches(v2['prior_checkpoint_sources_unchanged'])
    checks['full_class_exact_scope'] = (v2['direct_latent_triangular_grid_points'] == 153
        and len(v2['exact_interpolated_edges']) == 3)
    experiment_audit = read('audit/experiment_audit_final.json')
    checks['independent_experiment_checker_unchanged'] = sha(HERE / 'audit/check_experiment.py') == experiment_audit['audit_checker_sha256']
    checks['experiment_audit_scope'] = (experiment_audit['rows'] == 7680 and experiment_audit['cells'] == 240
        and experiment_audit['charged_flips'] == 3440640
        and all(experiment_audit['unseen_profiles_outside_prior'].values()))
    checks['polynomial_checks_status'] = read('upper/exact_checks.json')['status'] == 'EXACT_RATIONAL_CHECKS_PASSED'
    checks['general_proof_diagnostic_scope'] = len(read('audit/replay_final.json')['upper_polynomial_checks']) == 16

    lock_counts, lock_hashes = {}, {}
    for name in ['FROZEN.sha256', 'TIER3_FROZEN.sha256', 'TIER4_FROZEN.sha256', 'TIER5_FROZEN.sha256']:
        count = 0
        for line in (ROOT / name).read_text().splitlines():
            if not line.strip() or line.startswith('#'): continue
            expected, relative = line.split(maxsplit=1)
            path = (ROOT / relative).resolve()
            assert path.is_relative_to(ROOT.resolve())
            assert sha(path) == expected, (name, relative)
            count += 1
        lock_counts[name], lock_hashes[name] = count, sha(ROOT / name)
    checks['all_four_original_locks'] = all(count > 0 for count in lock_counts.values())
    inputs = subprocess.run([sys.executable, 'tools/verify_inputs.py'], cwd=ROOT, capture_output=True, text=True)
    checks['original_input_manifest'] = inputs.returncode == 0
    regression = read('regressions/RESULT.json')
    checks['regressions_passed'] = (regression['valid'] and len(regression['commands']) == 5
        and all(row['exit_code'] == 0 for row in regression['commands']))

    lock, complete, replay = read('EXPERIMENT_LOCK.json'), read('EXPERIMENT_COMPLETE.json'), read('REPLAY.json')
    checks['frozen_experiment_implementation'] = (sha(HERE / 'feedback_experiment.py') == lock['source_sha256']
        and sha(HERE / 'CONTRACT.md') == lock['contract_sha256'])
    checks['frozen_experiment_completed'] = (complete['complete'] and complete['rows'] == 7680
        and sha(HERE / 'EXPERIMENT_LOCK.json') == complete['lock_sha256']
        and sha(HERE / 'RAW.csv') == complete['raw_sha256'])
    checks['replay_matches_locked_data'] = (replay['valid'] and replay['cells'] == 240
        and replay['charged_replay_flips'] == 107520
        and replay['source_sha256'] == lock['source_sha256'] and replay['raw_sha256'] == complete['raw_sha256']
        and all(row['absolute_replay_difference'] < 1e-14 for row in replay['checks']))
    with (HERE / 'RAW.csv').open(newline='') as file:
        rows = list(csv.DictReader(file))
    checks['charged_work_and_ranges'] = (len(rows) == 7680 and sum(int(row['work']) for row in rows) == 3440640
        and all(int(row['work']) == int(row['budget']) and 0 <= float(row['estimate']) <= float(row['rho']) + 1e-15
            and float(row['clipped']) == min(1, max(0, float(row['estimate']))) for row in rows))
    assembly = read('NOTE_ASSEMBLY.json')
    checks['paper_packaging_matches'] = all(sha(HERE / row['source']) == row['source_sha256']
        and sha(HERE / row['target']) == row['target_sha256'] for row in assembly['files'])
    log = (HERE / 'RESEARCH_NOTE.log').read_text(encoding='utf-8')
    checks['pdf_compiled'] = (HERE / 'RESEARCH_NOTE.pdf').read_bytes().startswith(b'%PDF-')
    checks['pdf_no_overflow_or_unresolved_refs'] = 'Overfull' not in log and 'undefined' not in log.lower()
    required = ['STATE.md', 'CLAIMS.tsv', 'RESEARCH_NOTE.tex', 'RESEARCH_NOTE.pdf', 'LITERATURE_AUDIT.md',
        'ALGORITHMS.md', 'FORMAL_COVERAGE.md', 'FAILED_APPROACHES.md', 'REVIEW_PACKET.md', 'FINAL_REPORT.md',
        'RUN_LOG.md', 'DEPENDENCIES.md', 'prepare_commit.py', 'audit/REVIEW_V2.md']
    checks['required_deliverables'] = all((HERE / name).is_file() for name in required)
    with (HERE / 'CLAIMS.tsv').open(encoding='utf-8', newline='') as file:
        claims = list(csv.DictReader(file, delimiter='\t'))
    checks['claim_ledger_shape'] = len(claims) == 14 and all(None not in row and all(row.values()) for row in claims)
    excluded = {'ACCEPTANCE.json', 'CHECKPOINT_SHA256.json', 'PUBLICATION_RECEIPT.json'}
    files = {path.relative_to(HERE).as_posix(): sha(path) for path in sorted(HERE.rglob('*'))
        if path.is_file() and path.name not in excluded
        and not any(part in {'rendered', 'scratch', '__pycache__'} for part in path.relative_to(HERE).parts)
        and path.suffix not in {'.aux', '.out', '.toc'}}
    if not all(checks.values()):
        failure = HERE / ('FAILED_ACCEPTANCE_' + datetime.now(timezone.utc).strftime('%H%M%S') + '.json')
        failure.write_text(json.dumps(dict(checks=checks), indent=2) + '\n')
        raise AssertionError({key: value for key, value in checks.items() if not value})
    seal.write_text(json.dumps(dict(kind='POST-PROOF source and evidence checkpoint; not preregistration', files=files), indent=2) + '\n')
    result = dict(valid=True, scope='New paper proofs and diagnostics; no new Lean theorem or unrestricted minimax rate',
        utc=datetime.now(timezone.utc).isoformat(), python=platform.python_version(), git_version=git('--version'),
        lean_toolchain=(ROOT / 'lean/lean-toolchain').read_text().strip(),
        starting_shared_head=START, publication_parent=BASE, publish_branch=BRANCH,
        shared_head=git('rev-parse', 'HEAD'), shared_branch=git('branch', '--show-current'), shared_status=git('status', '--short'),
        checks=checks, lock_counts=lock_counts, original_lock_sha256=lock_hashes,
        inputs_output=inputs.stdout + inputs.stderr, checkpoint_sha256=sha(seal), new_package_file_count=len(files),
        pdf_visual_review='All 14 pages rendered and contact sheet inspected; no clipping or overlap seen. Underfull spacing warnings remain.')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(valid=True, checks=len(checks), files=len(files), lock_counts=lock_counts,
        shared_head=result['shared_head'])))

if __name__ == '__main__': main()
