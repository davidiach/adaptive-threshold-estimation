"""Verify the v2 rare-event package and replay its finite checks without mutation.

This checks artifact identity, exact finite certificates, and falsification
computations. It also binds every stored genie-bracket row to one verified
lower/upper pair for that row's instance. It is not a formal proof of the
manuscript's general theorems.
"""
from __future__ import annotations

import ast
import copy
import hashlib
import importlib
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / 'paper/rare-event'

# Fields of an optimized_genie/genie_bracket_results.json row and of the two
# files it names, exactly as checks/solve_genie_bracket.py writes them. The
# payload verifiers ignore unknown fields, so a file declaring anything else
# (another observation model or program, say) must not pass unnoticed.
BRACKET_ROW_FIELDS = frozenset({
    'case', 'cap', 'budget', 'dual_status', 'raw_genie_dual_rms',
    'certified_unrestricted_program_lower_decimal', 'certified_adaptive_rms_lower_decimal',
    'certified_rms_upper_decimal', 'program_bracket_ratio', 'adaptive_risk_bracket_ratio',
    'exact_factor_two_stopping_test', 'lower_certificate', 'upper_policy', 'elapsed_seconds'})
# Row fields recomputed from the verified bounds. The rest are solver
# diagnostics (status, raw float objective, timing) that certify nothing.
DERIVED_ROW_FIELDS = (
    'exact_factor_two_stopping_test', 'certified_unrestricted_program_lower_decimal',
    'certified_adaptive_rms_lower_decimal', 'certified_rms_upper_decimal',
    'program_bracket_ratio', 'adaptive_risk_bracket_ratio')
GENIE_LOWER_FIELDS = frozenset({
    'description', 'certificate_kind', 'gaps', 'weights', 'rho', 'budget', 'cap', 'priors',
    'information_work_price', 'information_potentials', 'certified_squared_lower_bound',
    'certified_rms_lower_bound_decimal', 'certified_adaptive_squared_lower_bound',
    'certified_adaptive_rms_lower_bound_decimal', 'repair'})
GENIE_NESTED_FIELDS = {
    'priors': frozenset({'low', 'high', 'variance', 'work'}),
    'repair': frozenset({'dyadic_precision_bits', 'backward_passes', 'reference_regularization',
                         'float_bisection_price'})}
POLICY_UPPER_FIELDS = frozenset({
    'description', 'gaps', 'weights', 'rho', 'budget', 'cap', 'poisson_intensity', 'offset',
    'stop_probability', 'terminal_output', 'certified_squared_upper_bound',
    'certified_rms_upper_bound_decimal'})
# The bracket L_N <= G_N <= P_inf <= P_N <= U_N of sections/computation.tex
# needs L_N from a verified four-prior genie dual. verify_finite_dual.py imposes
# the latent-genie terminal inequality on both genie kinds, which makes them
# uncapped, but only the four-prior kind's bound_scope is the program value. A
# midpoint-genie certificate bounds adaptive minimax risk, a different
# quantity, and a finite_cap certificate bounds the cap-N program alone.
GENIE_LOWER_KIND = 'uncapped_four_prior_genie'
GENIE_LOWER_SCOPE = 'unrestricted flow-program RMS value'
# solve_genie_bracket.py searches every case at both budgets, raising the cap
# along its ladder until the factor-two test passes (sections/computation.tex).
# The payload manifest pins the generator's bytes; BRACKET_PLAN_SOURCE only
# cross-references that pinned source with the ladder and budgets enforced here.
BRACKET_BUDGETS = (100.0, 1000.0)
BRACKET_PLAN_SOURCE = ('def run(output_dir, caps=(4, 8, 16, 32)):',
                       'for budget in (100.0, 1000.0):',
                       'for cap in ((1,) if name == "perfect_labels" else caps):')


def cap_ladder(case):
    return (1,) if case == 'perfect_labels' else (4, 8, 16, 32)
# Substitutions in genie_bracket_results.json that must be rejected, each with
# the rule that must reject it: (row, field, replacement, rule).
BRACKET_BINDING_CONTROLS = (
    (0, 'upper_policy', 'perfect_labels_N1_B1000_upper.json', 'identity'),
    (4, 'lower_certificate', '../certificates/three_scales_N8_B1000.json', 'scope'),
    (4, 'lower_certificate', '../genie_certificates/three_scales_N8_B1000_genieN8.json', 'scope'),
    (4, 'lower_certificate', '../binding_controls/relabelled_three_scales_N8_B1000.json',
     'verification'),
    (4, 'upper_policy', 'three_scales_N4_B1000_upper.json', 'identity'),
    (0, 'lower_certificate', 'one_gap_N4_B1000_lower.json', 'identity'),
    (3, 'exact_factor_two_stopping_test', True, 'stale'),
    (0, 'upper_policy', '../../MANIFEST.sha256', 'location'),
)


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


def load_payload_verifiers(checks):
    """Import the payload's own exact lower and upper verifiers from `checks`."""
    names = ('verify_finite_dual', 'verify_policy_upper')
    saved_path, saved_flag = list(sys.path), sys.dont_write_bytecode
    saved = {name: sys.modules.pop(name) for name in names if name in sys.modules}
    sys.path.insert(0, str(checks))
    sys.dont_write_bytecode = True
    importlib.invalidate_caches()
    try:
        lower, upper = (importlib.import_module(name) for name in names)
    finally:
        sys.path[:] = saved_path
        sys.dont_write_bytecode = saved_flag
        for name in names:
            sys.modules.pop(name, None)
        sys.modules.update(saved)
    for module in (lower, upper):
        require(Path(module.__file__).resolve().parent == checks.resolve(),
                f'{module.__name__} was not loaded from the checked copy')
    return lower, upper


def canonical_law(gaps, weights):
    """The magnitude law as sorted (gap, total mass) atoms, free of atom order."""
    masses = {}
    for gap, weight in zip(gaps, weights, strict=True):
        masses[gap] = masses.get(gap, 0) + weight
    return tuple(sorted(masses.items()))


def bracket_case_laws(checks, rational):
    """Read each bracket case's exact law and rarity from the payload's generator."""
    tree = ast.parse((checks / 'solve_genie_bracket.py').read_text(encoding='utf-8'))
    tables = [node.value for node in ast.walk(tree) if isinstance(node, ast.Assign)
              and [getattr(target, 'id', None) for target in node.targets] == ['cases']]
    require(len(tables) == 1, 'Expected one case table in solve_genie_bracket.py')
    source = (checks / 'solve_genie_bracket.py').read_text(encoding='utf-8')
    require(all(line in source for line in BRACKET_PLAN_SOURCE),
            'solve_genie_bracket.py does not contain the recorded cap ladder and budgets')
    laws = {}
    for name, gaps, weights, rho in ast.literal_eval(tables[0]):
        require(name not in laws, f'Duplicate bracket case: {name}')
        laws[name] = {'law': canonical_law(map(rational, gaps), map(rational, weights)),
                      'rho': rational(rho)}
    return laws


def instance_identity(record, rational):
    return {'law': canonical_law(map(rational, record['gaps']), map(rational, record['weights'])),
            'rho': rational(record['rho']), 'budget': rational(record['budget']),
            'cap': record['cap']}


def genie_terminal_dominates(certificate, module):
    """Recheck the latent-genie terminal inequality that makes a lower uncapped."""
    rational, cap = module.rational, certificate['cap']
    gaps, weights = (list(map(rational, certificate[key])) for key in ('gaps', 'weights'))
    low, high, reference = (list(map(rational, certificate['priors'][key]))
                            for key in ('low', 'high', 'variance'))
    rewards = module.exact_latent_rewards(gaps, weights, low, high, reference, cap)
    potentials = list(map(rational, certificate['information_potentials']))
    terminal = [i for i, (n, _) in enumerate(module.states_for(cap)) if n == cap]
    return bool(terminal) and all(potentials[i] >= rewards[i] for i in terminal)


def sqrt_ratio(upper, lower):
    try:
        return math.sqrt(float(upper / lower))
    except (OverflowError, ZeroDivisionError):
        return None


def bracket_pair_violations(checks, row, laws, verifiers):
    """Return every reason `row` fails to bind one verified genie lower and policy upper."""
    lower_module, upper_module = verifiers
    if set(row) != BRACKET_ROW_FIELDS:
        return [f'schema: row fields differ by {sorted(set(row) ^ BRACKET_ROW_FIELDS)}']
    reasons, records, checked = [], {}, {}
    for role, field, verify in (('lower', 'lower_certificate', lower_module.verify),
                                ('upper', 'upper_policy', upper_module.verify)):
        path = (checks / 'optimized_genie' / str(row[field])).resolve()
        if not (path.is_relative_to(checks.resolve()) and path.is_file()):
            reasons.append(f'location: {role} file {row[field]!r} is not a payload check file')
            continue
        try:
            records[role] = read_json(path)
            checked[role] = verify(records[role])
        except Exception as error:  # Any failure of a payload verifier rejects the file.
            reasons.append(f'verification: {role} file {row[field]!r} rejected: {error!r}')
    if len(checked) < 2:
        return reasons
    try:
        return reasons + verified_pair_violations(row, records, checked, laws, lower_module)
    except (KeyError, TypeError, ValueError, AttributeError) as error:
        # Verified files can still lack a field this binding reads.
        return reasons + [f'schema: verified files lack a field the binding needs: {error!r}']


def verified_pair_violations(row, records, checked, laws, lower_module):
    """Scope, schema, identity and derived-field reasons for a verified pair."""
    rational, reasons = lower_module.rational, []
    lower, upper = records['lower'], records['upper']
    lower_check, upper_check = checked['lower'], checked['upper']
    if (lower_check['certificate_kind'], lower_check['bound_scope']) != (
            GENIE_LOWER_KIND, GENIE_LOWER_SCOPE):
        reasons.append(f"scope: lower bounds the {lower_check['bound_scope']} "
                       f"({lower_check['certificate_kind']}), not the {GENIE_LOWER_SCOPE} "
                       'of a four-prior genie dual')
    elif not genie_terminal_dominates(lower, lower_module):
        reasons.append('scope: depth-cap potentials do not dominate the exact latent-genie rewards')
    for role, record, fields in (('lower', lower, GENIE_LOWER_FIELDS),
                                 ('upper', upper, POLICY_UPPER_FIELDS)):
        if set(record) != fields:
            reasons.append(f'schema: {role} fields differ by {sorted(set(record) ^ fields)}')
    for key, fields in GENIE_NESTED_FIELDS.items():
        value = lower.get(key)
        if not isinstance(value, dict) or set(value) != fields:
            reasons.append(f'schema: lower {key} fields are not {sorted(fields)}')
    budget = row['budget']
    if not isinstance(row['case'], str) or row['case'] not in laws:
        reasons.append(f"identity: unknown bracket case {row['case']!r}")
    elif not (all(type(record['cap']) is int for record in (row, lower, upper))
              and type(budget) in (int, float) and math.isfinite(budget)):
        reasons.append('identity: cap or budget is not an exact number')
    else:
        stated = {**laws[row['case']], 'budget': rational(budget), 'cap': row['cap']}
        identities = (stated, instance_identity(lower, rational), instance_identity(upper, rational))
        differing = [key for key in stated
                     if not identities[0][key] == identities[1][key] == identities[2][key]]
        if differing:
            reasons.append(f"identity: row, lower and upper differ in {', '.join(differing)}")
    lower_sq = rational(lower_check['certified_squared_lower_bound'])
    upper_sq = rational(upper_check['certified_squared_upper_bound'])
    expected = {
        'exact_factor_two_stopping_test': upper_sq <= 4 * lower_sq,
        'certified_unrestricted_program_lower_decimal': lower_check['certified_rms_lower_bound_decimal'],
        'certified_rms_upper_decimal': upper_check['certified_rms_upper_bound_decimal'],
        'program_bracket_ratio': sqrt_ratio(upper_sq, lower_sq),
    }
    if ('certified_adaptive_squared_lower_bound' in lower_check
            and 'certified_adaptive_squared_lower_bound' in lower):
        # Present only for a verified four-prior genie lower; the stored value
        # was checked against the verifier's recomputed adaptive bound. If the
        # file omits it, both adaptive row fields count as stale.
        adaptive_sq = rational(lower['certified_adaptive_squared_lower_bound'])
        expected['certified_adaptive_rms_lower_decimal'] = lower_module.sqrt_lower_decimal(adaptive_sq)
        expected['adaptive_risk_bracket_ratio'] = sqrt_ratio(upper_sq, adaptive_sq)
    stale = [field for field in DERIVED_ROW_FIELDS
             if expected.get(field) is None or type(row[field]) is not type(expected[field])
             or row[field] != expected[field]]
    if stale:
        reasons.append(f"stale: not reproduced from the verified bounds: {', '.join(stale)}")
    return reasons


def check_bracket_table(checks, table, laws, verifiers):
    """Bind every bracket row to a verified pair and recheck each cap search."""
    rows = table.get('results') if isinstance(table, dict) else None
    require(isinstance(rows, list) and rows and set(table) == {'scope', 'results'},
            'Malformed genie bracket results')
    failures = [f'row {index}: {reason}' for index, row in enumerate(rows)
                for reason in (bracket_pair_violations(checks, row, laws, verifiers)
                               if isinstance(row, dict) else ['schema: row is not an object'])]
    require(not failures, 'Bracket rows do not bind verified certificate pairs:\n'
            + '\n'.join(failures))
    rational = verifiers[0].rational
    searches = {}
    for row in rows:
        key = (row['case'], rational(row['budget']))
        require(key not in searches or key == list(searches)[-1], f'Interleaved cap search: {key}')
        searches.setdefault(key, []).append(row)
    require(set(searches) == {(case, rational(budget)) for case in laws for budget in BRACKET_BUDGETS},
            'Cap searches are not every bracket case at every budget')
    for key, search in searches.items():
        caps, ladder = tuple(row['cap'] for row in search), cap_ladder(key[0])
        require(caps == ladder[:len(caps)], f'Cap search {key} does not follow its cap ladder {ladder}')
        require([row['exact_factor_two_stopping_test'] for row in search]
                == [False] * (len(search) - 1) + [True],
                f'Cap search {key} does not stop at its first passing cap')
    return {'pairs': len(rows), 'cap_searches': len(searches)}


def reject_binding_controls(checks, table, laws, verifiers):
    """Require every registered bracket substitution to fail for its stated rule."""
    relabelled = read_json(checks / 'certificates/three_scales_N8_B1000.json')
    relabelled['certificate_kind'] = GENIE_LOWER_KIND
    folder = checks / 'binding_controls'
    folder.mkdir(exist_ok=True)
    (folder / 'relabelled_three_scales_N8_B1000.json').write_text(
        json.dumps(relabelled, indent=2) + '\n', encoding='utf-8')
    rejected = 0
    for index, field, replacement, rule in BRACKET_BINDING_CONTROLS:
        changed = copy.deepcopy(table)
        changed['results'][index][field] = replacement
        try:
            check_bracket_table(checks, changed, laws, verifiers)
        except RuntimeError as error:
            require(f'row {index}: {rule}:' in str(error),
                    f'Substitution {index}/{field} -> {replacement!r} was not rejected '
                    f'by the {rule} rule:\n{error}')
            rejected += 1
            continue
        raise RuntimeError(f'Accepted bracket substitution {index}/{field} -> {replacement!r}')
    return rejected


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
        copy_root = Path(tmp) / 'v2'
        shutil.copytree(payload, copy_root)
        checks = copy_root / 'checks'
        run(checks / 'self_check_certificates.py', copy_root)
        run(checks / 'verify_revisions.py', copy_root)
        certificate = read_json(checks / 'certificate_self_check.json')
        require(certificate == read_json(payload / 'checks/certificate_self_check.json'),
                'Certificate replay disagrees with published result')
        revisions = read_json(checks / 'revision_checks.json')
        require(revisions == read_json(payload / 'checks/revision_checks.json'),
                'Revision checker disagrees with published result')
        # The payload self-check compares each row's bounds without asking whether
        # the two files concern the row's instance or the needed lower scope.
        verifiers = load_payload_verifiers(checks)
        laws = bracket_case_laws(checks, verifiers[0].rational)
        brackets = read_json(checks / 'optimized_genie/genie_bracket_results.json')
        bound = check_bracket_table(checks, brackets, laws, verifiers)
        require(bound['pairs'] == certificate['exact_stopping_decisions_rechecked'],
                'Bracket binding and certificate self-check disagree on the row count')
        substitutions_rejected = reject_binding_controls(checks, brackets, laws, verifiers)
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
        'bracket_pairs_bound': bound['pairs'],
        'bracket_cap_searches': bound['cap_searches'],
        'bracket_substitutions_rejected': substitutions_rejected,
        'revision_checks': revisions['status'],
        'selection_laws': replay['selection_and_variational_optimizer']['laws'],
        'hard_assignments': replay['selection_and_variational_optimizer']['enumerated_hard_assignments'],
        'genie_comparisons': replay['finite_divergence_genie']['cap_comparisons'],
        'published_records_unchanged': True,
        'scope': 'Artifact identity and finite checks, not formal verification of general theorems.',
    }, indent=2))


if __name__ == '__main__':
    main()
