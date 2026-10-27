"""Commit only this sealed directory on a new ref, preserving the shared checkout.

Uses a private index and verifies every committed blob against the working
bytes. Does not push, replace an existing ref, or include concurrent changes.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess, uuid

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '3897d390d2fdd66d6f3f4b84fabfe523b0e031ba'
BRANCH = 'research/nonlinear-feedback-20261027'
PREFIX = HERE.relative_to(ROOT).as_posix() + '/'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def run(args, env=None, input=None):
    process = subprocess.run(['git', '-c', 'core.autocrlf=false', *args], cwd=ROOT, env=env,
        input=input, text=True, capture_output=True, encoding='utf-8')
    if process.returncode: raise RuntimeError(process.stderr + process.stdout)
    return process.stdout.strip()

def main():
    receipt_path = HERE / 'PUBLICATION_RECEIPT.json'
    if receipt_path.exists(): raise RuntimeError('Refuse to overwrite publication receipt')
    acceptance = json.loads((HERE / 'ACCEPTANCE.json').read_text())
    assert acceptance['valid'] and acceptance['publication_parent'] == BASE and acceptance['publish_branch'] == BRANCH
    checkpoint = HERE / 'CHECKPOINT_SHA256.json'
    assert sha(checkpoint) == acceptance['checkpoint_sha256']
    sealed = json.loads(checkpoint.read_text())['files']
    assert all(sha(HERE / path) == digest for path, digest in sealed.items())
    assert subprocess.run(['git', 'show-ref', '--verify', '--quiet', 'refs/heads/' + BRANCH], cwd=ROOT).returncode == 1
    shared_head = run(['rev-parse', 'HEAD'])
    index = Path(run(['rev-parse', '--git-path', 'index']))
    if not index.is_absolute(): index = ROOT / index
    index_digest = sha(index)
    private = HERE / 'scratch' / ('publish-' + uuid.uuid4().hex + '.index')
    private.parent.mkdir(exist_ok=True)
    environment = dict(os.environ, GIT_INDEX_FILE=str(private))
    run(['read-tree', BASE], environment)
    paths = sorted(set(sealed) | {'CHECKPOINT_SHA256.json', 'ACCEPTANCE.json'})
    for offset in range(0, len(paths), 40):
        run(['add', '-f', '--', *[PREFIX + path for path in paths[offset:offset + 40]]], environment)
    changed = run(['diff', '--cached', '--name-only', BASE], environment).splitlines()
    assert set(changed) == {PREFIX + path for path in paths}
    tree = run(['write-tree'], environment)
    message = ('research: verify nonlinear feedback advantage and finite population approximation\n\n'
        'Prove an exact full-class feedback separation at a two-flip cap, arbitrary-feedback local-depth necessities, '
        'and a controlled finite approximation of the unrestricted expected-budget value. Preserve independent rational audits '
        'and a locked nonlinear posterior experiment. The arbitrary-law minimax rate remains open.\n')
    commit = run(['commit-tree', tree, '-p', BASE], environment, input=message)
    for path in paths:
        blob = subprocess.check_output(['git', 'show', commit + ':' + PREFIX + path], cwd=ROOT)
        assert hashlib.sha256(blob).hexdigest() == sha(HERE / path), path
    assert sha(index) == index_digest, 'Shared index changed concurrently; do not publish automatically'
    assert run(['rev-parse', 'HEAD']) == shared_head, 'Shared HEAD changed concurrently; inspect before publication'
    run(['update-ref', 'refs/heads/' + BRANCH, commit, '0' * 40])
    receipt = dict(commit=commit, branch=BRANCH, parent=BASE, shared_head_before=shared_head,
        shared_head_after=run(['rev-parse', 'HEAD']), shared_index_unchanged=sha(index) == index_digest,
        all_committed_file_bytes_verified=True, files_added=len(changed), scope=PREFIX,
        utc=datetime.now(timezone.utc).isoformat(), pushed=False)
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt))

if __name__ == '__main__': main()
