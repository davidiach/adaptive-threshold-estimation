"""Durable stage publication around unchanged benchmark sources, for fresh runs.

No command adopts or resumes a legacy results directory. In particular, a held-out
attempt is never retried, even if the launcher died before starting its child.
Storage validation here is not the scientific verification of the experiment.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import uuid
import zipfile

ROOT = Path(__file__).resolve().parents[1]
STAGES = ("train", "tune", "lock", "test")
INPUTS = (
    "benchmark/run_real.py", "benchmark/real_threshold.py",
    "benchmark/reference.py", "benchmark/verify_real.py",
    "benchmark/data/training.json", "benchmark/data/tuning.json",
    "results/real_verification.json",
)
OUTPUTS = {
    "train": ("real_training.json",),
    "tune": ("real_tuning.json",),
    "lock": ("real_selection.json",),
    "test": ("real_test_started.json", "real_test.json", "real_test_raw.npz"),
}
LOCK_INPUTS = set(INPUTS) | {"results/real_training.json", "results/real_tuning.json"}


class ExperimentError(RuntimeError):
    pass


class Busy(ExperimentError):
    pass


def require(condition, message):
    if not condition:
        raise ExperimentError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def sync_directory(path):
    # Windows has no portable directory-fsync equivalent in Python. File flushes
    # and replace still protect against process interruption; see the audit doc.
    if os.name != "nt":
        fd = os.open(path, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)


def atomic_json(path, value):
    payload = (json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n").encode()
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".state-", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        sync_directory(path.parent)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def durable_copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as incoming, target.open("xb") as outgoing:
        shutil.copyfileobj(incoming, outgoing)
        outgoing.flush()
        os.fsync(outgoing.fileno())


@contextmanager
def writer_lock(run):
    # Never unlink this file: replacing a lock inode would admit a second writer.
    with (run / "writer.lock").open("r+b") as stream:
        try:
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise Busy("Another wrapper owns this run; no work was started.") from exc
        try:
            yield
        finally:
            if os.name == "nt":
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def initialize(run, source=ROOT):
    """Create a distinct experiment identity; never copy selection or test data."""
    run, source = Path(run).resolve(), Path(source).resolve()
    require(not run.exists(), "Run directory already exists; it cannot be adopted or reset.")
    # Read all fixed inputs before creating anything. The archived selection and
    # held-out records are deliberately not inputs to a new experiment.
    hashes = {name: digest(source / name) for name in INPUTS}
    run.mkdir(parents=True)  # exclusive creation also arbitrates concurrent init
    with (run / "writer.lock").open("xb") as stream:
        stream.write(b"0")
        stream.flush()
        os.fsync(stream.fileno())
    with writer_lock(run):
        for name in INPUTS:
            durable_copy(source / name, run / "inputs" / name)
            require(digest(run / "inputs" / name) == hashes[name], "Input changed during initialization: " + name)
        (run / "attempts").mkdir()
        (run / "snapshots").mkdir()
        state = dict(schema=1, inputs=hashes, stages={}, snapshot=None)
        atomic_json(run / "state.json", state)
    return state


def check_files(root, hashes):
    for name, expected in hashes.items():
        require(digest(root / name) == expected, "Stored file changed: " + name)


def load_state(run):
    state = read_json(run / "state.json")
    require(state.get("schema") == 1 and set(state.get("inputs", {})) == set(INPUTS), "Invalid run identity.")
    stages = state.get("stages", {})
    require(isinstance(stages, dict) and set(stages) <= set(STAGES), "Invalid stage ledger.")
    for index, stage in enumerate(STAGES):
        if stage not in stages:
            continue
        entry = stages[stage]
        require(entry.get("status") in ("running", "interrupted", "completed"), "Invalid stage status.")
        require(all(stages.get(prior, {}).get("status") == "completed" for prior in STAGES[:index]), "Invalid stage order.")
    check_files(run / "inputs", state["inputs"])
    snapshot = state.get("snapshot")
    completed = [stage for stage in STAGES if stages.get(stage, {}).get("status") == "completed"]
    require(bool(snapshot) == bool(completed), "Snapshot does not match completed stages.")
    if snapshot:
        token = snapshot.get("id", "")
        require(len(token) == 32 and all(c in "0123456789abcdef" for c in token), "Invalid snapshot identity.")
        expected = {name for stage in completed for name in OUTPUTS[stage]}
        require(set(snapshot.get("files", {})) == expected, "Incomplete snapshot file set.")
        check_files(run / "snapshots" / token, snapshot["files"])
    return state


def status(run):
    """Report liveness using the OS lock, never a stale PID or timestamp."""
    run = Path(run).resolve()
    try:
        with writer_lock(run):
            state = load_state(run)
        busy = False
    except Busy:
        state, busy = load_state(run), True
    report = deepcopy(state)
    report["writer_active"] = busy
    for stage in STAGES:
        entry = report["stages"].setdefault(stage, {"status": "not_started"})
        if entry["status"] == "running" and not busy:
            entry["status"] = "interrupted"
    report["heldout_closed"] = "test" in state["stages"]
    return report


def validate_output(stage, work):
    """Check storage completeness; numeric correctness remains a separate audit."""
    results = work / "results"
    if stage in ("train", "tune"):
        value = read_json(results / OUTPUTS[stage][0])
        require(isinstance(value.get("rows"), list) and bool(value["rows"]), "Missing stage rows.")
        if stage == "tune":
            require(value.get("complete") is True, "Tuning did not complete.")
    else:
        selection = read_json(results / "real_selection.json")
        require(set(selection.get("hashes", {})) == LOCK_INPUTS, "Incomplete selection input lock.")
        check_files(work, selection["hashes"])
        require(isinstance(selection.get("rows"), list) and bool(selection["rows"]), "Missing selection rows.")
        if stage == "test":
            started = read_json(results / "real_test_started.json")
            require(started.get("selection_sha256") == digest(results / "real_selection.json"), "Test start does not bind the selection.")
            value = read_json(results / "real_test.json")
            require(value.get("complete") is True, "Held-out output did not complete.")
            cells = [(row["budget"], method) for row in selection["rows"] for method in ("gha_tuned", "real_tuned")]
            require([(row["budget"], row["method"]) for row in value["rows"]] == cells, "Incomplete held-out cells.")
            require(value.get("replications") == selection.get("heldout_replications"), "Held-out replication mismatch.")
            names = {f"{method}_{budget}_{kind}.npy" for budget, method in cells for kind in ("value", "work")}
            with zipfile.ZipFile(results / "real_test_raw.npz") as raw:
                require(set(raw.namelist()) == names and len(raw.namelist()) == len(names), "Raw arrays do not match held-out cells.")
                require(raw.testzip() is None, "Damaged raw-array archive.")


def run_child(work, stage, n):
    command = [sys.executable, "-B", str(work / "benchmark/run_real.py"), stage]
    if n is not None:
        command += ["--n", str(n)]
    with (work / "runner.log").open("xb") as log:
        child = subprocess.Popen(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
        try:
            code = child.wait()
        except BaseException:
            child.terminate()
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
            raise
        finally:
            log.flush()
            os.fsync(log.fileno())
    require(code == 0, f"Runner exited with status {code}; see {work / 'runner.log'}")


def advance(run, stage, *, n=None):
    run = Path(run).resolve()
    require(stage in STAGES, "Unknown stage.")
    if stage in ("train", "tune"):
        n = n if n is not None else (2000 if stage == "train" else 100)
        require(type(n) is int and n > 0, "Replications must be a positive integer.")
    else:
        require(n is None, "Only train/tune accept a replication count.")
    with writer_lock(run):
        state = load_state(run)
        stages = state["stages"]
        require("test" not in stages, "Held-out attempt already started; rerun and retuning are forbidden.")
        require(all(stages.get(prior, {}).get("status") == "completed" for prior in STAGES[:STAGES.index(stage)]), "Previous stage has not completed.")
        previous = stages.get(stage)
        if previous:
            require(previous["status"] != "completed", "Stage already completed; overwrite is forbidden.")
            require(previous["n"] == n, "Interrupted stage must retain its replication count.")
        token = uuid.uuid4().hex
        work = run / "attempts" / token
        work.mkdir()
        for name in INPUTS:
            durable_copy(run / "inputs" / name, work / name)
        snapshot = state["snapshot"]
        if snapshot:
            for name in snapshot["files"]:
                durable_copy(run / "snapshots" / snapshot["id"] / name, work / "results" / name)
        stages[stage] = dict(status="running", attempt=token, n=n)
        # This durable intent precedes the child launch, including the held-out
        # attempt. Any uncertainty consumes that once-only attempt.
        atomic_json(run / "state.json", state)
        try:
            run_child(work, stage, n)
            check_files(work, state["inputs"])
            if snapshot:
                check_files(work / "results", snapshot["files"])
            validate_output(stage, work)
            destination = run / "snapshots" / token
            destination.mkdir()
            names = [name for prior in STAGES[:STAGES.index(stage) + 1] for name in OUTPUTS[prior]]
            for name in names:
                durable_copy(work / "results" / name, destination / name)
            sync_directory(destination)
            sync_directory(destination.parent)
            updated = deepcopy(state)
            updated["snapshot"] = dict(id=token, files={name: digest(destination / name) for name in names})
            updated["stages"][stage]["status"] = "completed"
            atomic_json(run / "state.json", updated)
            return updated
        except BaseException:
            # If even recording the failure fails, the durable running intent
            # still blocks held-out retries. Never replace a committed snapshot
            # after a post-replace directory-fsync error.
            try:
                current = read_json(run / "state.json")
                if current["stages"][stage]["status"] == "running":
                    current["stages"][stage]["status"] = "interrupted"
                    atomic_json(run / "state.json", current)
            except (OSError, ValueError, KeyError):
                pass
            raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("init", "status", *STAGES))
    parser.add_argument("--run-dir", type=Path, required=True, help="A distinct fresh experiment directory; prefer .runtime/experiments/NAME")
    parser.add_argument("--n", type=int)
    args = parser.parse_args(argv)
    try:
        if args.stage in ("init", "status"):
            require(args.n is None, "Only train/tune accept --n.")
            value = initialize(args.run_dir) if args.stage == "init" else status(args.run_dir)
        else:
            value = advance(args.run_dir, args.stage, n=args.n)
        print(json.dumps(value, indent=2, sort_keys=True))
    except (ExperimentError, OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        parser.exit(1, f"Experiment state error: {exc}\n")


if __name__ == "__main__":
    main()
