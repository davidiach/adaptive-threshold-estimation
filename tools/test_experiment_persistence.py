"""Storage/transition tests with synthetic outputs; never sample held-out data."""
from concurrent.futures import ThreadPoolExecutor
import ast
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from threading import Barrier
import unittest
from unittest.mock import patch
import zipfile

import run_real_guarded as guarded

ROOT = Path(__file__).resolve().parents[1]


def write_json(path, value):
    path.write_text(json.dumps(value), encoding="utf-8")


def synthetic_child(work, stage, n):
    """Stand in for the expensive scientific computation, not for publication."""
    results = work / "results"
    if stage in ("train", "tune"):
        write_json(results / guarded.OUTPUTS[stage][0], dict(rows=[dict(n=n)], replications=n, complete=True))
    elif stage == "lock":
        write_json(results / "real_selection.json", dict(
            hashes={name: guarded.digest(work / name) for name in guarded.LOCK_INPUTS},
            rows=[dict(budget=16)], heldout_replications=3))
    else:
        write_json(results / "real_test_started.json", dict(selection_sha256=guarded.digest(results / "real_selection.json")))
        write_json(results / "real_test.json", dict(complete=True, replications=3,
            rows=[dict(budget=16, method=method) for method in ("gha_tuned", "real_tuned")]))
        with zipfile.ZipFile(results / "real_test_raw.npz", "w") as raw:
            for method in ("gha_tuned", "real_tuned"):
                for kind in ("value", "work"):
                    # The wrapper checks the storage envelope. It deliberately
                    # does not claim to parse or validate these numerical arrays.
                    raw.writestr(f"{method}_16_{kind}.npy", b"synthetic array")


class LegacyCharacterizationTests(unittest.TestCase):
    def legacy_function(self, name, namespace, prefix=None):
        tree = ast.parse((ROOT / "benchmark/run_real.py").read_text(encoding="utf-8"))
        function = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name)
        if prefix is not None:
            function.body = function.body[:prefix]
        exec(compile(ast.Module(body=[function], type_ignores=[]), "frozen-runner-excerpt", "exec"), namespace)
        return namespace[name]

    def test_legacy_direct_write_can_destroy_previous_checkpoint(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "checkpoint.json"
            write_json(target, {"complete": False, "rows": [1]})
            save = self.legacy_function("save", dict(RES=Path(directory), json=json))
            def interrupted_write(path, data, **kwargs):
                with path.open("w", encoding="utf-8") as stream:
                    stream.write(data[:4])
                raise OSError("simulated disk failure")
            with patch.object(Path, "write_text", interrupted_write), self.assertRaises(OSError):
                save(target.name, {"complete": True, "rows": [1, 2]})
            with self.assertRaises(json.JSONDecodeError):
                guarded.read_json(target)

    def test_legacy_start_check_admits_two_callers(self):
        with tempfile.TemporaryDirectory() as directory:
            result = Path(directory)
            write_json(result / "real_selection.json", {"hashes": {}})
            import hashlib
            import time
            # Only execute the marker preamble; the sampling body is excluded.
            start = self.legacy_function("test", dict(RES=result, ROOT=result, json=json, hashlib=hashlib, time=time), prefix=5)
            gate = Barrier(2)
            exists = Path.exists
            def simultaneous_check(path):
                found = exists(path)
                if path.name == "real_test_started.json":
                    gate.wait(timeout=5)
                return found
            with patch.object(Path, "exists", simultaneous_check), ThreadPoolExecutor(2) as pool:
                futures = [pool.submit(start) for _ in range(2)]
                self.assertEqual([future.result(timeout=10) for future in futures], [None, None])


class PersistenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.run = self.root / "run"
        guarded.initialize(self.run)
        worker = patch.object(guarded, "run_child", side_effect=synthetic_child)
        self.worker = worker.start()
        self.addCleanup(worker.stop)

    def complete_through(self, end):
        for stage in guarded.STAGES[:guarded.STAGES.index(end) + 1]:
            guarded.advance(self.run, stage)

    def test_stage_order_and_once_only_terminal_state(self):
        fresh = guarded.status(self.run)
        self.assertEqual([row["status"] for row in fresh["stages"].values()], ["not_started"] * 4)
        self.assertFalse(fresh["heldout_closed"])
        with self.assertRaisesRegex(guarded.ExperimentError, "Previous stage"):
            guarded.advance(self.run, "test")
        self.worker.assert_not_called()
        for stage in guarded.STAGES:
            guarded.advance(self.run, stage)
            state = guarded.status(self.run)
            self.assertEqual(state["stages"][stage]["status"], "completed")
            before = self.worker.call_count
            with self.assertRaises(guarded.ExperimentError):
                guarded.advance(self.run, stage)
            self.assertEqual(self.worker.call_count, before)
        self.assertTrue(guarded.status(self.run)["heldout_closed"])
        for stage in guarded.STAGES:
            with self.assertRaisesRegex(guarded.ExperimentError, "rerun and retuning"):
                guarded.advance(self.run, stage)

    def test_existing_or_incompletely_initialized_directory_is_never_adopted(self):
        for target in (self.run, self.root):
            with self.assertRaisesRegex(guarded.ExperimentError, "cannot be adopted"):
                guarded.initialize(target)
        incomplete = self.root / "incomplete"
        with patch.object(guarded, "durable_copy", side_effect=OSError("disk")), self.assertRaises(OSError):
            guarded.initialize(incomplete)
        with self.assertRaises(guarded.ExperimentError):
            guarded.initialize(incomplete)

    def test_invalid_replications_do_not_change_state(self):
        before = (self.run / "state.json").read_bytes()
        for stage, n in (("train", 0), ("tune", -1), ("train", True), ("train", 1.5), ("test", 5)):
            with self.subTest(stage=stage, n=n), self.assertRaises(guarded.ExperimentError):
                guarded.advance(self.run, stage, n=n)
        self.assertEqual((self.run / "state.json").read_bytes(), before)
        self.worker.assert_not_called()

    def test_interrupted_training_restarts_from_last_published_stage(self):
        def fail(work, stage, n):
            synthetic_child(work, stage, n)
            raise KeyboardInterrupt()
        self.worker.side_effect = fail
        with self.assertRaises(KeyboardInterrupt):
            guarded.advance(self.run, "train", n=7)
        failed = guarded.status(self.run)
        self.assertEqual(failed["stages"]["train"]["status"], "interrupted")
        self.assertIsNone(failed["snapshot"])
        with self.assertRaisesRegex(guarded.ExperimentError, "retain its replication"):
            guarded.advance(self.run, "train", n=8)
        self.worker.side_effect = synthetic_child
        retried = guarded.advance(self.run, "train", n=7)
        self.assertNotEqual(retried["stages"]["train"]["attempt"], failed["stages"]["train"]["attempt"])
        self.assertTrue((self.run / "attempts" / failed["stages"]["train"]["attempt"] / "results/real_training.json").is_file())

    def test_running_state_is_visible_and_overlapping_writer_never_launches(self):
        def inspect(work, stage, n):
            during = guarded.status(self.run)
            self.assertTrue(during["writer_active"])
            self.assertEqual(during["stages"][stage]["status"], "running")
            with self.assertRaises(guarded.Busy):
                guarded.advance(self.run, stage)
            with ThreadPoolExecutor(1) as pool:
                pending = pool.submit(guarded.advance, self.run, stage)
                with self.assertRaises(guarded.Busy):
                    pending.result(timeout=10)
            synthetic_child(work, stage, n)
        self.worker.side_effect = inspect
        guarded.advance(self.run, "train")
        self.assertEqual(self.worker.call_count, 1)

    def test_heldout_interruptions_never_retry_or_retune(self):
        self.complete_through("lock")
        before = guarded.load_state(self.run)["snapshot"]
        def fail(work, stage, n):
            synthetic_child(work, stage, n)
            raise SystemExit(9)
        self.worker.side_effect = fail
        with self.assertRaises(SystemExit):
            guarded.advance(self.run, "test")
        state = guarded.status(self.run)
        self.assertEqual(state["snapshot"], before)
        self.assertEqual(state["stages"]["test"]["status"], "interrupted")
        for stage in guarded.STAGES:
            with self.assertRaisesRegex(guarded.ExperimentError, "already started"):
                guarded.advance(self.run, stage)
        self.assertEqual(self.worker.call_count, 4)

    def test_failed_intent_write_launches_nothing(self):
        self.complete_through("lock")
        before = (self.run / "state.json").read_bytes()
        with patch.object(guarded.os, "replace", side_effect=OSError("disk")), self.assertRaises(OSError):
            guarded.advance(self.run, "test")
        self.assertEqual((self.run / "state.json").read_bytes(), before)
        self.assertEqual(self.worker.call_count, 3)

    def test_failed_snapshot_copy_preserves_prior_generation_and_blocks_retry(self):
        self.complete_through("lock")
        before = guarded.load_state(self.run)["snapshot"]
        original = guarded.durable_copy
        def fail(source, target):
            if target.parent.parent.name == "snapshots":
                raise OSError("disk")
            original(source, target)
        with patch.object(guarded, "durable_copy", side_effect=fail), self.assertRaises(OSError):
            guarded.advance(self.run, "test")
        self.assertEqual(guarded.status(self.run)["snapshot"], before)
        with self.assertRaisesRegex(guarded.ExperimentError, "already started"):
            guarded.advance(self.run, "test")

    def test_failed_final_replace_never_exposes_partial_or_orphan_snapshot(self):
        self.complete_through("lock")
        before = guarded.load_state(self.run)["snapshot"]
        original = guarded.atomic_json
        def fail(path, state):
            if state["stages"]["test"]["status"] == "completed":
                raise OSError("publication failed")
            original(path, state)
        with patch.object(guarded, "atomic_json", side_effect=fail), self.assertRaises(OSError):
            guarded.advance(self.run, "test")
        self.assertEqual(guarded.status(self.run)["snapshot"], before)
        self.assertEqual(len(list((self.run / "snapshots").iterdir())), 4)

    def test_post_replace_error_does_not_roll_back_a_committed_generation(self):
        self.complete_through("lock")
        original = guarded.atomic_json
        def fail_after(path, state):
            original(path, state)
            if state["stages"]["test"]["status"] == "completed":
                raise OSError("directory sync failed after replace")
        with patch.object(guarded, "atomic_json", side_effect=fail_after), self.assertRaises(OSError):
            guarded.advance(self.run, "test")
        self.assertEqual(guarded.status(self.run)["stages"]["test"]["status"], "completed")

    def test_corrupt_sources_snapshots_and_stage_order_fail_before_launch(self):
        self.complete_through("train")
        state = guarded.load_state(self.run)
        targets = [self.run / "inputs/benchmark/run_real.py",
                   self.run / "snapshots" / state["snapshot"]["id"] / "real_training.json"]
        for target in targets:
            original = target.read_bytes()
            target.write_bytes(b"changed")
            with self.assertRaisesRegex(guarded.ExperimentError, "Stored file changed"):
                guarded.advance(self.run, "tune")
            target.write_bytes(original)
        broken = deepcopy(state)
        broken["stages"]["test"] = dict(status="interrupted")
        guarded.atomic_json(self.run / "state.json", broken)
        with self.assertRaisesRegex(guarded.ExperimentError, "Invalid stage order"):
            guarded.advance(self.run, "tune")
        self.assertEqual(self.worker.call_count, 1)

    def test_malformed_or_mismatched_outputs_are_not_published(self):
        self.complete_through("lock")
        before = guarded.load_state(self.run)["snapshot"]
        def missing_array(work, stage, n):
            synthetic_child(work, stage, n)
            with zipfile.ZipFile(work / "results/real_test_raw.npz", "w") as raw:
                raw.writestr("gha_tuned_16_value.npy", b"partial")
        self.worker.side_effect = missing_array
        with self.assertRaisesRegex(guarded.ExperimentError, "Raw arrays"):
            guarded.advance(self.run, "test")
        self.assertEqual(guarded.status(self.run)["snapshot"], before)
        self.assertTrue(guarded.status(self.run)["heldout_closed"])

    def test_incomplete_tuning_does_not_replace_training_snapshot(self):
        self.complete_through("train")
        before = guarded.load_state(self.run)["snapshot"]
        def incomplete(work, stage, n):
            synthetic_child(work, stage, n)
            write_json(work / "results/real_tuning.json", dict(rows=[1], complete=False))
        self.worker.side_effect = incomplete
        with self.assertRaisesRegex(guarded.ExperimentError, "Tuning did not complete"):
            guarded.advance(self.run, "tune")
        self.assertEqual(guarded.status(self.run)["snapshot"], before)
        def restart(work, stage, n):
            self.assertFalse((work / "results/real_tuning.json").exists())
            synthetic_child(work, stage, n)
        self.worker.side_effect = restart
        self.assertEqual(guarded.advance(self.run, "tune")["stages"]["tune"]["status"], "completed")

    def test_changed_selection_binding_and_partial_completion_are_rejected(self):
        self.complete_through("lock")
        state = guarded.load_state(self.run)
        work = self.run / "attempts" / state["stages"]["lock"]["attempt"]
        synthetic_child(work, "test", None)
        marker = work / "results/real_test_started.json"
        write_json(marker, dict(selection_sha256="0" * 64))
        with self.assertRaisesRegex(guarded.ExperimentError, "bind the selection"):
            guarded.validate_output("test", work)
        synthetic_child(work, "test", None)
        record = work / "results/real_test.json"
        for complete in (False, 1, "true"):
            value = guarded.read_json(record)
            value["complete"] = complete
            write_json(record, value)
            with self.assertRaisesRegex(guarded.ExperimentError, "did not complete"):
                guarded.validate_output("test", work)

    def test_failure_to_record_interruption_still_blocks_heldout_retry(self):
        self.complete_through("lock")
        original = guarded.atomic_json
        def refuse_interruption(path, state):
            if state["stages"]["test"]["status"] == "interrupted":
                raise OSError("disk full")
            original(path, state)
        self.worker.side_effect = KeyboardInterrupt
        with patch.object(guarded, "atomic_json", side_effect=refuse_interruption), self.assertRaises(KeyboardInterrupt):
            guarded.advance(self.run, "test")
        self.assertEqual(guarded.status(self.run)["stages"]["test"]["status"], "interrupted")
        with self.assertRaisesRegex(guarded.ExperimentError, "already started"):
            guarded.advance(self.run, "test")

    def test_killed_process_leaves_durable_heldout_intent_and_releases_lock(self):
        self.complete_through("lock")
        script = """
import os, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import run_real_guarded as g
def die(work, stage, n):
    (work / 'results/real_test.json').write_text('{partial')
    os._exit(23)
g.run_child = die
g.advance(Path(sys.argv[2]), 'test')
"""
        result = subprocess.run([sys.executable, "-B", "-c", script, str(ROOT / "tools"), str(self.run)], capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 23, result.stderr.decode())
        self.assertEqual(guarded.read_json(self.run / "state.json")["stages"]["test"]["status"], "running")
        recovered = guarded.status(self.run)
        self.assertFalse(recovered["writer_active"])
        self.assertEqual(recovered["stages"]["test"]["status"], "interrupted")
        with self.assertRaisesRegex(guarded.ExperimentError, "already started"):
            guarded.advance(self.run, "test")

    def test_independent_process_is_excluded_by_writer_lock(self):
        command = [sys.executable, "-B", str(ROOT / "tools/run_real_guarded.py"), "train", "--run-dir", str(self.run)]
        with guarded.writer_lock(self.run):
            result = subprocess.run(command, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"Another wrapper owns", result.stderr)
        self.assertEqual(guarded.load_state(self.run)["stages"], {})

    def test_real_child_launcher_uses_isolated_work_and_reports_nonzero_exit(self):
        # Execute a harmless script via the actual subprocess path, never the
        # copied scientific runner. This also checks the interpreter and --n ABI.
        work = self.root / "fake"
        (work / "benchmark").mkdir(parents=True)
        script = work / "benchmark/run_real.py"
        script.write_text("import os, sys\nprint(os.getcwd(), sys.argv[1:])\nsys.exit(7)\n")
        with self.assertRaisesRegex(guarded.ExperimentError, "status 7"):
            REAL_RUN_CHILD(work, "train", 3)
        log = (work / "runner.log").read_text()
        self.assertIn(str(work), log)
        self.assertIn("['train', '--n', '3']", log)


REAL_RUN_CHILD = guarded.run_child

if __name__ == "__main__":
    unittest.main()
