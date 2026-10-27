# Run record

This pass continued from shared HEAD d75c775633df545b892e69fc876930d6d2dcc329. Another task advanced that checkout to 7311b6da2620924dad79bdfd795a87465746f67e. The new branch is based on our previously published 3897d390d2fdd66d6f3f4b84fabfe523b0e031ba; only this directory is included. STATE.md records the dirty state and environment. Commands below were executed from the repository root unless explicitly labeled as pending finalization.

The initial inspection read Git status/HEAD, the current research and inherited single-coin obstruction, concurrent nonlinear-critical notes and original audit tooling. Three delegated agents did actual construction, certificates and adversarial review. Their exact commands and source checkpoints appear in upper/RUN_LOG.md, audit/RUN_LOG.md and audit/RUN_LOG_V2.md. The full mathematical source was reviewed again after substantive extensions. Early reads of files still being written returned file-not-found; no content was inferred from those failures.

Executed certificate and experiment commands:

```powershell
python research/2026-10-27-nonlinear-population/lower/feedback_certificate.py
python research/2026-10-27-nonlinear-population/lower/full_class_certificate.py
python research/2026-10-27-nonlinear-population/upper/check_exact.py
python research/2026-10-27-nonlinear-population/feedback_experiment.py lock
python research/2026-10-27-nonlinear-population/feedback_experiment.py run
python research/2026-10-27-nonlinear-population/analyze_experiment.py
python research/2026-10-27-nonlinear-population/replay_experiment.py
python research/2026-10-27-nonlinear-population/regressions.py
python research/2026-10-27-nonlinear-population/assemble_note.py
```

The experiment was locked before its 7,680 runs. It used 3,440,640 flips and 41.22453 seconds in the saved completion record. Replicate zero from every one of 240 cells replayed, using another 107,520 flips; see REPLAY.json. Analysis did not change the frozen candidate. No general convex program was solved. No new Lean build was run. The regression runner executed all four unchanged validator test scripts (34 tests total) and verify_inputs.py (50 inputs), all successfully; raw logs are preserved.

The audit agent independently executed replay.py (then a fresh replay_final.json), check_experiment.py (then a fresh experiment_audit_final.json), and replay_v2.py. These completed successfully. Their historical outputs remain separate; the latest source hashes are used for final acceptance. Source browsing and exact inspected passages are recorded in audit/RUN_LOG.md. No external correspondence was sent.

The PDF operation marker was called once before artifact creation. The bundled Tectonic 0.17.0+20260731 was run with `--only-cached --untrusted --keep-logs`, using the existing cache at `../minimax-baseline-snapshot/.tectonic-cache`. The first build succeeded but emitted one overfull filename paragraph; compile_attempt_1.log is preserved. assemble_note.py was updated only to allow a line break before that filename in a derived body. Reviewed proof sources remained unchanged. The final compilation succeeded with 14 pages, no overfull boxes and no undefined references. Underfull spacing warnings remain. Poppler rendered all pages and the contact sheet was inspected; no clipping or overlap was seen. Font copies and page renders are ignored local build aids, not distributed assets.

Finalization commands are recorded by their generated outputs, rather than claimed here in advance:

```powershell
python research/2026-10-27-nonlinear-population/check_checkpoint.py
python research/2026-10-27-nonlinear-population/prepare_commit.py
```

ACCEPTANCE.json is produced only by the final checks, including every original freeze hash, current reviewed-source hashes, locked data, PDF assembly and required files. CHECKPOINT_SHA256.json is a post-proof evidence seal, not preregistration. prepare_commit.py uses an isolated index and a new ref, leaving the shared checkout/index untouched, and independently checks all committed file bytes against the seal. It does not push. An ignored PUBLICATION_RECEIPT.json records the actual commit and subsequently verified remote ref; GitHub history is the public publication record. Publication is authorized by the user. There is no promised background continuation.
