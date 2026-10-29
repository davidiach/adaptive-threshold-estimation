# Audit records and their scope

Start with the [final referee report](final_referee_report.pdf) and the
[revision audit](revision/revised_changes_audit.txt). These are AI-assisted
mathematical reviews, not external specialist reports or Lean certificates.

| Record | Manuscript examined | Interpretation |
|---|---|---|
| [Original audit scripts and results](original/) | The supplied 28 October standalone manuscript | Historical falsification checks of the upper/lower bounds, finite program, compactness, and their interfaces. |
| [Final referee report](final_referee_report.pdf) and [manifest](final_referee_report_manifest.json) | Original manuscript, after consolidating the audits | No established fatal error in the principal theorems; clarifications and optional improvements recommended. |
| [Revision audit](revision/revised_changes_audit.txt), [script](revision/revised_changes_adversarial_audit.py), and [results](revision/revised_changes_adversarial_audit_results.json) | First revised manuscript | Sharper constants, examples, and genie fix survived the checks. Two minor editorial defects were identified. |
| [V2 editorial patch](../v2/EDITORIAL_FIXES.patch) and [verification](../v2/VERIFICATION.json) | Delivered editorial v2 | Both defects are fixed; only PDF pages 15 and 36 changed. Earlier versions were preserved. |

## Corrections to historical wording

The supplied pointwise genie theorem already conditioned convergence on finite
`C_v`. The counterexample refutes an **unconditional extension**, not the stated
conditional theorem or optimized genie convergence. The final referee report
and its manifest supersede any stronger interpretation of earlier audit records.

The final referee report calls `M_0` a null second moment in its B.3 discussion.
That description is incorrect: `M_0` is the **uniform** second-moment supremum;
`W_0` is null work. The revised manuscript and its revision notes state this
correctly. The historical report is preserved rather than silently rewritten.

The revision audit's two editorial findings concern the first revision. Its
PDF hash therefore differs from v2. The v2 patch resolves both findings and
does not change the audited constants or examples.

## Reproduction and identity

[MANIFEST.sha256](MANIFEST.sha256) preserves the 26 historical audit files
byte for byte. The source records include their original target hashes; those
records are not claims of fresh validation of every later revision.

Run `python tools/verify_rare_event_manuscript.py` from the repository root for
the portable current check. It imports the revision audit's unchanged
computation functions, replays them on a temporary copy, and reports the v2
PDF hash. It does not invoke that historical script's workspace-specific
`main()` or overwrite its stored first-revision result. The older finite-program
audit also retains its original workspace path; its historical output is
preserved, while the delivered exact certificate verifiers run independently
as part of the current check.

Exact rational certificate checks, high-precision arithmetic, and numerical
falsification searches have different scopes. None alone proves the general
statistical or compactness theorems. The reports give the accompanying analytic
arguments and distinguish failed shortcuts from failures of stated results.
