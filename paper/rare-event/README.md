# General-law rare-event manuscript, revised v2

**[Read the 55-page PDF](v2/main.pdf)** · **[TeX sources](v2/main.tex)** · **[Audit index](audit/README.md)** · **[Claim status](../../docs/RESULTS.md#general-law-rare-event-characterization)**

*A general entropy-tail law for adaptive rare-event estimation* gives a paper
proof of a minimax characterization for every known magnitude law on
`(0,1/2]`, known rarity `0 < rho <= 1/4`, and positive expected budget `B`.
The estimator observes only its seed and paid Bernoulli observations, and may
create, revisit, interleave, and stop adaptively. The characterization requires
no inverse-moment or regularity assumption.

The manuscript also gives an attained four-prior stopping-program dual,
convergent genie brackets, a sufficient-cap factor-sixteen risk certificate,
and the fixed-cap target-identification threshold. Pointwise genie convergence
assumes finite latent divergence; optimized convergence first regularizes the
variance reference. The factor-sixteen statement applies to a sufficient cap
or a cap passing the verified genie criterion.

**Verification status:** paper proofs with adversarial AI audits. Exact rational
checks certify the stored finite instances. The new general characterization,
stopping-program comparison, and genie limits are not Lean-formalized, and no
external specialist review is claimed. Existing Lean results, including the
variational optimizer and fixed critical-law results, retain their own precise
scopes. These checks do not establish practical efficiency or publication priority.

## Contents and preservation

- `v2/` is the delivered source package, byte for byte, including the PDF,
  all 14 TeX files, exact verifiers and certificates, build records, revision
  notes, and source diffs. Its `MANIFEST.sha256` covers the payload.
- [Audit records](audit/README.md) distinguish the original-manuscript audits,
  final referee assessment, and subsequent audit of the first revision.
- [PUBLICATION.json](PUBLICATION.json) identifies the delivered PDF and source
  ZIP by SHA256 and records the repository base and imported payload manifest.
- The existing [v5 manuscript](../v5/README.md), [v4 manuscript](../paper.pdf),
  and [critical review packet](../critical-review/README.md) are unchanged.

This is editorial v2 of the new standalone rare-event manuscript, not a
renumbering of the repository's existing v5 paper. V2 applies exactly two
corrections to the first revised manuscript: permit the endpoint `1/128` in
the component-support sentence and repair the prose introducing conditional
normalization. See [EDITORIAL_FIXES.patch](v2/EDITORIAL_FIXES.patch).

## Verify and build

From the repository root, using only the Python standard library:

```sh
python tools/verify_rare_event_manuscript.py
```

This verifies the payload and historical-record hashes, reruns the stored
certificate checker and revision checker in a temporary copy, and replays the
independent revision-audit computations against the v2 PDF identity. It leaves
the published records unchanged. CI runs the same command.

To build the PDF, copy `v2/` to a disposable directory and run there:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The delivered PDF was built with Tectonic 0.17.0 and also checked with the
desktop LaTeX compiler. Its build and visual-review record is
[VERIFICATION.json](v2/VERIFICATION.json). Builds may differ in metadata or
engine output; the recorded hash identifies the delivered PDF.

The repository's [license scope](../../LICENSES.md) applies: paper and
documentation under CC BY 4.0, code under Apache-2.0, with preserved third-party
notices. AI-assisted provenance and review limits are retained in the manuscript.
