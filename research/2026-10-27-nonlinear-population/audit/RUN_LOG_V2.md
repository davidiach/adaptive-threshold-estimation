# Additional audit run log

The parent requested independent review of two new additions after the first
audit checkpoint: the full-rarity-class cap-two separation and the faithful
finite approximation theorem. Older audit outputs were preserved.

The new complete proofs and certificate source were read. An early batched
read found FINITE_APPROXIMATION.tex not yet present while its author was still
writing it. The lower files in that batch were read successfully. After the
upper agent reported completion, the complete approximation source was read;
the requested distinct-representative correction was then inspected. No
source or proof was inferred from the initially missing file.

The only new arithmetic execution was:

```powershell
python research/2026-10-27-nonlinear-population/audit/replay_v2.py
```

Exit code 0, Python 3.12.2. Output:

```text
PASS: full-Qrho certificate; 153 direct latent grid checks; 3 exact edge reconstructions; v1 hashes unchanged
```

The checker uses Fraction arithmetic for all certifications. It writes only
the new `replay_v2.json`; it imports the lower certificate as a module, so
the author's existing certificate JSON is not overwritten. It records the
actual shared HEAD `7311b6da2620924dad79bdfd795a87465746f67e`, not the older
checkpoint HEAD. The before/after source hashes agree. Its exact interpolation
uses direct latent-mixture probabilities rather than the author's polynomial
multiplication code. The all-parameter conclusion still uses the separately
reviewed degree and convexity proof.

To replay after checkout without overwriting historical evidence:

```powershell
python research/2026-10-27-nonlinear-population/audit/replay_v2.py replay_v2_local_new.json
```

No new Monte Carlo run, convex-program solve, Lean build, literature search,
PDF compilation, commit, push or external correspondence was performed by
this audit agent in the additional pass. The parent controls repository
integration and publication of verified files.
