# Manuscript provenance

This standalone manuscript consolidates the rare-event research notes and their subsequent mathematical development. Its immediate source is the complete clarified proof after the fresh review of 29 October 2026. Earlier working notes include *A general entropy-tail law for adaptive rare-event estimation* and *A closed quantile law for entropy-tail selection*. The arguments used here are reproduced in full; neither note is an external mathematical premise. Public methodological antecedents remain cited in the manuscript.

AI agents carried out the research and editorial preparation under the project's human direction, as described in the repository's [provenance record](../../docs/process/PROVENANCE.md). The preceding reviewer was a fresh-context AI agent using the inherited model, without the earlier conversation or audit conclusions. This does not constitute external human refereeing, review by a different model, or formal verification.

## Editorial changes

- Replaced continuation and audit framing with a standalone title, abstract, model section, proof roadmap and public bibliography.
- Promoted the already-derived constants $10^{-20}$ and $30001$, with the complete algorithm, parameter and budget quantifiers, into Theorem 1.1.
- Made the cutoff, sign, information-distance, cost-entropy and zero-coordinate conventions explicit.
- Preserved all 19 named results and all 18 proof environments from the precursor. Seventeen proof blocks are identical after the disclosed notation and citation normalization; the other removes only a sentence saying that there is no optimization over submeasures.
- Added a proved two-point testing lemma and proved mean-square and one-gap corollaries. The mean-square conclusion was already stated in prose in the input.
- Used one squared-Hellinger notation distinct from the budget scale and added a precise Sion minimax citation.

The repository import preserves the standalone manuscript's 32-page PDF byte for byte. All 13 TeX files retain their content; trailing whitespace and terminal blank lines are normalized in `entropy_tiers.tex`, `transfer_foundations.tex` and `upper_foundations.tex`. The README and this provenance note are adapted for their repository location. [SHA256SUMS](SHA256SUMS) records the distributed files.

## Verification boundary

The precursor's fresh AI review found no fatal gap or counterexample. This editorial version passed source-conservation checks, reference checks, compilation and visual inspection. It has not had external specialist review and is not Lean-checked. Compilation and numerical diagnostics do not certify the theorem, and existing Lean statements in this repository do not extend to it by association.

The claim is limited to known finite positive-gap laws, iid persistent latent pairs, global rarity, RMS loss and a uniform expected physical-observation budget. This preparation does not establish novelty, optimal constants or a broader model.

Attribution and licensing follow [LICENSES.md](../../LICENSES.md). The TeX manuscript leaves its author line blank; the repository's attribution policy is not a claim of completed journal authorship or external review.
