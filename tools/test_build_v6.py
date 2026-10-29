"""Regression checks for the consolidated v6 manuscript assembly."""
import re
import unittest
from pathlib import Path

from build_v6 import DEST, ROOT, assemble, check_project, project_text, rekey

GL = ROOT / "paper/rare-event/v2/sections"
FG = ROOT / "paper/finite-gap-rare-events/revision-2/sections"


def lines(text: str) -> list[str]:
    text = re.sub(r"(\\cite(?:\[[^]]+\])?)\{lv\}", r"\1{leevaliant}", text.replace("\r", ""))
    return [" ".join(line.split()) for line in text.split("\n") if line.strip()]


def missing(source: Path, generated: str) -> set[str]:
    present = set(lines(generated))
    return {line for line in lines(source.read_text(encoding="utf-8")) if line not in present}


# Finite-gap appendix lines intentionally absent from the merged appendices.
FINITE_GAP_REPLACED = {
    "upper_foundations": {
        # The merged introduction states both papers' conventions.
        r"This appendix proves the single-coin classification bounds and the",
        r"finite multilevel estimator used in Section~\ref{sec:direct-upper}.",
        r"Throughout this appendix, a false-positive probability means the joint",
        r"event $\Pp_q(Z=1,s=0)$, with the binary sign $s=\mathbf1_{\{S=+1\}}$, not the conditional",
        r"probability $\Pp_q(Z=1\mid s=0)$. All likelihoods",
        r"refer to the actual binary observations. A reference distribution evaluates",
        r"that prefix and does not reveal or redraw the latent state of a coin.",
        # The general-law appendix writes the binary sign as S.
        r"$\Pp_q(Z_0=1)\le\Pp_q(s=1)+f_0\le\rho+f_0$.",
    },
    "lower_foundations": {
        r"This appendix proves the sign-testing and annular ingredients used in",
        # The general-law appendix proves the stronger constant 214 for 257.
        r"\frac{1+\operatorname{Ent}(\pi)}{257}.",
        r"Writing $\bar c=\sum_j\pi_jc_j$ and using $\bar c\ge1/16$, we obtain",
        r"$1+\operatorname{Ent}(\pi)\le65\bar c+12\le257\bar c$, as required.",
        r"\frac{1+\Ent(\pi)}{257}",
        r"\le1028\rho nW_0^Z",
        r"\le1\,069\,120\,m_ZW_0^Z",
        r"\le1\,069\,120\,C_g^4P.",
        # The model reference points to the common rare-event experiment.
        r"Section~\ref{sec:model}.",
    },
    "transfer_foundations": {
        r"lower bound. The finite-experiment",
        # The general-law appendix cites Lee--Valiant Lemmas 17--18.
        r"Lee--Valiant \cite[Lemma 17]{leevaliant}, written in the form needed here.",
        r"For unbounded stopping in the applications here, the same endpoint pair",
        r"Set $k=42\delta^2/J$ and use the oriented compact convex pair set",
        r"The same total budget $B$ occurs in every summand.",
        # The general-law appendix states the exact conversion identity here.
        r"Consequently, writing the corresponding unnormalized quantities with",
        r"respect to $\sigma_i$ as $\Gamma_{\sigma_i}^{\circ}=\tau_i\Gamma_i^{\circ}$ and",
        r"$w_{*,\sigma_i}=\tau_iw_{*,i}$, we obtain",
        r"Section~\ref{sec:matching-lower} applies this bound to the components",
        r"constructed by the quantile-core filter and packing.",
    },
}

# General-law appendix lines replaced by the finite-gap clarifications, by the
# Hellinger symbol, or by references inside the consolidated paper.
GENERAL_LAW_REPLACED = {
    "upper_foundations": {
        r"This section proves the specialized upper-bound tools used below. The",
        r"ordinary classifier is the construction in the supplied manuscript",
        r"\cite{original,repo}; the weighted reference bank and multilevel",
        r"allocation are restated with their proofs so that the present paper",
        r"does not depend on the preceding unpublished notes. All likelihoods",
        r"is used to evaluate that prefix, and never reveals or redraw the",
        r"Independently across levels, draw Poisson replication counts with means",
    },
    "lower_foundations": {
        r"$c_j>3/40>1/16$.",
        r"The new lower-bound ingredient charges activation at the information",
        r"h(P_-,P_+)\le\tfrac12\kappa a^2W_0,",
        r"where \(h=1-\operatorname{Aff}\).",
        r"\le4(\E_PF^2+\E_QF^2)h(P,Q).",
        r"Let \(p=\Pp_{\rm fair}(E)\) and \(p_s(d)=\Pp_{d,s}(E)\). Then",
        r"Since \(h\le\KL/2\), \eqref{eq:cross-hellinger-moment} implies",
        r"accepted trial. Moreover,",
        r"Otherwise a fractional prior of total mass \(\rho\) on that set would",
        r"contradict the bias guarantee and the mean separation \(31\rho/32\).",
        r"bounded by \(1/128\).",
    },
    "transfer_foundations": {
        r"function. Sion's minimax theorem \cite{sion} therefore applies to $X\times X$ and",
        r"$\mathcal F\times(0,\infty)$. Write",
        r"We use $h(P,Q)=1-\Aff(P,Q)$, so $0\le h\le1$ and",
        r"$\operatorname{TV}(P,Q)\le\sqrt{2h(P,Q)}$.",
        r"h(P_-^A,P_+^A)\le\kappa\,\E_{\bar q}T_A.",
        r"h(P_-^{\rm pop},P_+^{\rm pop})",
        r"For observable types, use the type selected at a slot in each leaf.",
        r"The same product factorization holds, with its type-specific local",
        r"kernel. To realize a hybrid locally, first simulate the midpoint",
        r"history before the slot's first observation; its type and that history are",
        r"part of the independent seed. The genuine unit has the selected type's",
        r"prescribed latent law independently of that seed. Future simulated midpoint",
        r"units use fresh independent seeds. Conditional on the preceding history, the hypothesis",
        r"for the selected type applies. Sum and integrate as above. No latent",
        r"magnitude or sign is supplied to the local policy.",
        r"h(P_{q_-}^A,P_{q_+}^A)",
        r"h\le\frac{\log2}{n}",
        r"cell with probability \(\varepsilon>0\). Run the policy even on",
        r"and reveal the chosen index. Both work and squared Hellinger distance",
        r"are affine in the mixture weights. Hellinger is continuous and convex",
        r"in the parameter pair. Finite-simplex minimax gives a pair satisfying",
        r"every constraint in the collection. The constraint sets are closed in",
        r"the weak-star compact convex set",
        r"\{(q_-,q_+)\in X_\rho^2:",
        r"Let \(\varepsilon\downarrow0\), then use that full squared Hellinger",
        r"distance is the supremum over finite measurable partitions. This proves",
        r"For Bernoulli observations, define the known variational modulus \cite{repo}",
        r"\le4(\E_PY^2+\E_QY^2)h(P,Q),\qquad",
        r"h(P,Q)\le\tfrac12\KL(P,Q).",
        r"h(P_{i,-}^A,P_{i,+}^A)",
        r"Consider a stronger experiment that can select a component at no cost and",
        r"adaptively select, revisit, and interleave these coins. Under the conditional",
        r"scale to be chosen separately. Section~\ref{sec:matching-lower} applies this expression to components",
        r"selected by the entropy--tail optimizer.",
    },
}

APPENDIX = {"upper_foundations": "appendix-upper-foundations.tex",
            "lower_foundations": "appendix-lower-foundations.tex",
            "transfer_foundations": "appendix-transfer-foundations.tex"}


class ConsolidatedAssemblyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.output = assemble()

    def test_generated_sources_are_current(self):
        for name, text in self.output.items():
            with self.subTest(name=name):
                self.assertEqual((DEST / name).read_text(encoding="utf-8"), text)

    def test_project_labels_references_and_citations_resolve(self):
        label_count, cite_count = check_project(project_text(DEST))
        self.assertGreater(label_count, 300)
        self.assertGreater(cite_count, 20)

    def test_merged_appendices_keep_every_finite_gap_line(self):
        for name, replaced in FINITE_GAP_REPLACED.items():
            with self.subTest(name=name):
                self.assertEqual(missing(FG / (name + ".tex"), self.output[APPENDIX[name]]),
                                 replaced)

    def test_merged_appendices_change_only_listed_general_law_lines(self):
        for name, replaced in GENERAL_LAW_REPLACED.items():
            with self.subTest(name=name):
                self.assertEqual(missing(GL / (name + ".tex"), self.output[APPENDIX[name]]),
                                 replaced)

    def test_entropy_tier_lemma_keeps_both_versions(self):
        lower = self.output["appendix-entropy-tail-lower.tex"]
        self.assertEqual(missing(FG / "entropy_tiers.tex", lower), set())

    def test_merged_appendices_use_stronger_sign_entropy_constant(self):
        lower = self.output["appendix-lower-foundations.tex"]
        self.assertIn(r"\frac{1+\operatorname{Ent}(\pi)}{214}.", lower)
        self.assertNotIn("257", lower)

    def test_hellinger_distance_never_shares_the_budget_scale_symbol(self):
        for name in ("appendix-lower-foundations.tex", "appendix-transfer-foundations.tex"):
            with self.subTest(name=name):
                text = self.output[name]
                self.assertIsNone(re.search(r"(?<!\\mathfrak )(?<![\\\w])h\((?:P|Q)", text))
                self.assertIn(r"\mathfrak h(P", text)

    def test_finite_upper_bound_cites_the_general_construction(self):
        upper = self.output["finite-upper.tex"]
        self.assertNotIn(r"\subsection{An uncapped reference bank", upper)
        self.assertNotIn(r"\label{eq:split", upper)
        self.assertIn(r"Appendix~\ref{sec:entropy-tail-upper}", upper)
        self.assertIn(r"\eqref{eq:split-poisson}", upper)
        self.assertIn(r"30000(R+H)", upper)

    def test_repeated_construction_matches_the_general_construction(self):
        # Outside the renamed resolved law and finite-bank remarks, the
        # dropped finite-gap construction is the general-law text.
        finite = (FG / "direct_upper.tex").read_text(encoding="utf-8")
        general = (GL / "additive.tex").read_text(encoding="utf-8")
        start = r"\subsection{An uncapped reference bank with a capped observable race}"
        end = r"\begin{proof}[Completion of Theorem~\ref{thm:"
        repeated = finite[finite.index(start):finite.index(end)].replace(r"\chi", r"\nu")
        construction = general[general.index(start):general.index(end)]
        differing = missing_lines(repeated, construction)
        self.assertLessEqual(differing, {
            "Use the fixed decomposition above, put",
            "has risk at most $64z$. For a finite submeasure $\\xi$, define explicitly",
            "\\[", "\\]",
            "a_j(\\xi)=\\int_{I_j}d^{-2}\\,\\xi(dd),\\qquad",
            "A_\\xi=\\sum_j a_j(\\xi),\\qquad H_\\xi=\\int d^{-1}\\,\\xi(dd),",
            "\\Gamma_\\xi=A_\\xi+\\sum_j a_j(\\xi)\\log(A_\\xi/a_j(\\xi)).",
            "Zero coordinates are omitted, and all three quantities are zero for the",
            "zero measure. These are exact inverse-square costs, not the rounded",
            "canonical costs used in the lower bound. Write $A=A_\\sigma$, $H=H_\\tau$.",
            "stop. The known all-negative mixture in the denominator is the full law",
            "In the finite-law theorem the reference bank is finite; its stopping",
            "events are measurable and its positive reference is a finite probability",
            "mixture. No countable-support extension is needed here.",
        })

    def test_finite_gap_labels_do_not_collide_with_version_5(self):
        labels = re.findall(r"\\label\{([^}]+)\}", project_text(DEST))
        self.assertIn("sec:model", labels)
        self.assertIn("fg:sec:model", labels)
        self.assertIn("fg:thm:direct-main", labels)
        self.assertEqual(len(labels), len(set(labels)))

    def test_rekey_changes_only_listed_keys(self):
        source = r"\label{a}\eqref{a,b}\cref{b}\ref{c}"
        self.assertEqual(rekey(source, {"a": "fg:a"}),
                         r"\label{fg:a}\eqref{fg:a,b}\cref{b}\ref{c}")

    def test_no_companion_or_supplied_manuscript_citations_remain(self):
        text = project_text(DEST)
        for key in ("gl", "original", "repo", "lv"):
            with self.subTest(key=key):
                self.assertIsNone(re.search(r"\\cite(?:\[[^]]+\])?\{[^}]*\b" + key + r"\b", text))


def missing_lines(source: str, generated: str) -> set[str]:
    present = set(lines(generated))
    return {line for line in lines(source) if line not in present}


if __name__ == "__main__":
    unittest.main()
