"""Regression checks for the consolidated v6 manuscript assembly."""
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import copy

import build_v6
from build_v6 import (DEST, ROOT, STATUS_WORDS, assemble, check_project, load_status,
                      project_text, rekey, status_text, validate_status)
from build_v6 import STATUS as STATUS_PATH

GL = ROOT / "paper/rare-event/v2/sections"
FG = ROOT / "paper/finite-gap-rare-events/revision-2/sections"


def lines(text: str) -> list[str]:
    text = re.sub(r"(\\cite(?:\[[^]]+\])?)\{lv\}", r"\1{leevaliant}", text.replace("\r", ""))
    # Former main-text sections are cited as appendices in the consolidated paper.
    text = text.replace(r"Appendix~\ref{", r"Section~\ref{")
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
                self.assertEqual((DEST / name).read_bytes(), text.encode("utf-8"))

    def test_check_rejects_line_ending_drift(self):
        # .gitattributes keeps exact bytes, so --check must compare bytes too.
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp)
            for path in DEST.iterdir():
                if path.suffix in (".tex", ".json"):
                    shutil.copyfile(path, dest / path.name)
            name = sorted(self.output)[0]
            with mock.patch.object(build_v6, "DEST", dest), \
                    mock.patch.object(sys, "argv", ["build_v6.py", "--check"]), \
                    mock.patch("builtins.print"):
                build_v6.main()
                crlf = (dest / name).read_bytes().replace(b"\n", b"\r\n")
                (dest / name).write_bytes(crlf)
                with self.assertRaisesRegex(SystemExit, "Generated v6 source differs"):
                    build_v6.main()

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


class VerificationStatusTests(unittest.TestCase):
    """The abstract and boundary status sentences come only from status.json."""

    def setUp(self):
        self.status = load_status()

    def generated(self, status, venue):
        if venue == "abstract":
            return " ".join(build_v6.abstract_status_text(status).split())
        return " ".join(status_text(status, venue).split())

    def test_status_change_moves_a_result_in_every_venue(self):
        status = copy.deepcopy(self.status)
        status["results"]["rms-law"]["status"] = "paper"
        status["results"]["psi-lower-bound"]["status"] = "paper"
        status["results"]["arbitrary-law-adaptation"]["status"] = "lean"
        abstract = self.generated(status, "abstract")
        boundary = self.generated(status, "boundary")
        self.assertIn("For the original RMS law in both directions", abstract)
        self.assertIn("the arbitrary-law statistical $\\Psi$ lower bound", abstract)
        self.assertNotIn("eventual oracle-rate adaptation", abstract)
        self.assertIn("For the arbitrary-law statistical $\\Psi$ lower bound", boundary)
        self.assertIn("Lean also checks arbitrary-law oracle adaptation", boundary)
        self.assertIn("For both directions of the original RMS law", boundary)
        self.assertNotIn("checks both directions of the original RMS law", boundary)

    def test_every_entry_reads_correctly_under_either_status(self):
        for key, result in self.status["results"].items():
            for kind in ("lean", "paper"):
                status = copy.deepcopy(self.status)
                status["results"][key]["status"] = kind
                for venue in ("abstract", "boundary"):
                    # The abstract names a paper proof by its abstract phrase,
                    # or by its boundary phrase when it has no abstract phrase.
                    source = venue if venue in result else "boundary"
                    if venue == "boundary" and venue not in result:
                        continue
                    with self.subTest(key=key, kind=kind, venue=venue):
                        text = self.generated(status, venue)
                        phrase = " ".join(result[source].split())
                        if venue == "abstract" and kind == "lean":
                            # Checked results are counted in the abstract, not named.
                            self.assertNotIn(phrase, text)
                            continue
                        self.assertIn(phrase, text)
                        sentence = next(s for s in text.split(". ") if phrase in s)
                        if kind == "lean":
                            self.assertTrue(sentence.startswith("Lean "), sentence)
                        else:
                            self.assertTrue(sentence.startswith("For "), sentence)
                            self.assertIn("the manuscript gives paper proofs only", text)

    def test_generated_status_matches_the_source(self):
        output = assemble()
        abstract = output["status-abstract.tex"].split("\n", 1)[1]
        self.assertEqual(abstract.rstrip("\n"), build_v6.abstract_status_text(self.status))
        table = output["status-table.tex"].split("\n", 1)[1]
        self.assertEqual(table.rstrip("\n"), build_v6.status_table(self.status, output))
        boundary = self.generated(self.status, "boundary")
        self.assertIn(boundary, " ".join(output["introduction.tex"].split()))

    def test_abstract_counts_checked_results_and_names_only_paper_proofs(self):
        results = self.status["results"]
        total = len(results)
        paper = [key for key, result in results.items() if result["status"] == "paper"]
        abstract = self.generated(self.status, "abstract")
        self.assertTrue(abstract.startswith(
            f"Lean checks {total - len(paper)} of the {total} results listed in "
            "\\cref{tab:status}"), abstract)
        for item in self.status["abstract"]:
            if "text" in item:
                self.assertIn(" ".join(item["text"].split()), abstract)
        every = copy.deepcopy(self.status)
        none = copy.deepcopy(self.status)
        for key in results:
            every["results"][key]["status"] = "lean"
            none["results"][key]["status"] = "paper"
        text = self.generated(every, "abstract")
        self.assertTrue(text.startswith(f"Lean checks all {total} results"), text)
        self.assertNotIn("paper proofs only", text)
        text = self.generated(none, "abstract")
        self.assertTrue(text.startswith("For "), text)
        self.assertNotIn("Lean checks", text)
        # One more checked result changes the count, not the length of the list.
        more = copy.deepcopy(self.status)
        more["results"][paper[0]]["status"] = "lean"
        self.assertIn(f"Lean checks {total - len(paper) + 1} of the {total} results",
                      self.generated(more, "abstract"))

    def test_status_table_lists_every_result_once_under_its_status(self):
        results = self.status["results"]
        table = build_v6.status_table(self.status)
        rows = [line for line in table.splitlines() if line.endswith("\\\\[2pt]")]
        self.assertEqual(len(rows), len(results))
        self.assertIn("\\label{tab:status}", table)
        checked, paper = table.split("\\emph{Paper proof only")
        for key, result in results.items():
            phrase = result.get("summary") or result.get("abstract") or result["boundary"]
            row = build_v6._sentence_case(phrase) + " & "
            with self.subTest(key=key):
                self.assertEqual(table.count(row), 1)
                self.assertIn(row, checked if result["status"] == "lean" else paper)
        counts = {kind: sum(r["status"] == kind for r in results.values())
                  for kind in ("lean", "paper")}
        self.assertIn(f"\\emph{{Checked in Lean ({counts['lean']} results)}}", table)
        self.assertIn(f"({counts['paper']} results)", paper)
        # A paper proof points to the section that holds it; a checked result to its modules.
        self.assertIn("unknown gap laws & \\cref{sec:arbitrary-law-adaptation}", paper)
        self.assertNotIn("\\path{", paper)
        self.assertIn("\\path{Tier6/Full.lean}", checked)
        flipped = copy.deepcopy(self.status)
        flipped["results"]["rms-law"]["status"] = "paper"
        changed = build_v6.status_table(flipped).split("\\emph{Paper proof only")[1]
        self.assertIn("Original RMS law in both directions", changed)
        self.assertIn("See \\cref{sec:verification}", changed)

    def rejects(self, mutate, message):
        status = copy.deepcopy(self.status)
        mutate(status)
        with self.assertRaisesRegex(ValueError, message):
            validate_status(status)

    def test_status_words_stay_in_the_status_field(self):
        def phrase(s): s["results"]["confidence"]["abstract"] += ", Lean-checked"
        def proved(s): s["results"]["confidence"]["boundary"] += " are also proved"
        def text(s): s["abstract"].append({"text": "All of this is a paper proof."})
        def suffix(s): s["boundary"][1]["suffix"] = " as verified in Lean"
        def wrapped(s): s["abstract"].append({"text": "All of this is a paper\nproof."})
        def summary(s): s["results"]["confidence"]["summary"] = "the confidence law, formalized"
        for mutate in (phrase, proved, text, suffix, wrapped, summary):
            with self.subTest(mutate=mutate.__name__):
                self.rejects(mutate, "Status wording")

    def test_phrases_are_safe_tex(self):
        def percent(s): s["results"]["unbiased"]["abstract"] += " 50% of"
        def braces(s): s["results"]["unbiased"]["abstract"] += " \\cref{x"
        def math(s): s["results"]["unbiased"]["abstract"] += " $x"
        def empty(s): s["results"]["unbiased"]["abstract"] = " "
        def summary_math(s): s["results"]["unbiased"]["summary"] = "the $x law"
        for mutate, message in ((percent, "unescaped %"), (braces, "unbalanced"),
                                (math, "unbalanced"), (empty, "non-empty"),
                                (summary_math, "unbalanced")):
            with self.subTest(mutate=mutate.__name__):
                self.rejects(mutate, message)

    def test_every_status_needs_existing_evidence_in_the_repository(self):
        cases = {
            "missing": (["lean/ThresholdHC/Missing.lean"], "not an existing path"),
            "outside": (["../outside"], "relative repository paths"),
            "root": (["."], "not an existing path"),
            "absolute": (["/etc/hosts"], "relative repository paths"),
            "empty": ([], "non-empty list"),
            "no lean evidence": (["docs/RESULTS.md"], "under lean/ or results/"),
            "dot-dot inside": (["lean/../docs/RESULTS.md"], "relative repository paths"),
        }
        for name, (evidence, message) in cases.items():
            with self.subTest(case=name):
                self.rejects(lambda s: s["results"]["unbiased"].__setitem__("evidence", evidence), message)
        self.rejects(lambda s: s["results"]["unbiased"].__setitem__("status", "proved"), "must be one of")

    def test_entries_are_used_and_phrased_for_their_venues(self):
        def orphan(s):
            s["results"]["orphan"] = {"status": "lean", "evidence": ["lean/ThresholdHC/Tier6/Full.lean"]}
        def unphrased(s): del s["results"]["unbiased"]["boundary"]
        def dropped(s): s["boundary"][1]["results"].remove("unbiased")
        def repeated(s): s["abstract"][0]["results"].append("rms-law")
        def unknown_field(s): s["results"]["unbiased"]["note"] = "x"
        def unknown_item(s): s["abstract"].append({"results": ["rms-law"], "lead": "x"})
        def top_level(s): s["extra"] = []
        def text_extra(s): s["abstract"].append({"text": "A note.", "suffix": " here"})
        for mutate, message in ((orphan, "Unused status entries"), (unphrased, "No boundary phrase"),
                                (dropped, "not listed there"), (repeated, "repeated"),
                                (unknown_field, "Unknown fields"), (unknown_item, "Malformed"),
                                (top_level, "exactly"), (text_extra, "Malformed")):
            with self.subTest(mutate=mutate.__name__):
                self.rejects(mutate, message)

    def test_duplicate_keys_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "status.json"
            text = STATUS_PATH.read_text(encoding="utf-8").replace(
                '"results": {', '"results": {\n    "rms-law": {"status": "lean"},', 1)
            path.write_text(text, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Duplicate keys"):
                load_status(path)

    def test_status_words_match_only_status_uses(self):
        self.assertIsNotNone(STATUS_WORDS.search("Lean-checked"))
        self.assertIsNotNone(STATUS_WORDS.search("a paper~proof"))
        self.assertIsNone(STATUS_WORDS.search("a lean estimator"))

    def test_list_joins_ignore_braced_and_math_commas(self):
        self.assertFalse(build_v6.has_list_comma(r"results of \cref{a,b}"))
        self.assertFalse(build_v6.has_list_comma(r"the pair $(a,b)$"))
        self.assertTrue(build_v6.has_list_comma("the law, with constants"))
        self.assertEqual(build_v6.join_phrases(["a", "b and c", "d"]), "a, b and c, and d")
        self.assertEqual(build_v6.join_phrases(["a", "b"]), "a and b")

    def test_section18_rows_agree_with_status(self):
        tex = (DEST / "verification.tex").read_text(encoding="utf-8")
        build_v6.check_verification_rows(self.status, tex)
        rows = build_v6.verification_rows(tex)
        self.assertIn("Rare-event rates below two", rows)
        self.assertGreaterEqual(len(rows), 18)
        for key in ("rms-law", "psi-lower-bound"):
            with self.subTest(key=key):
                status = copy.deepcopy(self.status)
                status["results"][key]["status"] = "paper"
                with self.assertRaisesRegex(ValueError, "must say paper proof"):
                    build_v6.check_verification_rows(status, tex)
        # A row that stops citing its Lean source no longer supports a lean status.
        label = "General statistical $\\Psi$ lower bound"
        uncited = tex.replace(rows[label], "\nThe bound remains a paper theorem.")
        self.assertNotEqual(uncited, tex)
        with self.assertRaisesRegex(ValueError, "cites no Lean source"):
            build_v6.check_verification_rows(self.status, uncited)
        for key, result in self.status["results"].items():
            if result.get("verification_rows"):
                with self.subTest(flipped=key):
                    status = copy.deepcopy(self.status)
                    status["results"][key]["status"] = "paper" if result["status"] == "lean" else "lean"
                    with self.assertRaises(ValueError):
                        build_v6.check_verification_rows(status, tex)
        status = copy.deepcopy(self.status)
        status["results"]["unbiased"]["verification_rows"] = ["No such row"]
        with self.assertRaisesRegex(ValueError, "no claim row"):
            build_v6.check_verification_rows(status, tex)

    def test_abstract_has_no_hand_written_status(self):
        text = (DEST / "frontmatter.tex").read_text(encoding="utf-8")
        body = re.sub(r"(?<!\\)%[^\n]*", "", text)
        self.assertIn("\\input{status-abstract}", body)
        self.assertIsNone(STATUS_WORDS.search(body), STATUS_WORDS.search(body))

if __name__ == "__main__":
    unittest.main()
