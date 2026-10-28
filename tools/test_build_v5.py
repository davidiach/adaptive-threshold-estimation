"""Regression checks for mathematical fidelity during manuscript assembly."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from build_v5 import assemble, between, prefix_equation_tags, project_text


class ManuscriptAssemblyTests(unittest.TestCase):
    def test_input_graph_rejects_missing_or_dropped_addendum(self):
        for directive, error in ((r'\input{typo}', 'Missing TeX input'),
                                 ('', 'Unincluded TeX source'),
                                 (r'% \input{addendum}', 'Unincluded TeX source')):
            with self.subTest(directive=directive), TemporaryDirectory() as tmp:
                folder = Path(tmp)
                (folder/'main.tex').write_text(directive, encoding='utf-8')
                (folder/'addendum.tex').write_text('Mathematical result', encoding='utf-8')
                with self.assertRaisesRegex(ValueError, error):
                    project_text(folder)

    def test_standalone_input_graph(self):
        with TemporaryDirectory() as tmp:
            folder = Path(tmp)
            (folder/'main.tex').write_text(r'\input{addendum}', encoding='utf-8')
            (folder/'addendum.tex').write_text('Mathematical result', encoding='utf-8')
            self.assertIn('Mathematical result', project_text(folder))
            for directive, error in ((r'\input{../external}', 'outside standalone project'),
                                     (r'\input{main}', 'Repeated or cyclic')):
                with self.subTest(directive=directive):
                    (folder/'main.tex').write_text(directive, encoding='utf-8')
                    with self.assertRaisesRegex(ValueError, error):
                        project_text(folder)

    def test_line_break_is_not_display_math(self):
        source = "Row\\\\[4pt] see (B).\n\\[x\\tag{B}\\]"
        self.assertEqual(prefix_equation_tags(source, "C."),
                         "Row\\\\[4pt] see (C.B).\n\\[x\\tag{C.B}\\]")

    def test_alignat_and_eqnarray_arguments_are_math(self):
        for env in ("alignat*", "flalign", "eqnarray"):
            source = f"See (B).\n\\begin{{{env}}}x (B)\\tag{{B}}\\end{{{env}}}"
            expected = f"See (C.B).\n\\begin{{{env}}}x (B)\\tag{{C.B}}\\end{{{env}}}"
            with self.subTest(env=env):
                self.assertEqual(prefix_equation_tags(source, "C."), expected)

    def test_between_searches_for_end_after_start(self):
        self.assertEqual(between("end start body end", "start", "end"), "start body ")

    def test_equation_references_do_not_change_function_arguments(self):
        source = r"""Use (B), (D), and (2).
$R_{\mu,\rho}(B)$ and $\operatorname{Ber}(q(D))$ and $f (2)$.
\[q(D) + R_{\mu,\rho}(B)\tag{B}\]
\(q(D)\) and $$f(2)\tag{D}$$.
\begin{align*}f(2)&=q(D)\tag{2}\end{align*}
Then (B) and (D) apply."""
        expected = r"""Use (C.B), (C.D), and (C.2).
$R_{\mu,\rho}(B)$ and $\operatorname{Ber}(q(D))$ and $f (2)$.
\[q(D) + R_{\mu,\rho}(B)\tag{C.B}\]
\(q(D)\) and $$f(2)\tag{C.D}$$.
\begin{align*}f(2)&=q(D)\tag{C.2}\end{align*}
Then (C.B) and (C.D) apply."""
        self.assertEqual(prefix_equation_tags(source, "C."), expected)

    def test_untagged_source_is_unchanged(self):
        source = r"$f(B)$ and (B), with no equation tag."
        self.assertEqual(prefix_equation_tags(source, "C."), source)

    def test_real_critical_experiment_keeps_gap_and_budget_arguments(self):
        critical = assemble()["appendix-critical.tex"]
        self.assertIn(r"\operatorname{Ber}(q(D))", critical)
        self.assertIn(r"U_1\le q(D)", critical)
        self.assertIn(r"R_{\mu,\rho}(B)=\inf", critical)
        self.assertIn(r"\min\{\rho,\mu(E)\}", critical)
        self.assertIn(r"property (C.B)", critical)
        self.assertIn(r"\tag{C.D}", critical)
        self.assertNotIn("q(C.D)", critical)
        self.assertNotIn(r"R_{\mu,\rho}(C.B)", critical)
        self.assertNotIn(r"\mu(C.E)", critical)


if __name__ == "__main__":
    unittest.main()
