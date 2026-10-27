"""Regression checks for mathematical fidelity during manuscript assembly."""
import unittest

from build_v5 import assemble, prefix_equation_tags


class ManuscriptAssemblyTests(unittest.TestCase):
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
