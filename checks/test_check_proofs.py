"""Regression checks for the source scan and Lean's project-wide axiom audit.

Run `python3 -m unittest discover -s checks -p 'test_*.py'`. The Lean cases
compile small isolated fixtures using the pinned toolchain; no project proof
source or compiled project module is changed.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import check_proofs


ROOT = Path(__file__).resolve().parents[1]


class SourceScanTests(unittest.TestCase):
    def test_unimported_library_module_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "QuantumBackflow").mkdir()
            (root / "QuantumBackflow" / "Hidden.lean").write_text(
                "theorem checked : True := True.intro\n")
            (root / "QuantumBackflow.lean").write_text("-- import QuantumBackflow.Hidden\n")
            self.assertEqual(check_proofs.check_library_imports(root),
                             ["Library module missing from aggregate: QuantumBackflow.Hidden"])
            (root / "QuantumBackflow.lean").write_text("import QuantumBackflow.Hidden\n")
            self.assertEqual(check_proofs.check_library_imports(root), [])

    def tokens(self, source: str) -> list[str]:
        return check_proofs.FORBIDDEN.findall(check_proofs.mask_noncode(source))

    def test_proof_placeholders_and_added_axioms(self):
        cases = {
            "example : False := by sorry": ["sorry"],
            "example : False := by admit": ["admit"],
            "example : False := sorryAx False true": ["sorryAx"],
            "example : False := «sorryAx» False true": ["sorryAx"],
            "axiom unproved : False": ["axiom"],
            "unsafe def unchecked : Nat := 0": ["unsafe"],
            "example : 1 = 1 := by native_decide": ["native_decide"],
            'def text := s!"{(by admit : Nat)}"': ["admit"],
        }
        for source, expected in cases.items():
            with self.subTest(source=source):
                self.assertEqual(self.tokens(source), expected)

    def test_comments_strings_and_ordinary_identifiers(self):
        source = '''-- sorry admit axiom
/- outer sorry /- nested admit -/ unsafe -/
def text := "sorry \\"axiom\\" admit"
def raw := r##"sorry "unsafe" admit"##
def letter := 's'
def «a sorry in a name» := 0
def sorryForTheName := 0
'''
        self.assertEqual(self.tokens(source), [])
        self.assertEqual(
            check_proofs.mask_noncode(source).count("\n"), source.count("\n")
        )

    def test_unterminated_noncode_fails_closed(self):
        for source in ['/- comment', '"string', 'r#"raw', '«identifier']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                check_proofs.mask_noncode(source)

    def test_dependency_caches_are_excluded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Proof.lean").write_text("example : True := by trivial\n")
            for excluded in [".lake", ".git"]:
                (root / excluded).mkdir()
                (root / excluded / "Ignored.lean").write_text("axiom ignored : False\n")
            self.assertEqual(check_proofs.scan_sources(root), (1, []))


class LeanAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lake = os.environ.get("LAKE", "lake")
        prefix = subprocess.check_output(
            [lake, "env", "lean", "--print-prefix"], cwd=ROOT, text=True
        ).strip()
        cls.lean = str(Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean"))
        # Ask Lake for its search path without depending on a POSIX printenv command.
        cls.lean_path = subprocess.check_output(
            [lake, "env", os.sys.executable, "-c", "import os; print(os.environ.get('LEAN_PATH', ''))"],
            cwd=ROOT,
            text=True,
        ).strip()
        source = (ROOT / "checks" / "Axioms.lean").read_text()
        # Reuse the actual audit commands, stopping before the named theorem list.
        cls.audit_commands = source.split("open Lean Elab Command\n", 1)[1].split(
            "\naudit_axioms QuantumBackflow.", 1
        )[0]

    def run_fixture(self, source: str) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = root / "QuantumBackflow" / "AuditFixture.lean"
            fixture.parent.mkdir()
            fixture.write_text(source)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(root) + os.pathsep + self.lean_path
            compiled = subprocess.run(
                [self.lean, "-o", str(fixture.with_suffix(".olean")), str(fixture)],
                cwd=root,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=60,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout)
            audit = root / "Audit.lean"
            audit.write_text(
                "import QuantumBackflow.AuditFixture\n"
                "import Lean.Util.CollectAxioms\n"
                "import Lean.Elab.Command\n"
                "open Lean Elab Command\n"
                + self.audit_commands
            )
            return subprocess.run(
                [self.lean, str(audit)],
                cwd=root,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=60,
            )

    def test_permitted_proofs_pass(self):
        result = self.run_fixture(
            "private theorem private_true : True := True.intro\n"
            "theorem OtherNamespace.checked : True := private_true\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Audited all", result.stdout)

    def test_untrusted_declarations_fail_regardless_of_name_or_visibility(self):
        cases = {
            "private admit": "private theorem hidden : False := by admit\n",
            "normal sorryAx": "theorem OtherNamespace.bad : False := sorryAx False true\n",
            "quoted sorryAx": "theorem OtherNamespace.bad : False := «sorryAx» False true\n",
            "unused axiom": "axiom OtherNamespace.unused : False\n",
        }
        for label, source in cases.items():
            with self.subTest(case=label):
                result = self.run_fixture(source)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Untrusted dependencies in project declarations", result.stdout)

    def test_unsafe_declaration_fails(self):
        result = self.run_fixture("unsafe def OtherNamespace.unchecked : Nat := 0\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Unsafe project declaration", result.stdout)


if __name__ == "__main__":
    unittest.main()
