"""Focused helper tests; no Lean installation or project build is performed."""

import contextlib
import importlib.util
import io
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock


SCRIPT = (Path(__file__).resolve().parents[1] /
          ".agents/skills/yulang-lean-proofs/scripts/check_lean.py")
SPEC = importlib.util.spec_from_file_location("check_lean", SCRIPT)
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)


def evidence(name, axioms=None):
    report = ("does not depend on any axioms" if axioms is None else
              "depends on axioms: [" + ", ".join(axioms) + "]")
    return (f"YULANG_AUDIT_BEGIN {name}\n"
            f"{name}.{{u}} {{a : Sort u}} : a → a\n"
            f"'{name}' {report}\nYULANG_AUDIT_END {name}\n")


class AuditTests(unittest.TestCase):
    def test_complete_multiple_declarations_and_standard_axioms(self):
        check.validate_audit(evidence("Foo.first") + evidence(
            "Foo.second", ["propext", "Classical.choice", "Quot.sound"]),
            ["Foo.first", "Foo.second"])

    def test_missing_truncated_duplicate_and_reordered_evidence(self):
        complete = evidence("Foo.first") + evidence("Foo.second")
        invalid = ["", evidence("Foo.first"), complete[:-8],
                   complete + evidence("Foo.second"),
                   evidence("Foo.second") + evidence("Foo.first"),
                   complete.replace("Foo.second.{u} {a : Sort u} : a → a\n", ""),
                   complete.replace("'Foo.second' does not depend on any axioms", "")]
        for output in invalid:
            with self.subTest(output=output), self.assertRaises(check.CheckFailure):
                check.validate_audit(output, ["Foo.first", "Foo.second"])

    def test_sorry_project_and_native_axioms_rejected(self):
        for axiom in ["sorryAx", "Foo.assumedBridge", "Lean.ofReduceBool"]:
            with self.subTest(axiom=axiom), self.assertRaises(check.CheckFailure):
                check.validate_audit(evidence("Foo.first", [axiom]), ["Foo.first"])

    def test_truncated_axiom_list_rejected(self):
        with self.assertRaises(check.CheckFailure):
            check.validate_audit(evidence("Foo.first", ["propext"]).replace(
                "[propext]", "[propext"), ["Foo.first"])

    def test_version_is_required_and_exact(self):
        for output in ["", "Lake version 5.0.0", "Lean (version 4.34.0, release)",
                       "Lean (version 4.35.0-rc1, release)"]:
            with self.subTest(output=output), self.assertRaises(check.CheckFailure):
                check.check_version(output, "4.35.0", "test")
        check.check_version("Lake version 5.0.0 (Lean version 4.35.0)", "4.35.0", "Lake")
        check.check_version("Lean (version 4.35.0, release)", "4.35.0", "Lean")

    def test_names_do_not_allow_code_injection(self):
        for name in ["Foo\naxiom bad : False", "Foo;bar", "Foo..bar", "Foo.日本語"]:
            with self.subTest(name=name), self.assertRaises(Exception):
                check.identifier(name)
        self.assertEqual(check.identifier("Foo.bar_2'"), "Foo.bar_2'")


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix="yulang-lean-helper-tests-", dir="/tmp")
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.temp_patch = mock.patch.object(tempfile, "tempdir", str(self.root))
        self.temp_patch.start()
        self.addCleanup(self.temp_patch.stop)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        (self.root / "lakefile.toml").write_text('name = "Foo"\n')
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.args = ["--project", str(self.root), "--lake", sys.executable,
                     "--module", "Foo", "--theorem", "Foo.first"]
        self.output = io.StringIO()

    def invoke(self, responses, extra=()):
        with mock.patch.object(check.Runner, "run", side_effect=responses) as run, \
                contextlib.redirect_stdout(self.output), contextlib.redirect_stderr(self.output):
            status = check.main(self.args + list(extra))
        return status, run

    def versions(self):
        return ["Lake version 5.0.0 (Lean version 4.35.0)",
                "Lean (version 4.35.0, release)"]

    def test_selected_modules_precede_optional_default_build_and_audit(self):
        status, run = self.invoke(self.versions() + ["built", "built", evidence("Foo.first")], ["--full"])
        self.assertEqual(status, 0)
        commands = [call.args[0] for call in run.call_args_list]
        self.assertEqual(commands[2][-2:], ["build", "+Foo"])
        self.assertEqual(commands[3][-1:], ["build"])
        self.assertIn("-j1", commands[4])
        self.assertIn("-M1024", commands[4])
        self.assertEqual(Path(commands[4][-1]).name, "YulangProofAudit.lean")
        self.assertFalse(Path(commands[4][-1]).exists())
        self.assertIn("PASS: Foo.first, under its printed hypotheses", self.output.getvalue())

    def test_build_failure_stops_before_audit_or_pass(self):
        status, run = self.invoke(self.versions() + [check.CheckFailure("build failed")])
        self.assertEqual(status, 1)
        self.assertEqual(run.call_count, 3)
        self.assertNotIn("PASS:", self.output.getvalue())

    def test_missing_or_mismatched_version_stops_before_build(self):
        for version in ["", "Lean (version 4.34.0, release)"]:
            with self.subTest(version=version):
                status, run = self.invoke([self.versions()[0], version])
                self.assertEqual(status, 1)
                self.assertEqual(run.call_count, 2)

    def test_successful_process_without_audit_cannot_pass(self):
        status, _ = self.invoke(self.versions() + ["built", ""])
        self.assertEqual(status, 1)
        self.assertNotIn("PASS:", self.output.getvalue())

    def test_missing_manifest_stops_without_launching_lake(self):
        (self.root / "lake-manifest.json").unlink()
        status, run = self.invoke([])
        self.assertEqual(status, 1)
        run.assert_not_called()

    def make_elan_proxy(self):
        elan = self.root / "elan"
        elan.touch(mode=0o755)
        proxy = self.root / "lake"
        proxy.symlink_to(elan)
        return elan, proxy

    def test_elan_resolves_installed_native_lake_without_running_proxy(self):
        elan, proxy = self.make_elan_proxy()
        native = self.root / "toolchain-lake"
        native.touch(mode=0o755)
        runner = mock.Mock()
        runner.run.return_value = str(native) + "\n"
        self.assertEqual(check.installed_lake(str(proxy), runner), str(native))
        runner.run.assert_called_once_with([str(elan), "which", "lake"])

    def test_missing_elan_toolchain_fails_without_proxy_fallback(self):
        elan, proxy = self.make_elan_proxy()
        runner = mock.Mock()
        runner.run.side_effect = check.CheckFailure("toolchain is not installed")
        with self.assertRaises(check.CheckFailure):
            check.installed_lake(str(proxy), runner)
        runner.run.assert_called_once_with([str(elan), "which", "lake"])

    def test_runner_logs_failure_and_enforces_shared_deadline(self):
        runner = check.Runner(self.root, 3)
        with contextlib.redirect_stdout(self.output), self.assertRaises(check.CheckFailure):
            runner.run([sys.executable, "-c", "print('failure detail'); raise SystemExit(7)"])
        self.assertIn("failure detail", self.output.getvalue())
        self.assertIn("[exit 7]", self.output.getvalue())
        runner.deadline = time.monotonic() - 1
        with mock.patch.object(check.subprocess, "Popen") as popen, self.assertRaises(check.CheckFailure):
            runner.run([sys.executable, "-c", "pass"])
        popen.assert_not_called()

    @unittest.skipUnless(os.name == "posix", "process-group termination is POSIX-specific")
    def test_timeout_kills_descendants(self):
        marker = self.root / "child-survived"
        child = f"import time; from pathlib import Path; time.sleep(0.7); Path({str(marker)!r}).touch()"
        parent = ("import subprocess, sys, time; "
                  f"subprocess.Popen([sys.executable, '-c', {child!r}]); time.sleep(30)")
        with contextlib.redirect_stdout(self.output), self.assertRaises(check.CheckFailure):
            check.Runner(self.root, 0.2).run([sys.executable, "-c", parent])
        time.sleep(0.8)
        self.assertFalse(marker.exists(), "descendant outlived the helper timeout")
        self.assertIn("[exit -9]", self.output.getvalue())


if __name__ == "__main__":
    unittest.main()
