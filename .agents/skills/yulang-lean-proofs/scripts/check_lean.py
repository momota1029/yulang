#!/usr/bin/env python3
"""Bounded checks for named Lean theorems, not proof review or a security sandbox.

Names deliberately support ASCII dotted identifiers only. This ordinary-mistake
check trusts the installed Lean/Lake and imported metaprograms. It does not defend
against malicious meta-code, prove source correspondence, or close parent gates.
Run against a provisioned project: its lakefile, manifest, and dependencies are
trusted inputs. This helper is not an offline execution sandbox.
"""

import argparse
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_PROJECT = Path(__file__).resolve().parents[4] / "notes/theory/lean"


class CheckFailure(Exception):
    pass


def identifier(value):
    if not IDENTIFIER.fullmatch(value):
        raise argparse.ArgumentTypeError("expected an ASCII dotted Lean identifier")
    return value


def positive_seconds(value):
    result = float(value)
    if not math.isfinite(result) or result <= 0:
        raise argparse.ArgumentTypeError("timeout must be finite and positive")
    return result


class Runner:
    def __init__(self, project, timeout):
        self.project = project
        self.deadline = time.monotonic() + timeout
        self.env = dict(os.environ, LEAN_NUM_THREADS="1")

    def run(self, command):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise CheckFailure("total wall timeout expired before next command")
        print(f"cwd: {self.project}\n$ {shlex.join(command)}", flush=True)
        try:
            process = subprocess.Popen(
                command, cwd=self.project, env=self.env, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, errors="replace",
                start_new_session=(os.name == "posix"),
            )
        except OSError as exc:
            raise CheckFailure(f"could not execute {command[0]}: {exc}") from exc
        problem = None
        try:
            output, _ = process.communicate(timeout=max(0, self.deadline - time.monotonic()))
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as exc:
            problem = exc
            # Kill the whole Lake/Lean process group, including descendants.
            try:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
            except ProcessLookupError:
                pass
            output, _ = process.communicate()
        sys.stdout.write(output)
        if output and not output.endswith("\n"):
            print()
        print(f"[exit {process.returncode}]", flush=True)
        if isinstance(problem, KeyboardInterrupt):
            raise problem
        if problem is not None:
            raise CheckFailure("total wall timeout expired; subprocess group terminated")
        if process.returncode:
            raise CheckFailure(f"command failed with exit {process.returncode}")
        return output


def elan_proxy(path):
    resolved = path.resolve()
    if resolved.name in {"elan", "elan.exe"}:
        return resolved
    sibling = path.with_name("elan.exe" if os.name == "nt" else "elan")
    return sibling if sibling.exists() and path.samefile(sibling) else None


def installed_lake(value, runner):
    path = shutil.which(value)
    if path is None:
        raise CheckFailure(f"Lake unavailable: {value}; install separately, then retry")
    path = Path(path).absolute()
    # `elan which` is a read-only lookup and fails for an uninstalled toolchain.
    # Never execute the Lake proxy itself, which could trigger an installation.
    proxy = elan_proxy(path)
    if proxy is not None:
        path = Path(runner.run([str(proxy), "which", "lake"]).strip())
        if not path.is_absolute() or not path.is_file() or not os.access(path, os.X_OK):
            raise CheckFailure("elan which lake did not return an installed executable")
        if elan_proxy(path) is not None:
            raise CheckFailure("elan which lake returned another proxy, not native Lake")
    return str(path)


def check_version(output, expected, tool):
    versions = re.findall(r"\bLean \(version ([^,\s)]+)|\bLean version ([^,\s)]+)", output)
    found = [first or second for first, second in versions]
    if found != [expected]:
        raise CheckFailure(f"{tool} must report Lean {expected}; found {found or 'no version'}")


def audit_source(modules, theorems):
    lines = ["import Lean.Elab.Command", "import Lean.Util.CollectAxioms",
             *(f"import {module}" for module in modules),
             "set_option pp.fullNames true", "set_option pp.universes false"]
    for name in theorems:
        lines.extend([
            "run_cmd do",
            f"  match (← Lean.getEnv).find? `{name} with",
            "  | some (.thmInfo _) => pure ()",
            f'  | _ => throwError "{name} is not a theorem declaration"',
            f'  Lean.logInfo "YULANG_AUDIT_BEGIN {name}"',
            f"#check @{name}",
            f"#print axioms {name}",
            "run_cmd do",
            f"  let axioms ← Lean.collectAxioms `{name}",
            "  for ax in axioms do",
            "    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do",
            '      throwError "unapproved axiom: {ax}"',
            f'  Lean.logInfo "YULANG_AUDIT_END {name}"',
        ])
    return "\n".join(lines) + "\n"


def validate_audit(output, theorems):
    # Require complete, ordered, unique evidence for every requested declaration.
    markers = re.findall(r"^YULANG_AUDIT_(BEGIN|END) (.+)$", output, re.MULTILINE)
    expected = [(kind, name) for name in theorems for kind in ("BEGIN", "END")]
    if markers != expected:
        raise CheckFailure("absent, duplicated, truncated, or reordered theorem audit")
    for name in theorems:
        body = output.split(f"YULANG_AUDIT_BEGIN {name}\n", 1)[1].split(
            f"YULANG_AUDIT_END {name}", 1)[0]
        signature = rf"(?m)^@?{re.escape(name)}(?:\.\{{|\s|:)"
        if not re.search(signature, body):
            raise CheckFailure(f"missing printed theorem type: {name}")
        pattern = (rf"'{re.escape(name)}' (?:does not depend on any axioms|"
                   r"depends on axioms:\s*\[([^\[\]]*)\])")
        matches = list(re.finditer(pattern, body))
        if len(matches) != 1:
            raise CheckFailure(f"missing or incomplete axiom report: {name}")
        raw = matches[0].group(1)
        axioms = set() if raw is None or not raw.strip() else {
            item.strip() for item in raw.split(",")
        }
        if axioms - ALLOWED_AXIOMS:
            raise CheckFailure(f"unapproved axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=DEFAULT_PROJECT)
    parser.add_argument("--lake", default="lake", help="Lake executable; installed Elan toolchains supported")
    parser.add_argument("--module", action="append", type=identifier, required=True)
    parser.add_argument("--theorem", action="append", type=identifier, required=True)
    parser.add_argument("--full", action="store_true", help="also build the project's default targets")
    parser.add_argument("--timeout", type=positive_seconds, default=120.0,
                        help="total wall seconds across all commands (default: 120)")
    args = parser.parse_args(argv)
    project = args.project.resolve()
    runner = Runner(project, args.timeout)
    def interrupted(_signum, _frame):
        raise KeyboardInterrupt()

    old_handler = signal.signal(signal.SIGTERM, interrupted)
    try:
        pin = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
        match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", pin)
        if match is None:
            raise CheckFailure("lean-toolchain must pin an exact stable leanprover/lean4:vX.Y.Z")
        if not any((project / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
            raise CheckFailure("project has no lakefile.toml or lakefile.lean")
        if not (project / "lake-manifest.json").is_file():
            raise CheckFailure("existing lake-manifest.json required; helper never generates manifests")
        lake = installed_lake(args.lake, runner)
        check_version(runner.run([lake, "--version"]), match[1], "Lake")
        # Disable build-cache downloads; use the project's trusted manifest.
        command = [lake, "--no-cache"]
        check_version(runner.run(command + ["env", "lean", "--version"]), match[1], "Lean")
        modules = list(dict.fromkeys(args.module))
        theorems = list(dict.fromkeys(args.theorem))
        runner.run(command + ["build", *("+" + module for module in modules)])
        if args.full:
            runner.run(command + ["build"])
        with tempfile.TemporaryDirectory(prefix="yulang-lean-audit-") as scratch:
            source = Path(scratch) / "YulangProofAudit.lean"
            source.write_text(audit_source(modules, theorems), encoding="utf-8")
            output = runner.run(command + ["env", "lean", "-j1", "-M1024",
                                            f"--root={scratch}", str(source)])
        validate_audit(output, theorems)
        for name in theorems:
            print(f"PASS: {name}, under its printed hypotheses; axiom whitelist satisfied.")
        print("Named declarations only; ordinary-mistake check, not independent review or source correspondence.")
        return 0
    except (CheckFailure, OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("FAIL: interrupted; active subprocess group terminated", file=sys.stderr)
        return 130
    finally:
        signal.signal(signal.SIGTERM, old_handler)


if __name__ == "__main__":
    sys.exit(main())
