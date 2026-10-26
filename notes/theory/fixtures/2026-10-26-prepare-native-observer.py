#!/usr/bin/env python3
"""Prepare the exact observation-only solver in a new directory outside Git.

This does not build, execute inference, or modify the repository. The patch
logs events and has an explicit observation cutoff; it is not a solver fix.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    destination = args.destination.resolve()
    if destination == repo or repo in destination.parents:
        parser.error("choose a new destination outside the repository")
    if destination.exists():
        parser.error("destination already exists; choose a new directory")
    if shutil.which("patch") is None:
        parser.error("the patch utility is required")

    def git(*argv):
        return subprocess.check_output(["git", *argv], cwd=repo)

    native_paths = ["crates", "Cargo.toml", "Cargo.lock",
                    "tools/inference-playground/src/pinned_stdlib.rs",
                    "tools/inference-playground/pinned_stdlib.bin"]
    if git("diff", "--name-only", "HEAD", "--", *native_paths).strip():
        parser.error("native inputs differ from HEAD; use a clean source checkout")

    expected = {
        "candidate_context.rs": "57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e",
        "candidate_extrusion.rs": "80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61",
        "candidate_intrusion.rs": "475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97",
        "lib.rs": "ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07",
    }
    for name, digest in expected.items():
        data = git("show", "HEAD:crates/yu-solver/src/" + name)
        if hashlib.sha256(data).hexdigest() != digest:
            parser.error("snapshot differs at " + name)

    source = destination / "source"
    source.mkdir(parents=True)
    paths = git("ls-files", "-z", "--", "crates/yu-solver").split(b"\0")
    for raw in paths:
        if not raw:
            continue
        relative = raw.decode()
        target = source / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git("show", "HEAD:" + relative))
    patch = Path(__file__).with_name("2026-10-26-native-observer.patch")
    subprocess.run(["patch", "-p1", "--batch", "--forward", "-i", str(patch)],
                   cwd=source, check=True)

    solver = source / "crates/yu-solver"
    manifest = solver / "Cargo.toml"
    content = manifest.read_text()
    for name in ("yu-hir", "yu-syntax", "yu-types", "yu-core"):
        content = content.replace('path = "../' + name + '"',
                                  "path = " + json.dumps(str(repo / "crates" / name)))
    manifest.write_text(content)

    manifest_text = '\n'.join([
        '[package]', 'name = "yulang-finite-prefix-observer"',
        'version = "0.1.0"', 'edition = "2024"', '[workspace]',
        '[[bin]]', 'name = "yulang-finite-prefix-observer"',
        'path = ' + json.dumps(str(Path(__file__).with_name("2026-10-26-native-observer.rs"))),
        '[dependencies]',
        'yu-hir = { path = ' + json.dumps(str(repo / "crates/yu-hir")) + ', features = ["shadow"] }',
        'yu-solver = { path = ' + json.dumps(str(solver)) + ', features = ["shadow-apply-candidate"] }',
        'yu-syntax = { path = ' + json.dumps(str(repo / "crates/yu-syntax")) + ' }',
        '',
    ])
    (destination / "Cargo.toml").write_text(manifest_text)
    (destination / "Cargo.lock").write_bytes(git("show", "HEAD:Cargo.lock"))
    receipt = {
        "source_commit": git("rev-parse", "HEAD").decode().strip(),
        "original_solver_hashes": expected,
        "patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
        "patched_solver_hashes": {
            name: hashlib.sha256((solver / "src" / name).read_bytes()).hexdigest()
            for name in expected
        },
        "manifest": str(destination / "Cargo.toml"),
    }
    (destination / "preparation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
