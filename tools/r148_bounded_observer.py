#!/usr/bin/env python3
"""Bounded one-shot supervisor for the R148 source-history observer.

This is research tooling, not a general process runner. It fixes the command,
working tree, output caps and wall deadline so the contract can pin its bytes.
"""

from __future__ import annotations

import os
import selectors
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE_DIR = Path("/tmp/yulang-r148-4c9d549")
MAX_CAPTURE = 64 * 1024
TERM_AFTER = 115.0
KILL_AFTER = 120.0
COMMAND = [
    "cargo", "test", "-p", "yu-solver", "--features",
    "shadow-apply-candidate", "observe_nested_recursion_raw_bound_history",
    "--", "--nocapture",
]


def main() -> int:
    if len(sys.argv) != 1:
        print("R148 supervisor accepts no arguments", file=sys.stderr)
        return 64
    if not hasattr(os, "sched_setaffinity"):
        print("CPU affinity enforcement unavailable", file=sys.stderr)
        return 69
    CAPTURE_DIR.mkdir(mode=0o700, parents=True, exist_ok=False)
    os.sched_setaffinity(0, {0})
    out_path = CAPTURE_DIR / "stdout.txt"
    err_path = CAPTURE_DIR / "stderr.txt"
    out_file = out_path.open("xb")
    err_file = err_path.open("xb")
    child = subprocess.Popen(
        COMMAND,
        cwd=ROOT,
        env={**os.environ, "CARGO_BUILD_JOBS": "1"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
        bufsize=0,
    )
    selector = selectors.DefaultSelector()
    assert child.stdout is not None and child.stderr is not None
    selector.register(child.stdout, selectors.EVENT_READ, (out_file, "stdout"))
    selector.register(child.stderr, selectors.EVENT_READ, (err_file, "stderr"))
    kept = {"stdout": 0, "stderr": 0}
    overflow = set()
    started = time.monotonic()
    term_sent = False
    kill_sent = False
    term_at = None
    while selector.get_map() or child.poll() is None:
        elapsed = time.monotonic() - started
        if elapsed >= TERM_AFTER and not term_sent:
            term_at = time.monotonic()
            term_sent = True
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        if elapsed >= KILL_AFTER and not kill_sent:
            kill_sent = True
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for key, _ in selector.select(timeout=0.05):
            block = os.read(key.fd, 8192)
            file, name = key.data
            if not block:
                selector.unregister(key.fileobj)
                key.fileobj.close()
                continue
            available = MAX_CAPTURE - kept[name]
            if available > 0:
                written = block[:available]
                file.write(written)
                kept[name] += len(written)
            if len(block) > available:
                overflow.add(name)
    child.wait()
    out_file.flush()
    err_file.flush()
    out_file.close()
    err_file.close()
    elapsed = time.monotonic() - started
    print(f"R148_EXIT_STATUS={child.returncode}")
    print(f"R148_ELAPSED_SECONDS={elapsed:.3f}")
    print(f"R148_TERM_SENT={int(term_sent)}")
    print(f"R148_KILL_SENT={int(kill_sent)}")
    print(f"R148_CAPTURE_OVERFLOW={','.join(sorted(overflow)) or 'none'}")
    print(f"R148_CAPTURE_DIR={CAPTURE_DIR}")
    if term_at is not None:
        print(f"R148_TERM_ELAPSED_SECONDS={term_at - started:.3f}")
    return 0 if child.returncode == 0 and not overflow and not term_sent else 1


if __name__ == "__main__":
    raise SystemExit(main())
