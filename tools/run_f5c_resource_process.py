#!/usr/bin/env python3
"""Run one F5c resource command with bounded memory, disk, and wall time."""

import argparse
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import time

GIB = 1024 ** 3
FLOOR = 8 * GIB
SAMPLE_SECONDS = 1.0
TERM_GRACE_SECONDS = 10.0
PAGE_BYTES = os.sysconf("SC_PAGE_SIZE")


def mem_available():
    with open("/proc/meminfo", encoding="ascii") as source:
        for line in source:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) * 1024
    raise RuntimeError("/proc/meminfo has no MemAvailable")


def file_bytes(path):
    try:
        return path.stat().st_size
    except FileNotFoundError:
        return 0


def disk_free(paths):
    return min(os.statvfs(path.parent).f_bavail * os.statvfs(path.parent).f_frsize
               for path in paths)


def group_processes(pgid):
    """Return live group PIDs and their RSS, including surviving descendants."""
    live = []
    rss = 0
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            stat = (entry / "stat").read_text(encoding="ascii")
            fields = stat[stat.rfind(")") + 2:].split()
            if int(fields[2]) != pgid or fields[0] in ("Z", "X"):
                continue
            live.append(int(entry.name))
            rss += int((entry / "statm").read_text(encoding="ascii").split()[1]) * PAGE_BYTES
        except (FileNotFoundError, ProcessLookupError, PermissionError, ValueError, IndexError):
            continue
    return live, rss


def signal_group(pgid, sig):
    if group_processes(pgid)[0]:
        try:
            os.killpg(pgid, sig)
        except ProcessLookupError:
            pass


def sample(pgid, sidecar, log, monitor, summary):
    available = mem_available()
    members, rss = group_processes(pgid) if pgid is not None else ([], 0)
    sidecar_size = file_bytes(sidecar)
    log_size = file_bytes(log)
    free = disk_free((sidecar, log, monitor, summary))
    return available, members, rss, sidecar_size, log_size, free


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=float, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--monitor", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--sidecar", type=Path, required=True)
    parser.add_argument("--existing-sidecar", action="store_true",
                        help="reuse a regular sidecar for read-only offline replay")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or args.timeout_seconds <= 0:
        parser.error("a positive timeout and a command after -- are required")
    paths = (args.log, args.monitor, args.summary, args.sidecar)
    if len({path.resolve() for path in paths}) != len(paths):
        parser.error("log, monitor, summary, and sidecar paths must differ")
    if args.existing_sidecar:
        try:
            if not stat.S_ISREG(args.sidecar.stat().st_mode):
                parser.error("existing sidecar must be a regular file")
        except FileNotFoundError:
            parser.error("existing sidecar must be a regular file")
    elif os.path.lexists(args.sidecar):
        parser.error("new sidecar path must be unused")
    if any(os.path.lexists(path) for path in (args.log, args.monitor, args.summary)):
        parser.error("per-run log, monitor, and summary paths must be unused")
    for path in paths:
        if not path.parent.is_dir():
            parser.error(f"parent directory does not exist: {path.parent}")

    interrupted = None

    def on_signal(signum, _frame):
        nonlocal interrupted
        interrupted = signal.Signals(signum).name

    signal.signal(signal.SIGINT, on_signal)
    signal.signal(signal.SIGTERM, on_signal)
    start = time.monotonic()
    process = None
    reason = None
    status = None
    minimum_available = None
    maximum_rss = maximum_sidecar = maximum_log = 0
    minimum_free = None
    samples = 0

    def record(monitor, pgid):
        nonlocal minimum_available, maximum_rss, maximum_sidecar, maximum_log
        nonlocal minimum_free, samples
        available, members, rss, sidecar_size, log_size, free = sample(
            pgid, args.sidecar, args.log, args.monitor, args.summary)
        minimum_available = available if minimum_available is None else min(minimum_available, available)
        maximum_rss = max(maximum_rss, rss)
        maximum_sidecar = max(maximum_sidecar, sidecar_size)
        maximum_log = max(maximum_log, log_size)
        minimum_free = free if minimum_free is None else min(minimum_free, free)
        samples += 1
        monitor.write(json.dumps({"elapsed_seconds": time.monotonic() - start,
            "mem_available_bytes": available, "group_pids": members,
            "group_rss_bytes": rss, "sidecar_bytes": sidecar_size,
            "log_bytes": log_size, "disk_free_bytes": free}) + "\n")
        monitor.flush()
        if available < FLOOR:
            return members, "MemAvailable below 8 GiB"
        if free < max(FLOOR, 2 * (sidecar_size + log_size)):
            return members, "disk free below resource floor"
        return members, None

    try:
        with args.monitor.open("x", encoding="utf-8") as monitor:
            # Apply the same floors before launching the command.
            _, reason = record(monitor, None)
            if reason is None and interrupted is not None:
                reason = interrupted
            if reason is None:
                environment = os.environ.copy()
                environment["F5C_RESOURCE_SIDECAR"] = str(args.sidecar.absolute())
                environment["RUSTC_WRAPPER"] = ""
                with args.log.open("xb") as output:
                    process = subprocess.Popen(command, stdin=subprocess.DEVNULL,
                        stdout=output, stderr=subprocess.STDOUT, env=environment,
                        start_new_session=True)
                    pgid = process.pid
                    while True:
                        members, breach = record(monitor, pgid)
                        status = process.poll()
                        if interrupted is not None:
                            reason = interrupted
                        elif breach is not None:
                            reason = breach
                        elif time.monotonic() - start >= args.timeout_seconds:
                            reason = "wall timeout"
                        elif status is not None and status != 0:
                            reason = "command failed"
                        elif status == 0 and not members:
                            reason = "completed"
                        if reason is not None:
                            break
                        time.sleep(SAMPLE_SECONDS)
                    if reason != "completed":
                        signal_group(pgid, signal.SIGTERM)
                        deadline = time.monotonic() + TERM_GRACE_SECONDS
                        while time.monotonic() < deadline:
                            members, _ = record(monitor, pgid)
                            if not members:
                                break
                            time.sleep(min(SAMPLE_SECONDS, max(0, deadline - time.monotonic())))
                        signal_group(pgid, signal.SIGKILL)
                        record(monitor, pgid)
                    status = process.wait() if status is None else status
    except (OSError, RuntimeError) as error:
        reason = f"supervisor error: {error}"
        if process is not None:
            signal_group(process.pid, signal.SIGTERM)
            time.sleep(TERM_GRACE_SECONDS)
            signal_group(process.pid, signal.SIGKILL)
            status = process.wait()
    finally:
        summary = {"reason": reason, "command_status": status,
            "elapsed_seconds": time.monotonic() - start,
            "min_mem_available_bytes": minimum_available,
            "peak_group_rss_bytes": maximum_rss,
            "peak_sidecar_bytes": maximum_sidecar,
            "peak_log_bytes": maximum_log,
            "min_disk_free_bytes": minimum_free, "samples": samples,
            "command": command}
        args.summary.write_text(json.dumps(summary, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(summary, sort_keys=True), file=sys.stderr)
    return 0 if reason == "completed" else 1


if __name__ == "__main__":
    sys.exit(main())
