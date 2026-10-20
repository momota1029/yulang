#!/usr/bin/env python3
"""Single-use bounded supervisor for the R148 source-history observer."""

from __future__ import annotations

import os
import selectors
import signal
import subprocess
import sys
import time
import hashlib
import ctypes
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE_DIR = ROOT / "target/r148-4c9d549-observer"
MAX_CAPTURE = 64 * 1024
MAX_CGROUP_MEMORY = 1024 * 1024 * 1024
TERM_AFTER = 109.0
KILL_AFTER = 114.0
TERM_GRACE = 5.0
RUN_LIMIT = 120.0
COMMAND = [
    "/usr/bin/bwrap", "--die-with-parent", "--unshare-net", "--unshare-pid", "--as-pid-1",
    "--ro-bind", "/", "/", "--proc", "/proc", "--dev", "/dev",
    "--ro-bind", "/dev/null", f"/run/user/{os.getuid()}/bus",
    "--ro-bind", "/dev/null", f"/run/user/{os.getuid()}/systemd/private",
    "--ro-bind", "/dev/null", "/run/dbus/system_bus_socket",
    "--ro-bind", "/sys/fs/cgroup", "/sys/fs/cgroup",
    "--bind", str(CAPTURE_DIR), str(CAPTURE_DIR),
    "--bind", str(CAPTURE_DIR / "tmp"), "/tmp",
    "--chdir", str(ROOT),
    "--setenv", "HOME", str(Path.home()),
    "--setenv", "CARGO_HOME", str(Path.home() / ".cargo"),
    "--setenv", "CARGO_TARGET_DIR", str(CAPTURE_DIR / "cargo-target"),
    "--setenv", "PATH", f"{Path.home() / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin'}:/usr/bin:/bin",
    "--setenv", "CARGO_BUILD_JOBS", "1",
    "--setenv", "CARGO_NET_OFFLINE", "true",
    "--setenv", "CARGO_INCREMENTAL", "0",
    "--setenv", "DBUS_SESSION_BUS_ADDRESS", "unix:path=/dev/null",
    "--setenv", "DBUS_SYSTEM_BUS_ADDRESS", "unix:path=/dev/null",
    "--", str(Path.home() / ".rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo"),
    "test", "--locked", "--offline", "-p", "yu-solver", "--features",
    "shadow-apply-candidate", "observe_nested_recursion_raw_bound_history",
    "--", "--nocapture",
]
TOOLCHAIN_BIN = Path.home() / ".rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin"
TOOL_PINS = {
    Path("/usr/bin/python3"): "e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f",
    Path("/usr/lib/x86_64-linux-gnu/libc.so.6"): "3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf",
    TOOLCHAIN_BIN / "cargo": "841072d1d92f9e841d9ba5b0814182a0adf064acf4527cd120967b7bc49dcb66",
    TOOLCHAIN_BIN / "rustc": "bff349e72704ff70bc08a234a3847338e797065bbedde5e556808bc87b7bf7c6",
    Path("/usr/bin/bwrap"): "e318903862396f96de3df57264e0158682b952fd3fb53ac23d876413e7b30f71",
    Path("/home/momota1029/.cargo/config.toml"): "ae913eabcfcdcd3c0c22c27c76397f859176c914eae0686b183d68d5b94776e9",
    Path("/usr/bin/clang"): "8ef402d453d1ba4902e4ee0f0f847f6cfa01400c95aa43c24e97818b9c0e3f45",
    Path("/usr/local/bin/mold"): "1ca3c22c01ccf168e026ce73add18b75cb7879f130a6cfa25a3cd1cf16e4cad7",
    Path("/usr/bin/timeout"): "12690a043dfd555a6c14ccc1564f5649c18f1762c0d6ff66729948130898ec52",
    Path("/usr/bin/systemd-run"): "de28cc5757d3789efa5f6fed5659893410469f68b42175d4531f5b34d3a09e16",
    Path("/usr/bin/systemctl"): "37ec607113f55f1b385b4fa75588a43402aec0de57927500763b267713f10f63",
    Path("/usr/lib/systemd/systemd"): "9a813714ffd4dadb692afe44384c9c5b334fa323a4ec1dd5157aebdcbbb0667a",
    ROOT / "apps/yulang-wasm/Cargo.toml": "c00101fa1b063622a9826a7971add7396e0f73b614d408f2e962a006799966f6",
    ROOT / "tools/bench-runner/Cargo.toml": "c266b7bb06e133d3f287386ff99fb52c510684023d0e080e09a8a12211bf16dc",
    ROOT / "tools/xtask/Cargo.toml": "cbfb0a52f3324dda81c90e1825f73a7aa9b6038f862c923f6e30bc5e562769b8",
}
LIBC = ctypes.CDLL(None, use_errno=True)

SPAWNING = False
PENDING_STOP: int | None = None
SERVICE_CGROUP: Path | None = None
SERVICE_UNIT = "r148-bounded-observer-20261020.service"
SERVICE_PROPERTIES: dict[str, str] = {}


class StopRequested(Exception):
    pass


def signal_stop(signum: int, _frame: object) -> None:
    global PENDING_STOP
    if SPAWNING:
        PENDING_STOP = signum
        return
    raise StopRequested(f"received signal {signum}")


def child_parent_death_guard(expected_parent: int) -> None:
    # Runs in Popen's fork child before exec. Arm parent-death cleanup, then
    # close the race where the parent died before prctl took effect.
    if LIBC.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
        os._exit(127)
    if os.getppid() != expected_parent:
        os.kill(os.getpid(), signal.SIGKILL)


def service_cgroup_path() -> Path:
    for line in Path("/proc/self/cgroup").read_text().splitlines():
        if line.startswith("0::/"):
            return Path("/sys/fs/cgroup") / line[3:].lstrip("/")
    raise RuntimeError("unified systemd service cgroup is unavailable")


def service_memory_bytes() -> int:
    if SERVICE_CGROUP is None:
        raise RuntimeError("service cgroup was not initialized")
    return int((SERVICE_CGROUP / "memory.current").read_text().strip())


def verify_service_properties() -> None:
    global SERVICE_PROPERTIES
    names = (
        "Type", "ExitType", "Restart", "KillMode", "KillSignal", "SendSIGKILL",
        "FinalKillSignal", "RuntimeMaxUSec", "TimeoutStartUSec", "TimeoutStartFailureMode",
        "TimeoutStopUSec", "TimeoutStopFailureMode", "Delegate", "MemoryAccounting",
        "StandardInput", "StandardOutput", "StandardError", "WorkingDirectory", "MainPID", "ControlGroup",
        "InvocationID",
    )
    proc = subprocess.run(
        ["/usr/bin/systemctl", "--user", "show", SERVICE_UNIT,
         "--property=" + ",".join(names), "--no-pager"],
        check=False, capture_output=True, text=True, timeout=1.0,
    )
    if proc.returncode != 0:
        raise RuntimeError("could not read effective transient service properties")
    SERVICE_PROPERTIES = dict(
        line.split("=", 1) for line in proc.stdout.splitlines() if "=" in line
    )
    expected = {
        "Type": "exec", "ExitType": "main", "Restart": "no", "KillMode": "control-group",
        "KillSignal": str(int(signal.SIGTERM)), "SendSIGKILL": "yes",
        "FinalKillSignal": str(int(signal.SIGKILL)),
        "TimeoutStartFailureMode": "kill", "TimeoutStopFailureMode": "kill", "Delegate": "no",
        "MemoryAccounting": "yes", "StandardInput": "null", "StandardOutput": "null",
        "StandardError": "null", "MainPID": str(os.getpid()),
        "WorkingDirectory": str(ROOT),
        "ControlGroup": str(SERVICE_CGROUP).removeprefix("/sys/fs/cgroup"),
        "InvocationID": os.environ.get("INVOCATION_ID", ""),
    }
    for key, value in expected.items():
        if SERVICE_PROPERTIES.get(key) != value:
            raise RuntimeError(f"effective systemd property mismatch: {key}")
    if SERVICE_PROPERTIES.get("RuntimeMaxUSec") not in {"109s", "1min 49s", "109000000"}:
        raise RuntimeError("effective RuntimeMaxSec does not equal 109 seconds")
    if SERVICE_PROPERTIES.get("TimeoutStartUSec") not in {"5s", "5000000"}:
        raise RuntimeError("effective TimeoutStartSec does not equal 5 seconds")
    if SERVICE_PROPERTIES.get("TimeoutStopUSec") not in {"5s", "5000000"}:
        raise RuntimeError("effective TimeoutStopSec does not equal 5 seconds")


def signal_group(pgid: int, sig: int) -> bool:
    try:
        os.killpg(pgid, sig)
        return True
    except ProcessLookupError:
        return False


def group_exists(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def remaining_wall(started: float | None) -> float:
    if started is None:
        return 0.0
    return max(0.0, RUN_LIMIT - (time.monotonic() - started))


def verify_toolchain() -> None:
    expected_python = Path("/usr/bin/python3").resolve()
    if Path(sys.executable).resolve() != expected_python:
        raise RuntimeError("Python interpreter does not match the pinned executable")
    for path, expected in TOOL_PINS.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"toolchain pin mismatch: {path}")
    mapped_libc = {
        Path(line.rsplit(None, 1)[-1]).resolve()
        for line in Path("/proc/self/maps").read_text().splitlines()
        if "libc.so.6" in line and line.rsplit(None, 1)[-1].startswith("/")
    }
    if Path("/usr/lib/x86_64-linux-gnu/libc.so.6").resolve() not in mapped_libc:
        raise RuntimeError("loaded libc does not match pinned input")


def main() -> int:
    global SPAWNING, SERVICE_CGROUP
    if len(sys.argv) != 1:
        print("R148 supervisor accepts no arguments", file=sys.stderr)
        return 64
    if not hasattr(os, "sched_setaffinity") or not Path("/proc/self/stat").exists():
        print("Linux affinity and process monitoring are required", file=sys.stderr)
        return 69
    if not os.environ.get("INVOCATION_ID"):
        print("R148 observer must run as a systemd service", file=sys.stderr)
        return 69
    try:
        SERVICE_CGROUP = service_cgroup_path()
        if os.environ.get("R148_UNIT_NAME") != SERVICE_UNIT or SERVICE_CGROUP.name != SERVICE_UNIT:
            raise RuntimeError("systemd unit identity does not match the frozen observer unit")
        if not (SERVICE_CGROUP / "memory.current").is_file():
            raise RuntimeError("systemd service memory accounting is unavailable")
        verify_service_properties()
    except (OSError, RuntimeError) as exc:
        print(f"R148 systemd cgroup preflight failed: {exc}", file=sys.stderr)
        return 69
    CAPTURE_DIR.mkdir(mode=0o700, parents=True, exist_ok=False)
    (CAPTURE_DIR / "tmp").mkdir(mode=0o700)
    out_file = (CAPTURE_DIR / "stdout.txt").open("xb")
    err_file = (CAPTURE_DIR / "stderr.txt").open("xb")
    old_handlers = {sig: signal.signal(sig, signal_stop) for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    child: subprocess.Popen[bytes] | None = None
    selector = selectors.DefaultSelector()
    overflow: set[str] = set()
    kept = {"stdout": 0, "stderr": 0}
    peak_rss = 0
    result = 1
    reason = "not-started"
    started: float | None = None
    term_sent = False
    kill_sent = False
    try:
        if sys.version_info < (3, 11):
            raise RuntimeError("Python 3.11 or newer is required")
        verify_toolchain()
        allowed_cpus = os.sched_getaffinity(0)
        if not allowed_cpus:
            raise RuntimeError("no allowed CPU is available")
        selected_cpu = min(allowed_cpus)
        os.sched_setaffinity(0, {selected_cpu})
        started = time.monotonic()
        SPAWNING = True
        expected_parent = os.getpid()
        child = subprocess.Popen(
            COMMAND,
            cwd=ROOT,
            env={"PATH": f"{TOOLCHAIN_BIN}:/usr/bin:/bin"},
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            process_group=0,
            bufsize=0,
            preexec_fn=lambda: child_parent_death_guard(expected_parent),
        )
        SPAWNING = False
        if PENDING_STOP is not None:
            raise StopRequested(f"received signal {PENDING_STOP} during spawn")
        assert child.stdout is not None and child.stderr is not None
        selector.register(child.stdout, selectors.EVENT_READ, (out_file, "stdout"))
        selector.register(child.stderr, selectors.EVENT_READ, (err_file, "stderr"))
        reason = "running"
        while selector.get_map() or child.poll() is None or group_exists(child.pid):
            elapsed = time.monotonic() - started
            peak_rss = max(peak_rss, service_memory_bytes())
            if peak_rss > MAX_CGROUP_MEMORY:
                reason = "aggregate-service-cgroup-memory-over-1gib"
                signal_group(child.pid, signal.SIGTERM)
                term_sent = True
                break
            if elapsed >= TERM_AFTER and not term_sent:
                reason = "wall-limit-term"
                term_sent = signal_group(child.pid, signal.SIGTERM)
            if elapsed >= KILL_AFTER and not kill_sent:
                reason = "wall-limit-kill"
                kill_sent = signal_group(child.pid, signal.SIGKILL)
                break
            if child.poll() is not None and group_exists(child.pid) and not term_sent:
                reason = "descendant-remained-after-cargo-exit"
                term_sent = signal_group(child.pid, signal.SIGTERM)
            for key, _ in selector.select(timeout=0.1):
                block = os.read(key.fd, 8192)
                file, name = key.data
                if not block:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                available = MAX_CAPTURE - kept[name]
                if available > 0:
                    retained = block[:available]
                    file.write(retained)
                    kept[name] += len(retained)
                if len(block) > available:
                    overflow.add(name)
        if child.poll() is None or group_exists(child.pid):
            reason = reason if reason != "running" else "supervisor-stop"
            if not term_sent:
                signal_group(child.pid, signal.SIGTERM)
                term_sent = True
            if not kill_sent:
                grace_end = min(time.monotonic() + TERM_GRACE,
                                time.monotonic() + remaining_wall(started))
                while group_exists(child.pid) and time.monotonic() < grace_end:
                    time.sleep(0.05)
                if group_exists(child.pid):
                    signal_group(child.pid, signal.SIGKILL)
                    kill_sent = True
        try:
            child.wait(timeout=remaining_wall(started))
        except subprocess.TimeoutExpired:
            reason = "direct-cargo-reap-unconfirmed"
            result = 1
        if group_exists(child.pid):
            reason = "process-group-cessation-unconfirmed"
        elif child.returncode == 0 and not overflow and not term_sent and reason == "running":
            reason = "completed"
            result = 0
        else:
            reason = reason if reason != "running" else "nonzero-or-truncated-output"
    except BaseException as exc:
        reason = f"supervisor-exception:{type(exc).__name__}"
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, signal.SIG_IGN)
        if child is not None:
            signal_group(child.pid, signal.SIGTERM)
            term_sent = True
            grace_end = min(time.monotonic() + TERM_GRACE,
                            time.monotonic() + remaining_wall(started))
            while group_exists(child.pid) and time.monotonic() < grace_end:
                time.sleep(0.05)
            if group_exists(child.pid):
                signal_group(child.pid, signal.SIGKILL)
                kill_sent = True
            try:
                child.wait(timeout=remaining_wall(started))
            except subprocess.TimeoutExpired:
                reason = "process-group-cessation-unconfirmed"
        if isinstance(exc, (KeyboardInterrupt, StopRequested)):
            result = 130
    finally:
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, signal.SIG_IGN)
        if child is not None and group_exists(child.pid):
            signal_group(child.pid, signal.SIGKILL)
            kill_sent = True
        if child is not None and child.poll() is None:
            try:
                child.wait(timeout=remaining_wall(started))
            except subprocess.TimeoutExpired:
                reason = "process-group-cessation-unconfirmed"
        if child is not None and group_exists(child.pid):
            reason = "process-group-cessation-unconfirmed"
        if child is not None:
            for stream in (child.stdout, child.stderr):
                if stream is not None and not stream.closed:
                    stream.close()
        for key in list(selector.get_map().values()):
            selector.unregister(key.fileobj)
            key.fileobj.close()
        selector.close()
        for file in (out_file, err_file):
            if not file.closed:
                file.flush()
                file.close()
        elapsed = time.monotonic() - started if started is not None else 0.0
        (CAPTURE_DIR / "supervisor.txt").write_text(
            f"reason={reason}\nexit_status={child.returncode if child else 'not-started'}\n"
            f"elapsed_seconds={elapsed:.3f}\npeak_service_cgroup_memory_bytes={peak_rss}\n"
            f"stdout_bytes={kept['stdout']}\nstderr_bytes={kept['stderr']}\n"
            f"overflow={','.join(sorted(overflow)) or 'none'}\n"
            f"term_sent={int(term_sent)}\nkill_sent={int(kill_sent)}\n"
            f"selected_cpu={selected_cpu if 'selected_cpu' in locals() else 'unavailable'}\n"
            f"cargo_sha256={TOOL_PINS[TOOLCHAIN_BIN / 'cargo']}\nrustc_sha256={TOOL_PINS[TOOLCHAIN_BIN / 'rustc']}\n"
            f"systemd_invocation_id={os.environ.get('INVOCATION_ID', 'unknown')}\n"
            f"systemd_cgroup={SERVICE_CGROUP if SERVICE_CGROUP else 'unknown'}\n"
            + "".join(f"systemd_{key}={value}\n" for key, value in sorted(SERVICE_PROPERTIES.items()))
            + f"process_group_gone={'unknown' if child is None and started is not None else int(child is None or not group_exists(child.pid))}\n"
        )
    return result


if __name__ == "__main__":
    raise SystemExit(main())
