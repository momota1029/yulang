# R171 implementation handoff — invocation revision 2

Assignment: `formal-name-forwarding-instance-20261021-r171`, contract revision 1, SHA-256 `2491bcdc3dc7b09f8aeb06754ebe635b1dae4b8c1e8cef5f526c7517ea667241`.
Status: **pre-probe candidate, exact invocation frozen for independent review; probe NOT RUN**.
This sequential handoff revision supersedes candidate revision 1, SHA-256 `1c02ca97381b158d45df2e4d4f66f3ffc1fef31395f6f2958d2da26910414fee` (preserved in Git history). Luna owns implementation and all Git operations.

## Review-ready exact inputs

- Source fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`: `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
- Harness `tools/inference-playground/examples/r171_provider_incidence.rs`: `b8d9afd91154c7b0df1d1192ad1567a0e25fac7ef4ff4b698d989acd1c205e75`.
- Reused observer owners: `candidate_scheme.rs` `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225`; `shadow_apply.rs` `46959cf65e447f4c1dc3db34f1969cfa5746e8d7b86227b1b8b456ac2701ddbb`; R170 observer example `d6392dde7fc2aedd4e5c860e75f89df0217bb621598558bf99817d9cc1d5d3a4`.
- Proof membership result `notes/theory/2026-10-21-r171-forwarding-instance.md` `d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b`; proof handoff `tasks/agent-loop/inbox/20261021-r171-proof.md` `37f3057c3c5be46eb36e6624cdc98e4945d9943d90ebcd9cb765c32e85b13525`. Both received fresh CLEAN source/native review from `/root/r157_contract_review`.
- Fixture/harness review: `/root/r157_contract_review`, CLEAN for the exact two source hashes; no build/run.
- Contract source membership is approved only as a source argument under its stated base typing contracts; no parser or inference success is presumed.

## Host pins and one exact invocation

Immediately before any execution, require a separate fresh CLEAN review of this handoff revision, these exact inputs and the invocation below. Verify host executable pins:

- `/usr/bin/bwrap`: version `bubblewrap 0.9.0`, SHA-256 `e318903862396f96de3df57264e0158682b952fd3fb53ac23d876413e7b30f71`.
- `/usr/bin/timeout`: `GNU coreutils 9.4`, SHA-256 `12690a043dfd555a6c14ccc1564f5649c18f1762c0d6ff66729948130898ec52`.

This is the only authorized command, once, from the repository root after that review and Luna's recorded gate. It grants networkless read-only host mounts, with writes only under `target/r171/` plus the three named caller-side receipt redirections. `/tmp` is mounted read-only. Cargo runs offline and locked. Timeout gives the process group 280 seconds, then 10 seconds for TERM/KILL; a separate bounded scan has a 4-second run plus 1-second kill grace. The wrapper records probe, exact process-group and marker-scan statuses separately. The total probe allocation is 300 seconds.

```sh
ROOT=/home/momota1029/rust/yulang
mkdir -p "$ROOT/target/r171/tmp" "$ROOT/tasks/agent-loop/probes"
: > "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stdout"
: > "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr"
: > "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.status"
/usr/bin/timeout --signal=TERM --kill-after=10s --verbose 280s /usr/bin/bwrap --unshare-net --ro-bind / / --bind "$ROOT/target/r171" "$ROOT/target/r171" --dev /dev --proc /proc --ro-bind /tmp /tmp --chdir "$ROOT" --setenv HOME /home/momota1029 --setenv CARGO_HOME /home/momota1029/.cargo --setenv RUSTUP_HOME /home/momota1029/.rustup --setenv RUSTUP_SKIP_UPDATE_CHECK 1 --setenv CARGO_NET_OFFLINE true --setenv CARGO_TARGET_DIR "$ROOT/target/r171" --setenv TMPDIR "$ROOT/target/r171/tmp" --setenv PATH /home/momota1029/.cargo/bin:/usr/bin:/bin -- /bin/sh -c 'ps -o pgid= -p "$$" > "$CARGO_TARGET_DIR/process-group-id"; exec cargo run --offline --locked --manifest-path tools/inference-playground/Cargo.toml --example r171_provider_incidence' > "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stdout" 2> "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr"
status=$?
pgid=$(cat "$ROOT/target/r171/process-group-id" 2>/dev/null)
pgid=$(printf '%s' "$pgid" | tr -d '[:space:]')
case "$pgid" in
  ''|*[!0-9]*) process_group_status=1; printf 'POST-RUN PROCESS GROUP CHECK: missing or invalid PGID: %s\n' "$pgid" >> "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr" ;;
  *) if /bin/kill -0 -- "-$pgid" 2>/dev/null; then process_group_status=1; printf 'POST-RUN PROCESS GROUP CHECK: residual process group %s\n' "$pgid" >> "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr"; else process_group_status=0; printf 'POST-RUN PROCESS GROUP CHECK: group %s absent\n' "$pgid" >> "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr"; fi ;;
esac
/usr/bin/timeout --signal=TERM --kill-after=1s 4s /usr/bin/python3 - <<'PY' >> "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.stderr"
import os
needles = (b"target/r171", b"r171_provider_incidence")
skip = set()
pid = os.getpid()
while pid > 1:
    skip.add(pid)
    try:
        rest = open(f"/proc/{pid}/stat").read().rsplit(")", 1)[1].split()
        pid = int(rest[1])
    except (OSError, ValueError, IndexError):
        break
left = []
for entry in os.scandir("/proc"):
    if not entry.name.isdigit() or int(entry.name) in skip:
        continue
    try:
        cmd = open(f"/proc/{entry.name}/cmdline", "rb").read().replace(bytes((0,)), b" ")
    except OSError:
        continue
    if any(needle in cmd for needle in needles):
        left.append((entry.name, cmd.decode(errors="replace")))
if left:
    print("POST-RUN PROCESS CHECK: residual probe processes found", left)
    raise SystemExit(1)
print("POST-RUN PROCESS CHECK: no matching command lines found")
PY
scan_status=$?
printf 'probe_status=%s\nprocess_group_status=%s\nprocess_scan_status=%s\n' "$status" "$process_group_status" "$scan_status" > "$ROOT/tasks/agent-loop/probes/20261021-r171-provider.status"
test "$status" -eq 0 -a "$process_group_status" -eq 0 -a "$scan_status" -eq 0
```

On any pin/input mismatch, failed prospective gate, refusal, timeout, nonzero status, residual process or outside write/network attempt: preserve exact receipts, stop, confirm process cessation and do not retry. Do not run tests, Yulang2, an evaluator, web demo or external runtime. Probe output is diagnostic only, not a theorem or source fact.

## Expected interpretation and unresolved join

The intended successful source instance is `terminal`'s resolved body Name together with the distinct `relay` Apply `terminal t` and its exact argument resolution. The initial `relay (signal::ping())` operation is not the forwarding edge. The CLEAN-reviewed proof's exact rows and conditional base typing derivation are in the pinned proof artifact above.

The borrowed R170 observation exposes ordinary provider/Capture rows, but explicitly returns `NotJoinedToContextRecord` for its Lambda source join. Equal q values, route IDs, row counts or printed relation IDs will not be promoted to incidence. The required R169 association remains open unless this exact run and extant source evidence authenticate source CauseId/FactId/Terms through the same provider's Capture or justified shared anchor and own maps, ordered routes and Replay alternatives, to the forwarding Apply's actual A_F consumer q with residual/scoped payload. Preserve all alternatives and self-pair factorization. Missing or truncated evidence leaves that join OPEN and is the result; no source rewriting or extra instrumentation is authorized.

After review and the single run, Luna will freeze a sequential result revision with source/harness and receipt hashes, honest statuses, output/truncation analysis, remaining association, and writes/process-stop status. Final result review remains independent of Luna. Luna alone integrates, commits and pushes exact reviewed R171 paths plus current state/closeout.
