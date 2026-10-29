# R29 separate execution authorization — compile-only stage 1

Recorded: 2026-10-29 23:51 UTC. Authority: the user's ongoing Yulang goal and standing sprint authorization; admitted contract `tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r29.md` (SHA-256 `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f`); and the fresh dispatcher recommendation to admit a bounded compile stage after Luna records a separate authorization and preserves execution/review reserves.

## Exact source gate

Independent source review R3 is **ACCEPT** for source inspection only. Its complete R1/R2/R3 report is frozen at `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-review-r3.md`, SHA-256 `8645fcc1adb9fe0beb82ca29d1bd7c9a8ae654006efa403d57b3688ba56a78da`. The leased review inbox has identical bytes. The reviewer charged 900/1,400 seconds, leaving 500 for final evidence review. No compiler, test, runtime, mutation, certificate or proof has run.

Exact frozen inputs:

- Contract: `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f`.
- Schema: `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379`.
- R3 `machine.rs`: `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`.
- `receiving.rs`: `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.
- Source mutation design: `75a408c3cd4f0a8b95a156fb5687cf577d9a927e0a9667c3dd704d154c18c5c2`.
- Author R3 handoff: `a19b4728042e396b452ace2154e5bd0d8a3f7da55d72eb29b91eec381dd041e8`.

## Live roster and assignment

Luna synchronized the agent roster immediately before this authorization (`collaboration.list_agents`, 2026-10-29 23:48:59 UTC onward). R29 implementer `/root/r29_impl` and proof worker `/root/r29_proof` are STOPPED; independent reviewer `/root/r29_review` completed and has stopped writing; dispatcher `/root/next_action_selector` returned its bounded recommendation. No R29 worker is RUNNING and no heavy process is active. The unrelated R17 WAITING assignment and all quarantined paths remain untouched. No capacity or path lease was released.

Luna authorizes the existing Rust owner `/root/r29_impl` to resume under its existing isolated project and `build-target` leases, with fresh worker session `R29-RUST-COMPILE-R1`. Source paths stay FROZEN. Resume receipt must identify the actual command and active process; current state must be updated from WAITING to RUNNING only after that live launch is observed.

## Sole authorized command

Working directory: `/home/momota1029/rust/yulang/isolated/ep-native-callback-grant-r29/project`.

```sh
timeout 90s env CARGO_TARGET_DIR=build-target CARGO_BUILD_JOBS=1 cargo test --locked --offline -p yu-playground --lib --no-run
```

This is one locked/offline, one-job compile of the library test target; it must not execute tests. The command has a 90-second ceiling. It consumes at most 90 seconds of the contract's 360-second aggregate Cargo allowance and uses only the already leased `project/build-target/`. No network, source edit, retry, runtime, selected-main route, focused test, Lean/Lake process or other heavy process is authorized by this receipt.

## Stop and next gate

Before launch, recheck every exact source/schema hash above, the isolated working directory, and no concurrent Cargo/Lean/Lake process. Stop on any mismatch, compile failure, timeout, output-path expansion, source change, unexpected process overlap or exhausted allowance. Preserve exact argv, stdout, stderr, exit status and resource receipt in the existing R29 receipts lease. Do not repair or retry under this authorization.

If compile succeeds, Luna must adjudicate its evidence and issue a **separate fresh runtime-stage receipt** before the focused certificate/mutation test or either pinned selected-main route. Runtime remains within the same 360-second aggregate Cargo ceiling and must run serially. Lean remains STOPPED until runtime evidence is frozen, its final certificate hash is authenticated, and Luna records the proof lane's fresh serialized receipt. Original A/B, full History, whole-language hygiene, source generation/propagation, soundness, principality, termination and production remain OPEN.
