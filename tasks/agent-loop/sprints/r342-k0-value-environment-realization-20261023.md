# Sprint R342 — K0 runtime value and environment realization

Status: frozen, revision 1.  
Branch / post-R341 baseline: `research/simple-sub-intrusion` / `ab58f80b7652dd26c75c1da293cf3b1ff33a3938` (same as upstream).  
Selector: `/root/r333_selector` recommends this D3/M supplier after R341 closeout; Luna accepts.  
Primary: `/root` (Luna).

## Parent and bounded outcome

The parent remains the full Yulang2/Simple-sub source/native theorem and
original A/B. Follow the user audit
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`,
especially §§4, 6 C/M and 10.3. R341 accepted the unchanged conditional S0
source-typing implication under its exact four premises. R340's authentic
Apply continuation prefix is accepted only with its explicit realization and
capture suppliers.

R342 targets the foundational K0 `ValReal₀` / `EnvReal₀` supplier needed at
the actual Value-entry call boundary. Define source values, typed parameter
environments, code/value/closure realization independently of successful
machine execution. Then establish the source-to-runtime bridge for authentic
K0 Lambda construction, parameter Name lookup, captured environments and the
same-value ValueEntry binding. Compose it with R340's accepted continuation
result through entry into the exact function body.

The proof must derive Function-typed source-value canonical form from the
independent K0 typing relation and the D0 Value preorder pinned below. Invert
the actual judgment, including Value subsumption and join/meet cases; a
syntactically Function-shaped type premise is insufficient. State the result
only for finite source/runtime evaluation prefixes that actually return a
value, so this packet does not assert that a callee evaluation must return.
It may not define `ClosureReal₀` as “the handle reached by a successful call”
or assume the closure conclusion in a canonical-form premise. It must inspect both
dictionary-absent and dictionary-present paths: `substitute_environment` may
create a dispatch wrapper and `dispatch_name` may change dispatch metadata;
the proof must establish exactly what happens to parameter lookup, value
identity and captured source bindings in each authentic K0 case.

**Fixed success result:** a bounded independently reviewed value/environment
lemma for the named K0 owners, with one of (a) all authentic K0 callee-result
forms connected to `ValReal₀`, or (b) the first exact source-qualified
remaining form/owner recorded as OPEN. In either case, prove lookup
preservation, exact Lambda handle/formal/body/capture identity, same-value
argument binding, applicable substitution preservation, and the R340 body
entry composition. State precisely which VREAL and M-REST obligations remain.

Do not claim the rest of M: normal return, result/future-port realization,
effect/continuation preservation, progress or unavailability exclusion remain
separate unless directly proved inside this fixed envelope. No runtime success,
`candidate.unresolved().is_empty()`, or model existence is a definition of
typing or realization. No compiler repair is authorized absent a concrete
source-qualified defect; current source lane is `NO_SAFE_CODE_SLICE`.

## Required source correspondence

Primary census inspects the actual selected-definition `RuntimeProgram` and
machine owners, including:

- authentic HIR lowering and source occurrence/label identity for literal,
  parameter Name, Value Lambda, Apply, If, Group and binding-free Block/
  StatementBlock;
- `Instruction::Lambda` allocation of the exact handle, formal, role, body
  and saved environment;
- `Instruction::Name`, `lookup`, Name consumption and the exact parameter
  cell/value lineage;
- `Frame::Callee`, executable lookup by actual `ValueHandle`,
  `substitute_environment`, `Frame::ValueEntry`, `bind`, `extend` and body
  entry;
- dictionary construction, name-instantiation metadata, ordered dispatch
  substitution, and the absent/present branches without assuming
  substitutions are inert or idempotent;
- literal decoding and the independent base-value representation cases;
- the exact boundary where R340's continuation proof supplies the
  whole-argument Delay, actual invocation and matching return frame.

The checked baseline is the same authenticated single-definition K0 program
from the audit. Excluded constructs remain excluded exactly as stated there;
do not import module/global, local let, Comp-role, record/default, operation,
handler, member/operator or other runtime cases into this theorem.

## Inputs and source pins

- R341 contract `tasks/agent-loop/sprints/r341-k0-source-constraint-retention-20261023.md`,
  SHA-256 `62cb4018db42e0266f0f357ed6f44c187d6397865905b68487fe143d00250769`.
- R341 accepted outcome `tasks/agent-loop/sprints/r341-k0-source-constraint-retention-20261023-outcome.md`,
  SHA-256 `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc`.
- R341 proof `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`,
  SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`.
- R336 rev4 fixed D0 algebra/source typing and D1 interface
  `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md`, SHA-256
  `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
  Its finite Value preorder (including bounded joins/meets and four-port
  Function variance) and independent K0 rules are the canonical-form authority.
- R340 conditional Apply continuation
  `notes/theory/2026-10-23-r340-k0-apply-continuation.md`, SHA-256
  `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`.
- R340 source census final file SHA-256
  `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`.
- R339 conditional D3 definitions/trace
  `notes/theory/2026-10-23-r339-k0-machine-call-simulation.md`, SHA-256
  `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666`.
- R341 source-typing outcome remains conditional and unchanged; do not reopen
  its reviewed result or enlarge this sprint into N/W/Z/A/B.

| Runtime source owner | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

All inputs and source files are read-only. A mismatched pin stops dependent
claims until Luna reconciles the baseline.

## Lanes, leases and review

**Constructive proof — one configured Sol/high `prover`, 2,400 seconds, no
carryover.** It owns only:

- `notes/theory/2026-10-23-r342-k0-value-environment-realization.md`
- `tasks/agent-loop/inbox/20261023-r342-k0-value-environment-prover.md`

**Primary integration output:**
`tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023-outcome.md`.
It is a primary-only lease for the frozen outcome receipt and is not a proof
worker output.

The producer proves/refutes the bounded result above, records every unresolved
VREAL/M-REST supplier exactly, hashes its frozen outputs, then stops. No code,
test, tooling, current-state or scratch-path writes; no descendants.

**Primary source lane — Luna, up to 2,100 seconds.** It owns only this
contract, `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md`
and `tasks/agent-loop/current.json`. Census the actual runtime owners and
falsifier paths while the proof proceeds. Compiler sources remain read-only.

After both lanes freeze, one fresh non-contributor `compiler_referee` receives
the exact bundle for message-only review, up to 1,200 seconds. Review canonical
form independence, handle/environment identity, dictionary branches, all
claimed K0 value/name forms and exact R340 composition. The falsifier is an
authentic typed K0 environment/trace with a concrete mismatched parameter
cell, closure handle/formal/body/capture, changed source-relevant lookup, or a
Function-typed value outside the claimed realization relation. Distinguish a
missing proof premise from a reachable compiler counterexample. No tests,
Cargo/builds, execution probes, Git, network, file writes or descendants.

**Integration — Luna, 300 seconds.** Adjudicate, write the outcome receipt,
update compact state, and integrate only the exact approved paths. Unused
time is discarded. Total fresh envelope: **6,000 seconds** (proof 2,400;
primary 2,100; review 1,200; integration 300), no carryover. Keep the three
UNKNOWN legacy worker identities quarantined; do not reclaim them or exceed
the six-slot cap.

## Stop and scope boundary

R342 ends at a frozen, independently reviewed supplier result or the first
precise source-qualified obstruction. Report R340 continuation and R341 S0
as conditional prerequisites, not as proof of all M. VREAL beyond the
accepted cases, M-REST, whole machine preservation/progress, W/Z, full N,
principality, original A/B, export transport and production remain open unless
separately closed by later approved packets.
