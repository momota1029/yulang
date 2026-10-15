# Direct versus identity-wrapped callback: frozen native observations

Status: independently reviewed finite source-qualified witness; not an exact-original-program or runtime counterexample.
Native source/binary baseline: e9790f96f154ef0ddf67cb45aa26a569148569d7.
Binary: /home/momota1029/rust/yulang/target/debug/yu-playground
SHA-256: ff9bbd6f0fb48200dcf691602547ab4020d0013e2b007b2493a2cc9a06293bed

Objective/method: independently discriminate the reported scope-identity obstruction
using actual source constraints and retained scoped observations. No scopes, effect
members, relations, or transition premises were synthesized. The direct-vs-id
mutation is the sole difference in the successful source pair. This corroborates
a bounded premise of the constructive lane, not the correctness of a new guard.
The selected language meaning and original Callback Hygiene target are unchanged.

## Complete successful sources

Direct:
```yu
act signal:
    our ping: () -> int

my id x = x
my g h = catch (h 0) {
    signal::ping(), _ -> 1,
    v -> v
}
my callback i = signal::ping()
my answer = g callback
```

Identity-wrapped:
```yu
act signal:
    our ping: () -> int

my id x = x
my g h = catch (id (h 0)) {
    signal::ping(), _ -> 1,
    v -> v
}
my callback i = signal::ping()
my answer = g callback
```

The requested literal `g (\i -> signal::ping())` failed syntax admission in
both first probes, so those sources produce no scope evidence. The successful
pair instead supplies the same closed callback through a named definition.
No general equivalence theorem between the two callback construction forms is
claimed. Original failed sources and diagnostics remain in direct.yu/identity.yu
and matching logs; they are not silently discarded.

## Actual source-to-Catch observations

Pinned candidate_source.rs:833-837 constructs Catch slot 51 as the actual
scrutinee effect flowing to the Catch result effect. This owner was read via
`git show e9790f96f154ef0ddf67cb45aa26a569148569d7:crates/yu-solver/src/candidate_source.rs`
so concurrent edits are not inputs to this interpretation.

Direct source:
- Authenticated omitted-formal introduction 0 belongs to g's Lambda occurrence 6,
  and h-call occurrence 9; the original demand is term271, output scope5.
- Actual FreshUse1 demand relation86 has output scope20, input route3, term327.
- Source relation34 (occurrence8, slot51) transports to relation97 with the
  actual original/copy pair EffectRow4->3 / EffectRow32->33.
- Recorded Support1/AnnotationMember(1,0) at relation138, row32 (scrutinee), has
  protections[20]. Relation142 at row33 (Catch output) also has protections[20].
- Final answer row14, relation158, retains protections[20].

Identity-wrapped source:
- Authenticated introduction 0 belongs to the same source-role Lambda occurrence6,
  h-call occurrence12; original demand term280, output scope8.
- Actual FreshUse2 demand relation113 has output scope28, input route4, term349.
- Relation197 records Support1/AnnotationMember(1,0) at row41, protections[28].
- Relation136 maps original id-Apply relation43, occurrence9 slot2, through
  FreshUse2: original EffectRow25->7 maps to actual EffectRow41->42.
- Replay relation201 combines lower197 with upper136 and records the same member
  at row42 with protections[]. Thus scope28 is absent before the Catch seam.
- Original Catch slot51 relation58 transports through FreshUse2 to relation142,
  original EffectRow4->3 / actual EffectRow43->44.
- Actual member observation205 at row43 (scrutinee) has protections[]; observation208
  at row44 (Catch output) has protections[]. Final answer row17, relation224,
  also has protections[].

Scope numbers are local to their individual executions. The direct scope20
and wrapped scope28 are matched by each log's original introduction, scope
lineage, demand and FreshUse record, not by numeric equality across programs.
Each listed source/target row has exactly one recorded Support1 observation;
these are finite emitted observations, not an enumeration of all derivations.

Conclusion class: genuine admitted-source witness to removal of the callback
*demand's existing protection scope* by the nested id Apply before Catch in the
current scoped experiment. The direct control retains its corresponding scope.
This supplies evidence for the scope-identity obstruction to the proposed
receiver interpretation. It does not establish capture eligibility, actual
operation removal, runtime behavior, soundness, or the exact original program's
expected result. Catch still forwards effects. It does not certify a replacement
receiver guard or authorize changing the selected compose release operation.

## Exact commands, outcomes and hashes

The manifest records fully expanded command arrays, exits, stop reasons, wall
times and complete source/stdout/stderr hashes. Every execution used
`--scoped-experiment --intrusion`; no other executable inference route ran.

```text
/home/momota1029/rust/yulang/target/debug/yu-playground --scoped-experiment --intrusion /tmp/yulang-callback-exact-20261015/receiver-falsifier/direct.yu
exit=1 stop=None wall_seconds=0.0055 stdout_bytes=0 stderr_bytes=1005
b8c3f73a8061a6aa5346c3a9b5fc1ed6414c0bf9d40891218c637b0076deca3f  direct.yu
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  direct.stdout
edcc4194c13192fff904abe0505c60d206d5350687d636923090ef7195ff2824  direct.stderr
```

```text
/home/momota1029/rust/yulang/target/debug/yu-playground --scoped-experiment --intrusion /tmp/yulang-callback-exact-20261015/receiver-falsifier/identity.yu
exit=1 stop=None wall_seconds=0.0055 stdout_bytes=0 stderr_bytes=1005
d20e957822f12b7f3310408149c22e8d70e7a55341bc69a4828e026ab9855e1e  identity.yu
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  identity.stdout
42f2469d5643f7e2f223832040088db3ef7991c3f1b64969db3f2def86a03a99  identity.stderr
```

```text
/home/momota1029/rust/yulang/target/debug/yu-playground --scoped-experiment --intrusion /tmp/yulang-callback-exact-20261015/receiver-falsifier/direct-named.yu
exit=0 stop=None wall_seconds=0.0261 stdout_bytes=71509 stderr_bytes=0
62092e06aab66dd107f2db2a9f906c0566bd61b1063e4f0b5b1aad1a6b5a1a48  direct-named.yu
96409e7c1557eeb0e807ce273023132e1947eb35442f1938f72f3e03d66c446d  direct-named.stdout
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  direct-named.stderr
```

```text
/home/momota1029/rust/yulang/target/debug/yu-playground --scoped-experiment --intrusion /tmp/yulang-callback-exact-20261015/receiver-falsifier/identity-named.yu
exit=0 stop=None wall_seconds=0.0364 stdout_bytes=107206 stderr_bytes=0
e335a2d3fbeefa89865c0f14be0a34ac1a0ca80f1942d8d7d1e7edbb75f38668  identity-named.yu
bc6f0436f0b67bbff6473bcd558739bafb53c84ffd6f0eab72c56c35cfe02950  identity-named.stdout
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  identity-named.stderr
```

Four of four CLI processes consumed, sequential, each capped at 15 wall seconds
and 256 KiB per output stream. Two syntax failures, two solved observations;
no timeouts, killed processes, or output-cap stops. No Cargo, build, test,
network, Git mutation, delegation, or compiler edit. CPU time and peak RSS
unknown; no randomized seed/search range. Scope includes exactly this pair of
closed named callbacks. General aliases, nested scopes, recursion, annotations,
literal Lambda construction, actual subtraction and the original stdlib example
remain unverified.

Checks: input/command/log hashes rechecked; selected source origin, FreshUse,
Replay, demand, member and source-to-Catch owner correspondence inspected.
No reference oracle ran; semantic targets come from accepted authority, while
all operational observations share the native binary and its current scoped
transformer kernel. This is not an independent proof of that kernel.

Recommended next action: apply this actual source-qualified obstruction to the
constructive theorem's receiver premise before choosing a new identity scheme;
keep the original callback hygiene and source/cutover obligations open.

Commit packet: only leased directory
/tmp/yulang-callback-exact-20261015/receiver-falsifier was written; files are
four .yu sources, their stdout/stderr logs, manifest.json and this REPORT.md.
Baseline e9790f96f154ef0ddf67cb45aa26a569148569d7, binary hash unchanged;
Production packet was unreviewed at freeze; subsequent independent conformance
review verified all source/log hashes and the bounded claims with no findings.
Proposed archival checkpoint message:
research: preserve source-qualified callback receiver scope witness.
Repository archival and any task/theory/authority delta remain primary-owned.
