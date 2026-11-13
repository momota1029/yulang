# Actual-inspection boundary agreement: owner-decision audit

Date: 2026-11-14. Status: **Draft; blocked on the owner question in §4.**
Scope: the local diagnostics of `GeneralNominalActualInspectionSteps.Step`,
before defining an agreed B4 V5 boundary. No language decision is made here.

Authority: [spec §6](../../spec/06-roles.md), including its confirmed decisions,
and the [B4 draft and addenda 1–7](2026-11-08-b4-main-statement-draft.md).
The task explicitly requires stopping if a guard introduces a deferral without
an owner decision. That condition is reached below; no new Lean boundary,
classification predicate, or bridge proof is implemented in this change.

## 1. The agreement being requested

The [actual-boundary note, §1](2026-11-14-actual-boundary-hole-phases.md)
identifies `GeneralNominalActualBoundary.boundary` as an operational adapter:
its Step is actual-inspection Step, but its local fields still come from
Settled. Its six structural bridge results do not establish installation-guard
agreement. They cannot certify an agreed replacement merely by inheritance.

The intended obligations for replacement predicates are:

- `Selected(registry, state, demand, key, children)` must characterize the
  unique visible candidate with all actual installation premises satisfied,
  or the corresponding already-installed candidate. Installation means the
  actual `At.install` premises, including `FeedbackSteps.Installable` and
  `ActualInspectionSteps.PacketGuard`; old `Unique` alone is insufficient.
- `RootCycle` must detect a root on a cycle, including cycles through nominal
  arguments without opening nominal bodies. `InspectedCycle` must use the
  actual report's tested origins, `Represents`, and `RecursAt`, including
  applicable alternative candidates. A failed `Safe` is not itself a cycle:
  `Safe` also requires complete origin records and `Located` certificates.
- `Pending` must have an owner-supported cause. Unknown unnamed input heads
  have first priority. Once they are known, K2 rejection precedes delayed
  expansion, ambiguity, and selection. Unsettled-output deferral preserves
  the equations used by K2.
- With no pending cause or K2 reason, two distinct surviving declaration IDs
  give ambiguity, and no survivor gives ordinary rejection. A local selected
  node does not assert that all children have dictionaries: addendum 2 keeps
  child failures in the diagnostic tree.

These are obligations, not final definitions. In particular, defining
`Pending` as the negation of guard satisfaction would include the unsupported
case in §3. It would make the desired equivalence easy by changing its meaning.

## 2. Owner decisions and their limits

The quoted Japanese text is retained verbatim from the linked sources.

| Requested behavior | Owner text | Consequence for this boundary |
| --- | --- | --- |
| Wait for unknown heads | Spec 6.4: 「`x` の型の下界が分かって、その型に `.method` があるとき」. Spec 6.3: 「この集合を使うのは、**型が決まった role 制約**の検査（見える `impl` で一つに決まる／曖昧／見つからない）だけである。」 | An unknown lower head is pending; a unique visible impl cannot determine it. Addendum 1 explicitly retains pending even with zero visible impls. |
| Wait for every unnamed argument | B4 addendum 4: 「需要の名前なしの引数は、候補の impl がその位置を変数で受けるだけ（中身を見ない）でも、すべての下界の頭が分かるまで需要全体を保留にする。」 and 「名前つきの引数（関連型の出力）は待つ対象に入れない。」 | Root readiness covers all unnamed arguments, including variable-only positions; it does not require every nested payload or named output to be known. Addendum 3 supplies the preceding multiargument decision. |
| Defer unsettled-output justification | Spec 6.3, 2026-11-13: 「片付いていない impl の出力を根拠にした展開は保留する」 and 「ソースの制約や、片付いた需要（子まで全部解けたもの）の出力が根拠になれば再開する。」 | This supports the semantic purpose of the settled `DecisionGuard`. Addenda 5–7 extend the rule from self-dependent cycles to downstream and then acyclic unsettled producers. It does not say that every failure to construct a certificate is such a dependency. |
| Keep K2 independent of output deferral | The same spec decision: 「等式そのものは捨てず、通常の制約・同じ入力の需要のまとめ・再帰型（K2）の判定には使う。」 | Delaying expansion must not hide a known cycle. |
| Reject actual inspected cycles before choosing | Spec K2: 「head の非変数 pattern が名前の無い構造的な再帰型の constructor を調べる必要が出た時点でも」拒否. Priority: 「安全な候補が 2 つ以上あっても、1 つだけでも、曖昧性や選択より先に拒否する。」 | Use actual inspected positions across applicable alternatives; do not select a safe alternative to evade an unsafe one. |
| Reject roots on cycles | Spec K2, 2026-11-12: 「根（または head の非変数 pattern が調べる位置）が**循環の上にある**か」 and 「名前つきの型の中身（body）は開かない」. | `len (nest 0)` with μ ≈ list μ is rejected; `len [loop 1]` can still pass when its list root is merely above another cycle. |
| Visible ambiguity and zero candidates | Spec 6.2: 「同じ role と型に対して複数の `impl` が候補になる場合は**曖昧**として拒否される」; spec 6.3 limits the visible-impl check to known types. B4 rejection clause (iii): 「区間の制約の伝播ですべての候補が消える」. | Preserve visible candidate identity and cardinality. The zero-candidate rule is subordinate to addendum 1. |
| Preserve actual input identity | Spec 6.3: 「すべての名前なしの引数が同じものを指す」（「同じソースの識別子であるか、等式で同じと示せる」）and 「impl を選ぶ前、保留のままでも行う。」 | This authorizes sharing equal actual inputs. It does not authorize making a known demand semantically pending because an implementation discarded that identity. |
| Missing shared-provenance certificate | No corresponding confirmed deferral decision was found in spec §6 or addenda 1–7. | The existing conservative implementation cannot supply its own semantic authority. This is the stopping point. |

Spec 6.5 also confirms centerless intervals: 「不変な引数は、中心を持たない区間
`(lower, upper)` で持つ」. Recovering actual input identity must not choose an
arbitrary value between the endpoints. This constrains a repair; it does not
establish a new pending rule.

## 3. Concrete guard obstruction and its exact scope

`GeneralNominalSharedCaptures.GenerationGuard` requires a `Usable` origin for
every head variable needed by a where-child. `Usable` includes `Captured`,
which requires a recorded origin and agreement across repeated captures.
The actual `PacketGuard` contains this guard through the shared packet guard.
This requirement is separate from the head-justification guard.

The existing checked fixture is
`GeneralNominalSharedPump.pPacket`. Its source root is
`P((V² A, V² A), (V never, V any))`, where V(t) is `:{tick t}`.
The source snapshot records both unnamed lower heads and all constructors
that P's head inspects; A's interior is captured as a variable. The initial
journal contains no installed output facts. Nevertheless:

- `GeneralNominalSettledIntervalDeclarations.checked` checks its registry.
- `GeneralNominalSettledIntervalSource.initial_source` establishes the initial
  source contract. It also gives an actual-inspection initial state through
  that relation's existing `SourceFormed.initial` constructor.
- `GeneralNominalSharedPump.p_captures` computes the second capture as
  `⟨1, (3,5), none⟩`, despite its source-known lower variant head.
- `p_first_round_blocked` proves failure of `GenerationGuard` for this packet
  at every tracked state. `p_not_installable` proves failure of every shared
  packet guard for it; the actual packet guard implies that shared guard.

Thus this failure is not merely an unproved certificate for that packet:
the certificate is refuted by the missing recorded origin. It is not an
unknown unnamed root or a dependency on an unsettled installed output.
The [shared-origin note, §2](2026-11-13-nonpoint-provenance.md) explicitly calls
this a “conservative implementation stage” and leaves complete
source-to-origin production as a separate obligation. Its §3 describes this
same first-round deferral. Those implementation statements are not owner
decisions extending the language's final pending outcomes.

The source-shaped example below is the one from the
[interval-sharing analysis, §2](2026-11-13-settled-cover-obstruction.md):

```yulang
role P 'a 'b:
    our a.pump: 'b -> int

role W 'a 'b:
    type anchor
    type out
    type tail

impl W (:{tick 'a}) 'b:
    type anchor = 'a
    type out = :{tick 'b}
    type tail = 'b

impl P (:{tick :{tick 'a}}) 'b:
    where (:{tick 'a}): W('b, anchor = 'z, out = 'z, tail = 'u)
    where (:{tick 'a}): P('b)
    our x.pump y = 0

my trigger(x: 'a, b: :{tick 't}) = (:tick (:tick x)).pump b
```

The triggering expression has known outer constructors and reuses `b` in
both child demands. The exact Lean fixture uses the strict interval stated
above. No frontend-to-that-exact-interval theorem is claimed, and this audit
does not prove old Local selection, all other installation premises, or
permanent haltedness of that source. The obstruction established here is the
independent missing-origin guard failure and the absence of authority to turn
it into an additional semantic pending cause.

## 4. One owner question

For the `trigger` example, when the needed input heads are source-known but
the shared actual-input certificate for `b` is missing, should the demand
**(1) remain pending until that certificate is available, including final
pending if it never arrives**, or **(2) retain the existing head-based
semantics, requiring the source/provenance implementation to preserve or
reconstruct `b` before an agreed boundary can be supplied**?

Option 1 is the lazy option. Option 2 is recommended because it preserves the
documented distinction between semantic deferral and an incomplete producer.
Choosing it would require work beyond a diagnostic-only retarget of the frozen
actual Step/source representation. No choice is made here.

## 5. Remaining work and validation scope

The new predicates, their agreement equivalences, actual K2 correspondence,
V3 totality/functionality, all requested V5 transfers, conditional executor
construction, `whereAccessible`, and `generatedChildren` remain open for the
proposed agreed boundary. Existing operational-adapter results are unaffected.
There is no new Lean module or audit file, and no theorem closure is claimed.
No termination work or git-ref operation is part of this change.

Checks run from the repository root:

| Command | Exit code | Meaning |
| --- | --- | --- |
| `cd lean && lake build Yulang > /tmp/yulang-actual-boundary-agreement-build.log 2>&1` | 0 | Existing aggregate build succeeds; no new Lean claim is checked. |
| `git diff --check` | 0 | No tracked whitespace errors. |
| `python3 /tmp/yulang-actual-boundary-agreement-scope.py` | 0 | Only this new note and one appended INDEX entry; local Markdown links resolve. |

A focused new-module build and `lake env lean Audit/<YourFile>.lean` were not
run: the stop condition was reached before creating either artifact. The
existing fixture statements above were inspected in source, not newly audited.
