# Cycle262: executable exact alias requests

Status: Draft representation/proof design,2026-11-18. No language semantics change.

The previous cycle proved fixed-snapshot request coverage from actual source sites,
but request selection still used noncomputable propositional Alias. The actual Alias
is the reflexive/symmetric/transitive closure of a finite list of Nat identity edges,
not semantic type equivalence. This cycle removes that particular computational gap.

## Contract

For every actual saturation state and every root/query identity, a terminating Bool
classifier equals true iff the existing Alias proposition. Original ordered site
filter and flatMap are retained, so the new requests list must be literally equal
to GeneralNominalCenteredHeadOutputs.requests, including duplicates and order.

The baseline implementation may enumerate all finite cuts of the vertex universe
(root,query,all edge endpoints). The query is reachable iff every edge-closed cut
containing root contains query. The finite subset enumeration terminates by structural
recursion on the finite vertex list. Soundness/completeness use edge closure induction
and the reachable cut respectively. This is exponential and intended as a verified
reference, not a performant compiler. A later BFS refinement must prove equivalence.

## Integration obligations

1. Executable classifier iff Alias with no external closure/correctness hypothesis.
2. Executable requests = current noncomputable requests; arbitrary snapshots/root.
3. Transport the cycle261 fixed-snapshot coverage and finite rebase driver to the new
   selection without weakening its ClassEffects meaning or changing fixed-Plan scope.
4. Regression: disconnected identities, reverse edge, transitive path through a
   non-site vertex; original request order and duplicates retained.

The source-wide finite pool across arbitrary installations and dynamic Plan/capture
transport remain separate. Completion and satisfiability must not be conflated.
Yulang2 is not invoked for an internal graph algorithm; existing source alias semantics
are the reference. Entire repo build is prohibited for this worker; focused modules
and independent standalone axiom/usage audits will be run.

## Verified refinement and source-wide pool

The cut baseline has now been refined to a finite frontier search. It starts with
visited=[root] and remaining=all alias-edge endpoints. Each progressing recursion
filters every newly adjacent endpoint out of remaining, strictly decreasing its
length (duplicates are removed together). An edge-closure invariant plus actual
Alias induction proves exact component membership. The implementation computes one
component per root before filtering the original sites; request order/multiplicity
remain unchanged. No semantic type-equivalence decision is substituted for Alias.

The actual child allocation has a stronger finite-pool result than the prior
Absorbed-only preservation lemma: child output targets are either named output
purpose2 ports or equation-specific purpose5 ports. Existing source-formation,
Paterson lineage and finite owner port results enumerate all such targets for every
reachable installation. With the registry's finite output-name menu and initial
root targets, their Cartesian product covers every raw site output throughout the
actual mixed-source trace, without Absorbed. Refresh/merge/equate/reobserve preserve
sites, enqueue is impossible for an already Generated root in these source paths,
and install appends only covered child outputs.

That source-wide pool feeds the *new* finite rebase Step. A supplied observer may
select different source snapshots at different rebase states, provided each is
reachable from the same source Initial. Requests are executable, and every step's
ClassEffects refers to its actual selected snapshot/root. A proof-only DynamicTrace
retains each snapshot/root at its precise intermediate state and yields one history
for all assignments simultaneously. The fixed Plan supplies fact meaning throughout.

This does not construct the observer from rebase state, show it simulates old Step,
or show all meaningful source observations are scheduled. Its reachability premise
is explicit. Source Initial gives existence of a finite candidate pool; extracting
it as a user-facing compiler artifact is separate. Ready, Frame, packet validity,
model existence, arbitrary dynamic Plan/capture transport and full EvidenceNode remain
unproved here. Quiescence is for the supplied new observer, not all old language actions.

## 実際に選択した Plan への拡張

PlanTransport.Same は、宣言・翻訳用constructor catalogue・interpretation・全actual binder名・
default用center列の一致という構造条件。desired ClassEffects の同値を仮定していない。
この条件から、各outputのschema/fact key、全assignmentに対する各factの意味、実ClassEffects
の同値を導出した。既存MatPlanData.Sameからも条件を導ける。
同一seed/owner/declarationで各input captureが「同じpoint」又は「両方nonpoint」なら、
実allocatorの定義からbinderの一致が出る。nonpoint→pointはまだ覆わない。

ObservedPlan.observe は供給された plans state root の実factsをproposalに使う。選ばれたroot
に限ってSameがあれば、固定Plan observerと関数として一致する。PlannedTraceは各中間状態の
source snapshot/root/そのPlanをeventに記録し、一つの履歴で全assignmentのモデル等式を示す。
実source Initialから導出したpoolを使うsource_certificateにも、このstructural compatibility
とinspectの各snapshot到達可能性を明示した。連続するsnapshot同士の旧Step接続、rootの
Generated/Frame適格性、packet validityを黙って補わない。

実candidate atomsのfamilyではordinary journalが異なっても空のbindingsからSameを導ける。
これは非自明なPlan変化例だが、任意atomsが実sourceに到達することやGood/packet Evidence
を主張していない。成功＝充足可能でもない。

境界の使用例として、旧239 sourceには有限request poolがあるのに旧StepのAccがないことを
一緒にkernel検証した。これは新しい言語反例でも停止命令でもなく、pool有限性と旧Step停止性
を混同しないための既知反例の再利用である。新rebase Stepのstrict fact進捗とは対象が違う。

## 選択限定検査・意味的 Plan 輸送

固定pool全体のReadyを先に要求すると、実際には選ばれないunknown bodyまで内部errorにする。
SelectedCheck/Settleは、各roundで実roots state全体のactual requestsを検査し、成功後に
既存schedulerで一つのstrict writeを行う。remaining長で再帰が終了し、成功した実行から
訪問round全部とfinalのReadyを得る。Readyを全stateに仮定していない。
実行errorにも実finite rebase prefixと、診断stateのselected root/正確なcheck failureがある。
Layoutとsource pool coverageがあればoutside-pool errorは除ける。残るselected translation
errorは内部compiler診断であり、言語拒否の規則ではない。

旧未使用unknown例は空root選択だけでなく、実際の非空[focus]選択でも新checkerで成功する。
任意stateから0又は1writeで実6factsを処理し、unused pairはremainingに残る。保持した
履歴制約が不充足でも成功する例を残し、translation検査とSATを混同しない。

さらにPlanSemantic.Layoutは宣言/catalogue/interpretationだけでschema/factsの同一を保証。
actual binder/center名が違っても、一つのassignmentでそれらの値がEquivalentならbodyと
ClassEffectsを運べる。SemanticObserverは『baseを満たすassignmentならこの局所値同値が
成立する』BaseCompatibleを前提に、Modelsのbase成分を使って全assignmentのstep iffと
同じactual planned historyの意味へ接続する。Layoutは別に要求するのでbaseが空の場合も
runtime tableの一致を仮定から失わない。実source modelからBaseCompatibleを導くことは未完。

Nをcandidate Output list長とすると実body facts≤N、同名pair facts≤N²。従って新Stepの
非自明write数≤N+N²を任意valid stateについて証明した。これは言語処理全体やobserver・
alias searchの計算量評価ではない。新source compilerを構成する残る主要義務は、inspectを
有限rebase stateから実際に生成すること、選ぶroot/PlanのFrame適格性、baseとの意味的輸送、
新旧境界のsimulationとEvidenceNodeである。
