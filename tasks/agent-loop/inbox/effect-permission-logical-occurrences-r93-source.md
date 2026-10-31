# R93 source handoff — logical occurrence to admission/readout seam

Sprint / contract: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R93`,
contract SHA-256 `e762c73cfd33c60428bb632ef4441bac8f4df2f579a6e0a9c394c5e6ac9b0c77`.
Baseline: `853b52673` (R93 admission pushed). Assignment: primary source lane,
read-only inspection; 600-second ceiling. This handoff is frozen at revision 1.

## Source constructors and generated routes

The pinned `OriginalSourceGeneration.lean` hash is
`126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
For an App, `sourceRules` emits `existsE ⟨mark.site, .viewLogic, 0⟩` around
the `.app` rule and its actual callee and argument subtrees (lines 112–123).
For a Lambda, it emits a description owner and a ViewLogic owner around the
lambda, then a formal-entry route through invocation and receipt. Under the
actual parameter-entry and pattern nodes, its body rule is wrapped by
`existsE ⟨body.site, .eventProof, 0⟩`; its local context is `bodyContext`, and
the body remains the exact `sourceRules bodyContext body` subtree (lines
`132–168`). The branch on `formal.entry` preserves Value's return/rebind
suffix and Computation's retained-entry route. `annotated` retains the
outer-source annotation wrapper.

The independent source-owner path is in
`OriginalSourceEvents.lean`, SHA-256
`cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`.
`sourceOwners` runs `owners [] [] (sourceRules context source)`. Its traversal
collects logical binders at their constructor routes; rule descent uses route
tag 0, forest siblings tag 1, and choice-right tag 3. `Owner` retains route,
binder, enclosing `ScopeEntry` telescope and lifetime. `ActualKey` separately
retains origin declaration, route, binder, actual parent path, occurrence and
raw runtime payload (`OriginalSourceEvents.lean:20–46,306–355`). Thus route
plus binder alone is not the full actual-event identity, and R93's new
inventory does not prove equality with `sourceOwners` until a route-convention
adapter is checked.

## Admission and decoding boundary

`OriginalFormalAdmission.lean` SHA-256 is
`77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`.
`localAdmissions` recognizes ViewLogic by the flat `viewBinder intro.parameter`
equality and admits any encoded `ViewPacket intro`; the packet's type-indexed
reference is the source parameter coordinate and its encoding writes no
descriptor/interface fields. Existing `view_preserves_contract` therefore
shows that this payload does not rewrite the selected formal contract. The
packet still carries `viewMeaning`, event `eta`, and witness; this local fact
does not validate those fields against the source-generated occurrence.
For `.eventProof`, `localAdmissions` delegates unchanged to `base.logical`.
Existing theorems at lines 151–153 and 417–453 establish that split and the
flat-binder/route distinction.

`OriginalSourceEnvironment.lean` SHA-256 is
`0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`.
`decodeFrame` sends every `.logical` frame directly to `state.logical`; unlike
Shared and runtime frames, it does not retain that frame in `fixedFrames`
(`:389–395`). `Decoded.logical` writes descriptor/interface lists, view meaning,
eta and witness (`:346–352`). Therefore neither decoding nor a route inventory
alone supplies a proof that the consumed payload is the one introduced at the
source route.

## Exact remaining law and parent application

R93's useful application is occurrence provenance: it can identify the actual
generated ViewLogic/App and EventProof/body subtrees, their full constructor
routes, contexts and source expressions. To reach the effect-hygiene parent,
an owner must still prove an adapter from that route convention to
`OriginalSourceEvents.Owner`/`ActualKey`, carry the resulting occurrence
evidence into admission and readout, and show the selected Value or
Computation formal contract reaches the actual Name consumer. The current flat
ViewLogic admission cannot distinguish two source occurrences with the same
Binder, and EventProof has no local source admission clause. The required
semantic admission/readout law remains OPEN; this source result does not
authorize Rust edits or an admission-policy change.

The falsifiers are a missing generated binder, a repeated complete route,
changed body subtree, or dropped outer telescope/entry-mode/annotation branch.
Repeated sites specifically test that a flat Binder does not stand in for
route identity. Both Value and Computation remain in scope. Original A/B,
source/native correspondence, complete effect hygiene and production remain
OPEN.

No Rust/Lean edits, execution, build, test, scratch/cache/environment/worktree,
or generated output were used in this source lane. The independent proof lane
owns its two exact paths. Primary owns Git and adjudication.
