# R223 — Local Apply provider route

## Disposition

The exact accepted `repeat loop` source exposes both LocalFreshRoutes and the
provider Apply constructor, but the retained records do not join the actual
callback argument to the callback formal's consumer lineage. This is
source-native evidence of an observer gap, not a semantic counterexample or a
refutation of the parent theorem.

## Exact route evidence

- The ordinary `CandidateInference::solve(hir)` source has no errors or
  candidate conflicts. The `loop` Name argument at occurrence 28 has an
  authentic LocalFreshRoute. It maps source Effect(41) to route row Effect(69)
  and retains the slot-4 source bound `BoundKey(Effect(5), Negative,
  Effect(41))` at relation 87.
- The `repeat` callee Name at occurrence 27 has an authentic LocalFreshRoute.
  Its graph includes the callback function's source Effect(31), mapped to
  route row Effect(57). Its formal-side bounds include Effect(31) at relations
  160, 170, and 171.
- The route function nodes retain separate ports: the actual loop positive
  function node has argument-effect Effect(29) and result-effect Effect(41);
  the repeat scheme's callback positive function node has argument-effect
  Effect(31) and result-effect Effect(49). These are structural source rows;
  the port list alone does not establish the callback transfer.
- The `repeat loop` Apply constructor at occurrence 26 retains argument
  endpoint `Component(55)` and a native interface with callee Term(451),
  argument Term(452), and demand Term(456). In ordinary solving its
  `local_callee` and `formal_name` fields are both `None`. Its source Call has
  actual `loop` but no formal registration. There are no `ReplayDemandRow`s
  for this provider Apply.
- The candidate intrusion forest contains 48 effect rows, while the route
  images above are Effect(69) and Effect(57). `effect_rep` leaves those
  out-of-domain route IDs unchanged. Thus comparing those integers through
  the intrusion forest cannot authenticate a relation between the route and
  the WorkBound consumer.

The first missing edge is the source-qualified transfer from Apply 26's actual
argument/function port to the callback formal's retained function port. The
current Apply record owns the actual endpoint and native demand, and separate
LocalFreshRoutes own both schemes, but no occurrence-specific replay,
transport, or function-port record joins those owners. A successful next step
must trace that exact Apply through the function comparison into the callback
formal's source rows and then the `f z` WorkBound relation. Do not treat equal
or unequal row integers as that witness.

## Verification and remaining scope

- `cargo test -p yu-solver --features shadow-apply-candidate r223_local_apply_provider_route_rows -- --nocapture` — passed.
- `cargo test -p yu-playground` — passed; the package's ordinary tests include
  the checked-in playground sample behavior.
- This is a focused test-only observer. No inference semantics or production
  implementation changed. No independent review is claimed. R71, R72, and the
  original computation-forwarding preservation theorem remain OPEN.

## Next evidence target

Trace how candidate_scheme consumes Apply 26's native demand and argument
endpoint alongside the two LocalFreshRoutes. Locate any existing FunctionPort,
FreshUse, or Replay witness that bridges Effect(41) / its function component to
the callback formal's consumer relation. If none exists, identify the minimal
owner-side record that would make the parent proof reconstructible before
proposing implementation.
