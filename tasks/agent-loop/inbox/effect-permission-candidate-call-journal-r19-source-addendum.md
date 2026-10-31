# R19 source addendum — term journal coupling

Status: primary-authenticated source clarification for the frozen R19 source handoff
Scope: same selected ordinary caller and same R19 contract; no authority or source-domain expansion

R18 `Conditions.activeJournal` models `BranchTermArena.route_journal` in
`crates/yu-solver/src/term.rs`, not the identically named
`InferenceSession.route_journal` field. The two are coupled by the production
route transaction owner:

- `Store::begin_route` calls `self.terms.begin_route()` before returning its
  store checkpoint (`lib.rs:3503–3517`).
- `InferenceSession::begin_route_transaction_for` checks that its session
  journal is absent, calls `store.begin_route`, then prepares/publishes the
  session journal (`lib.rs:9267–9355`). If preparation fails after the store
  begin, the error paths call `store.rollback_route` before returning.
- Successful transaction finish takes the session journal and calls
  `store.commit_route`; error finish calls rollback, which takes the session
  journal and calls `store.rollback_route` (`lib.rs:9505–9535, 9646–9678`).
- Store commit and rollback delegate to term commit/rollback (`lib.rs:3518–3558`).
  `BranchTermArena::commit_route` and `rollback_route` both `take()` the active
  term journal and retain it only as `route_journal_spare` (`term.rs:789–822`).
- Production `BranchTermArena.route_journal = Some` is established by
  `BranchTermArena::begin_route` (`term.rs:746–784`), reached from the Store
  transaction owner above. Other `begin_route` calls in `term.rs` are tests.
  `BranchTermArena::new` initializes active and spare journals to `None`
  (`term.rs:713–714`).

Thus the R18 active-journal proposition is the term-arena active journal. A
completed successful route wrapper returns it to `None` through commit; a
completed error wrapper returns it to `None` through rollback. A selected
ordinary candidate source root is invoked directly, with no wrapper at root,
schedule, or target-action dispatch. Its selected `BeginLambda` action does not
begin a transaction; the immediately following `FormalAnnotation` reaches
`with_term_events` / `positive_tuple` directly. No transaction can interleave
inside this synchronous action prefix.

This supplies the missing representation bridge between the R19 handoff's
session-level transaction trace and R18's term-level condition. Proof still
needs to make the completed-wrapper transition explicit and must not equate
the two journal fields by name. The broader graph-plan prefix remains
source-qualified by the invariant that only a completed transaction owner can
set the term journal, and each successful/failed owner return clears it. The
source handoff's selected-schedule restrictions remain in force; this addendum
does not authenticate a particular native source module execution or close
native, parent, or production gates.
