# Current HIR/F5 route for the identity binding

Date: 2026-10-08
Status: Draft research; read-only source-to-artifact boundary
Baseline: `080a5a15af3627fe8122754639e8dd50a59319db`
Lease: this file only
Implementation, semantic adoption and cutover authority: none

## 1. Result

At the pinned baseline, ordinary HIR resolves the body name of `my id x = x`
to its formal parameter and wraps the body in a Lambda. The ordinary F5 solver
recognizes that exact parameter-reference body, constructs the Lambda's
negative argument and positive result from the same live parameter ordinal,
and admits the resulting Function-shaped term at the Lambda root.

This is concrete current-source evidence for the identity endpoint equation.
It does not produce an independently interpreted complete-invocation
descriptor, admission relation, phase/receipt/Force contract or source-free
public use rule. In particular, it supplies no independently licensed
off-diagonal result-provider transport. The existing actual-root descriptor
and successor-membership obligations remain open.

## 2. Governing boundary

The approved root-policy answer requires a transformed displayable scheme plus
necessary use-time information at the actual public root; it does not approve a
decoder or production implementation. The selected contextual Function
membership definition requires same-provider acceptance and complete
observations under independently defined, comparison-independent admission.
Option 2 permits independently licensed non-source production observations,
but does not itself provide a license or complete membership grammar.

This note records only the present HIR/F5 correspondence for one source form.
It does not infer successor semantics from F5, reopen those decisions or
promote a shadow path into production.

## 3. Source occurrence and HIR path

At the pinned revision, `ResolvedExpr::Lambda` stores its exact parameter ID
and body (`crates/yu-hir/src/module.rs:1338–1344`). Identifier lowering first
checks the active parameter scope and records
`NameResolution::Parameter(parameter.id)` (`module.rs:1991–1999`). Thus the
resolved `id` body is an incidence back to the actual formal, not another
independent binding.

Ordinary `lower_module` calls `lower_module_with_counters` without enabling
shadow applications (`module.rs:867–874`). The application-lowering entrypoint
is compiled for `shadow` or tests and sets `shadow_applications`; only that
flagged path invokes the structural application parser (`module.rs:876–899,
1379–1394, 1519–1534`). The retained `ResolvedExpr::Apply` carries an attached
`UnsupportedExpression` error (`module.rs:442–453, 1810–1817, 1930–1937`), and
ordinary collection classifies Apply/Group bodies as errors
(`crates/yu-solver/src/lib.rs:1019–1025`). This is source identity retention in
the shadow lane, not production application typing.

## 4. F5 Lambda construction and comparison

For a Lambda whose body is exactly a Name resolving to the current parameter,
`emit_lambda` records the body's effect occurrence and sets
`body_value_component = None` (`crates/yu-solver/src/lib.rs:1717–1737`). During
Lambda admission, `admit_lambda_fact` obtains the parameter's live ordinal,
uses it as the negative argument endpoint, and—because the body value
component is absent—as the positive result endpoint (`solver/src/lib.rs:10790–
10804`). It then admits the Function-shaped value at the Lambda root
(`solver/src/lib.rs:10805–10820`).

The ordinary live Function comparison decomposes into the current four
polarized children: argument, argument effect, result effect and result
(`solver/src/lib.rs:11415–11444`). This establishes the current F5 constraint
route for this narrow Lambda case. It does not establish the successor
actual-root `Direct` rule, exhaustive complete observation membership, or
principal export adequacy.

## 5. Exact conclusion and omissions

The evidence establishes:

1. HIR retains the formal-to-body Name incidence for ordinary identity
   functions.
2. F5 uses one live parameter ordinal at both the negative argument and
   positive result positions for this exact body shape.
3. Ordinary application syntax is not thereby accepted through the current
   production route; the structural Apply carrier is opt-in and error-marked.

It does **not** establish a universal impossibility claim about current or
future compiler routes. Nor does it prove a language-level rejection of any
source form. The specific unresolved bridge is from these ordinary F5 endpoint
constraints and shadow source identities to the approved transformed public
contract with active invocation phases, independent admission, complete
Option 2 production licenses, and actual-root use.

Not inspected: parser completeness, unrelated Lambda bodies, callback/handler
formation, generalization/instantiation, solver principality, all compatible
contexts, performance, and runtime behavior. No tests, builds, probes or code
changes were made.

## 6. Frozen source snapshot

SHA-256 at the pinned baseline and live working tree:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |

The draft identity descriptor proposal was added after this baseline and is
used only as navigation for the next bridge; it is not an authority.
