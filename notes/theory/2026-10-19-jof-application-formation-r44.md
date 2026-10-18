# R44 proof attempt: JOF application formation at recursive `loop y`

Status: **candidate derivation; source/parent closure OPEN**
Sprint: `call-output-owner-jof-20261019-r44`, revision 1
Parent: unchanged full inference/evaluator theorem and Simple-sub A/B, **OPEN,
0 → 0**.
Producer: Luna primary `/root`; no coauthors or descendants.

## 1. Claim being tested

The user delegated selection of a recommended semantic route on 2026-10-19.
Luna selected R41's Joint Output Formation (JOF) as a candidate new rule for
the original ordinary Application/Call owner. This note tests whether that
candidate gives a well-ordered source formation at the exact q occurrence; it
does not claim that the old source accepted the same typings.

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

`q` is the body `Application(Name(loop), Name(y))` of `helper`. The direct
`loop x`, later `helper x` applications, `helper`'s completed invocation and
`loop`'s final body result are distinct nodes and interfaces.

## 2. Forward construction under the proposed rule

The pinned typed-computation core fixes the recursive expression construction
shape:

```text
Application(f,a) ↦ Computation(E_q,A_q)
                 ↦ reify(call(code(f),code(a)))
```

It identifies the role of the expression and retains symbolic endpoints; it
does not introduce a q-indexed `Desc` owner. The original Code-Call input
construction consumes `Comp(E_q,A_q), o_q` with operand Code, actual Call
origin and dependent suffix ports as premises. It expressly does not create
the output declaration, prove result inclusion or identify the returned
provider.

Under JOF the proposed candidate steps are:

1. Use the authentic Name constructor for `loop` and the authentic Name
   constructor for `y`, retaining their actual value/capture owners and
   independent source judgments. Do not infer these from their spellings or
   the lexical block alone.
2. Let `Γ_q` be the ordered typed source context produced by those child
   derivations and their enclosing original scopes. No lexical telescope is
   guessed here: the selected source record does not instantiate its entries.
3. At the ordinary Application owner, introduce
   `Desc(C_q, ρ_A, ValueDescription, σ_q, Γ_q)` where
   `ρ_A=(C_q,q,output-value-description)` and `σ_q` is the actual cursor after
   both child schemas, before q's output-indexed Call headers.
4. Form the original Application effect coordinate `E_q` using its actual
   effect constructor and scope. Keep `E_q`, `A_q`, the callee effect,
   argument effect, receiver invocation effect, returned provider and resumed
   world distinct.
5. Form every original complete Call header and arm under the actual ordered
   dependent telescope, with `A_q` and `E_q` substituted at their original
   output/effect ports. Assemble `Q_q` only after its independent roots and
   headers are formed.
6. Emit the unchanged symbolic computation and code. Constraint generation
   records open relations; Simple-sub later accumulates and propagates them,
   performs level extrusion/intrusion and generalizes at its existing
   boundaries. No constraint is solved at this source rule.

The first and second steps have standard constructor forms, and the abstract
fourth/sixth steps preserve the already selected computation/effect
separation. The third step is precisely the proposed semantic addition. The
fifth step is not discharged by naming `Q_q`: it requires the actual typed
root/header premises below.

## 3. Candidate well-formedness consequences

If `Γ_q` is well formed and `σ_q` is a legal source cursor, the proposed
identity inclusion `Δ_A=Γ_q` makes the new `Desc` well scoped. In source order,
every dependency is available before `A_q`, so this rule introduces no
forward reference by construction. Result-indexed headers formed later may
refer to `A_q`; they cannot feed a later provider/future back into its
declaration. This is only local telescope well-formedness. It does not prove
that `Γ_q` is the authentic context, that the original effect is formable at
the selected cursor, or that every header admits the requested substitution.

The finite R42 model applies only conditionally. If an inherited challenge
really is in `Γ_q` and a returned provider is later, JOF permits strategies
that can depend on the former and forbids strategies that depend on the
latter. R42 shows these input orders can have distinct uniform strategy
sets. No q source fiber is available to conclude that this permission changes
an actual program's typing, acceptance or principal scheme.

## 4. Generalize and CopyScope obligations

The source declaration's full `Γ_q` telescope must reach Generalize through
the actual retained typed certificate. L1–L5 classify real constructed
outputs and legal actions; they do not let this derivation erase unused
context entries or infer a minimal free set. For each of the two independent
frames and each alias, the required construction must say which entries are
fixed, retained as parameters, copied, shared or frame-local, using their
source owner and class.

No actual `C/D` copy pair, source map or independent frame projection is
instantiated here. A native level, unchanged endpoint identity or shared
erasure does not supply it. Principality and natural inference remain OPEN
until the exact Generalize action is established for accepted q clients.

## 5. Exact unresolved formation premise

The selected evidence proves the typed computation role and the Code-Call
consumer signature but supplies no complete q instance of:

```text
T ; Γ_q ; A_q:ValueDescription ; E_q:OriginalApplicationEffect
  ⊢ {every original primitive/root Call header and reference at q}
       : one complete SpecCall_q / Q_q with its original ordered arms
```

The missing data are concrete, not a generic request for more investigation:

- the original source component `C_q`, source cursor `σ_q`, and each actual
  typed `Γ_q` entry with owner/class/sort/predecessor dependencies;
- the Application effect introduction and its ordering relative to `A_q`;
- the actual callee return, receiver, receipt, designated consumer, complete
  Call return/provider/world and future interfaces;
- every structural, pending, W/Z, callee-local, receiver-local and nested arm,
  with its original binder order, legal substitution, guard and license;
- the actual pair of independent incoming frames, aliases and Generalize/
  CopyScope actions.

The R41 candidate writes several of these as `Original*` schema names. Those
names preserve intended fields, but do not instantiate the typed headers or
prove their owners. R43's selected-source audit likewise did not assert that
no such owner exists elsewhere. This derivation stops at the exact missing
formation construction; it does not resume a repository-wide search.

## 6. Decision and falsifiers

The recommendation remains: continue JOF as a general Application/Call
formation candidate, with q as a test instance, rather than wait indefinitely
or claim conservation without evidence. This candidate is not ready to become
Authoritative until an independent reviewer can construct the full q header
certificate and Generalize/copy map from independent premises.

Reject or revise it if a complete header uses a later input, if effect
formation is circular under `A_q`, if an original arm or provider-specific
future cannot be represented, if full-context retention changes ordinary
Generalize eligibility without a principled rule, if an existing authoritative
Application case overlaps, or if source/native consumers cannot carry the
certificate without reconstruction. A q-local source-qualified difference
would disprove preservation for the original parent but would not justify
narrowing the theorem; it would trigger a versioned design choice under the
user's delegated recommendation.

No code, test, expected output, fixture, build, Cargo or runtime was changed
or used. The original parent and all source/native, A/B, effect, Call,
principality, termination, F1/FK1 and production gates remain OPEN.
