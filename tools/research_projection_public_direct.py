#!/usr/bin/env python3
"""Conditional native Direct proof-fragment checker; research only.

Supported fragment: IDENTICAL complete inlet, IF and evidence incidences;
independently typed target-domain conjunctions; source RESULT inclusion into
its target result; preserved Echo/Fixed dependencies. The scalar language is
Unit/Bool/Int, Any and binary unions. No source lookup or production integration.

The supplied immutable Environment is a semantic PREMISE: its registered
whole-inlet/IF/foreign-value laws must have been independently justified. This
script checks their finite operand/scope identities and the submitted proof
fragment; it does not prove those independent laws, enumerate every lawful
view, implement H7, or establish semantic soundness by passing regressions.
Ground imports and built-in context-value admission predicates are fully typed
here. Foreign imports require an explicit matching complete-contract premise.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
import json
import re


@dataclass(frozen=True)
class Ref:
    name: str
    epoch: str


@dataclass(frozen=True)
class Type:
    tag: str
    args: tuple[Type, ...] = ()
    name: str = ""


@dataclass(frozen=True)
class ValueProof:
    rule: str
    source: Type
    target: Type
    children: tuple[ValueProof, ...] = ()


@dataclass(frozen=True)
class Scope:
    ref: Ref
    parent: Ref | None
    kind: str


@dataclass(frozen=True)
class Operand:
    ref: Ref
    sort: str
    scope: Ref
    dependencies: tuple[Ref, ...] = ()


@dataclass(frozen=True)
class Port:
    ref: Ref
    kind: str
    scope: Ref
    value_type: Type | None = None


@dataclass(frozen=True)
class IndependentLaw:
    """Externally justified complete local law; a tag alone does not prove it."""

    ref: Ref
    kind: str
    subject: Ref
    payload: Type | None
    interface: Ref | None
    external_certificate: Ref


@dataclass(frozen=True)
class Interface:
    ref: Ref
    provider: Ref
    scopes: tuple[Scope, ...]
    operands: tuple[Operand, ...]  # Full nu/K/D/profile/dependency incidence.
    ports: tuple[Port, ...]
    evidence: tuple[Operand, ...]  # Full proof fields, at original scopes.
    law: Ref
    protocol: str = "VP-EchoFixed/1"
    role: str = "Pure"
    entry: str = "Value"
    consumer: str = "ValueResult/InvocationReturn"


@dataclass(frozen=True)
class ContractClause:
    ref: Ref
    kind: str
    scope: Ref
    operands: tuple[Ref, ...]
    law: Ref


@dataclass(frozen=True)
class WholeInlet:
    ref: Ref
    interface: Ref
    payload: Type
    # Every complete contract operand, including all production alternatives,
    # is registered by these exact clauses and their independent complete laws.
    clauses: tuple[ContractClause, ...]
    residuals: tuple[Operand, ...]
    law: Ref
    schema: str = "ValueInletSchema/1"


@dataclass(frozen=True)
class ForeignValueContract:
    ref: Ref
    provider: Ref
    payload: Type
    scope: Ref
    future_ports: tuple[Ref, ...]
    dependencies: tuple[Ref, ...]
    law: Ref


@dataclass(frozen=True)
class PublicImport:
    ref: Ref
    provider: Ref
    payload: Type
    kind: str
    ground_value: object = None
    foreign_contract: Ref | None = None


@dataclass(frozen=True)
class AdmissionAtom:
    ref: Ref
    inlet: Ref
    interface: Ref
    context_port: Ref
    scope: Ref
    value_type: Type
    proof_into_context_port: ValueProof
    # Its independent meaning is membership of the OTHER context value at
    # this registered port. It never tests U acceptance, output safety or Q.
    rule: str = "context_value_membership"


@dataclass(frozen=True)
class PublicRoot:
    ref: Ref
    inlet: Ref
    interface: Ref
    result: Type
    dependency: str  # echo | fixed | any
    evidence_incidence: tuple[Ref, ...]
    admission_atoms: frozenset[Ref] = frozenset()
    fixed_import: Ref | None = None
    fixed_result_proof: ValueProof | None = None
    role: str = "Pure"
    entry: str = "Value"


@dataclass(frozen=True)
class Environment:
    roots: tuple[PublicRoot, ...]
    inlets: tuple[WholeInlet, ...]
    interfaces: tuple[Interface, ...]
    laws: tuple[IndependentLaw, ...]
    imports: tuple[PublicImport, ...] = ()
    foreign_values: tuple[ForeignValueContract, ...] = ()
    admission_atoms: tuple[AdmissionAtom, ...] = ()


@dataclass(frozen=True)
class DirectProof:
    source: PublicRoot
    target: PublicRoot
    # Exact snapshots: stale submitted clauses/incidences are rejected.
    inlet: WholeInlet
    interface: Interface
    output_proof: ValueProof
    fixed_imports: tuple[PublicImport, ...] = ()
    foreign_contracts: tuple[ForeignValueContract, ...] = ()


SCALARS = frozenset({"Unit", "Bool", "Int"})
INLET_CLAUSES = frozenset({"inert", "force", "response", "raw_resume", "future", "guards", "whole_output_image"})
REQUIRED_PORTS = frozenset({"callable", "whole_carrier", "force", "receipt", "formal", "body_result", "outward_result", "future"})


def valid_ref(r: Ref) -> bool:
    return isinstance(r, Ref) and all(
        isinstance(s, str) and bool(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9:._/-]{0,127}", s))
        for s in (r.name, r.epoch)
    )


def valid_type(t: Type, depth: int = 0, budget: list[int] | None = None) -> bool:
    if budget is None:
        budget = [512]
    budget[0] -= 1
    if not isinstance(t, Type) or depth > 24 or budget[0] < 0 or not isinstance(t.args, tuple):
        return False
    if t.tag == "atom":
        return t.name in SCALARS and not t.args
    if t.tag == "any":
        return not t.name and not t.args
    return t.tag == "union" and not t.name and len(t.args) == 2 and all(
        valid_type(c, depth + 1, budget) for c in t.args
    )


def ground_member(value: object, t: Type) -> bool:
    """Exact ground-only membership, used for the finite production separator."""
    if not valid_type(t):
        return False
    if t.tag == "any":
        return value is None or type(value) in (bool, int)
    if t.tag == "union":
        return any(ground_member(value, part) for part in t.args)
    return {"Unit": value is None, "Bool": type(value) is bool, "Int": type(value) is int}[t.name]


def check_value_proof(p: ValueProof, depth: int = 0, budget: list[int] | None = None) -> bool:
    """Finite semantic local proof terms, not composed Function query successes."""
    if budget is None:
        budget = [512]
    budget[0] -= 1
    if not isinstance(p, ValueProof) or depth > 24 or budget[0] < 0:
        return False
    if not (valid_type(p.source) and valid_type(p.target) and isinstance(p.children, tuple)):
        return False
    if not all(check_value_proof(c, depth + 1, budget) for c in p.children):
        return False
    if p.rule == "identity":
        return not p.children and p.source == p.target
    if p.rule == "top":
        return not p.children and p.target == Type("any")
    if p.rule in ("union_left", "union_right"):
        if len(p.children) != 1 or p.target.tag != "union":
            return False
        c = p.children[0]
        return c.source == p.source and c.target == p.target.args[p.rule == "union_right"]
    if p.rule == "union_cases":
        return p.source.tag == "union" and len(p.children) == 2 and all(
            c.source == part and c.target == p.target
            for c, part in zip(p.children, p.source.args, strict=True)
        )
    if p.rule == "compose" and len(p.children) == 2:
        a, b = p.children
        return a.source == p.source and a.target == b.source and b.target == p.target
    return False


def lookup(entries: tuple, ref: Ref):
    return next((entry for entry in entries if entry.ref == ref), None)


def unique(entries: tuple) -> bool:
    return isinstance(entries, tuple) and len(entries) <= 128 and all(
        valid_ref(e.ref) for e in entries
    ) and len({e.ref for e in entries}) == len(entries)


def has_law(env: Environment, ref: Ref, kind: str, subject: Ref,
            payload: Type | None, interface: Ref | None) -> bool:
    law = lookup(env.laws, ref)
    return law is not None and (
        law.kind, law.subject, law.payload, law.interface
    ) == (kind, subject, payload, interface) and valid_ref(law.external_certificate)


def valid_interface(env: Environment, interface: Interface) -> bool:
    if not valid_ref(interface.provider) or (interface.protocol, interface.role, interface.entry, interface.consumer) != (
        "VP-EchoFixed/1", "Pure", "Value", "ValueResult/InvocationReturn"
    ) or not has_law(env, interface.law, "complete_IF", interface.ref, None, interface.ref):
        return False
    if not all(unique(xs) for xs in (interface.scopes, interface.operands, interface.ports, interface.evidence)):
        return False
    scopes: set[Ref] = set()
    ancestors: dict[Ref, set[Ref]] = {}
    for s in interface.scopes:
        if s.kind not in {"base", "type", "view", "event", "proof"} or (
            s.parent is not None and s.parent not in scopes
        ) or (s.parent is None and (scopes or s.kind != "base")):
            return False
        ancestors[s.ref] = {s.ref} | (ancestors[s.parent] if s.parent is not None else set())
        scopes.add(s.ref)
    if not scopes:
        return False
    declared: set[Ref] = set()
    declaration_scopes: dict[Ref, Ref] = {}
    for op in interface.operands + interface.evidence:
        if op.scope not in scopes or op.ref in declared or not set(op.dependencies) <= declared:
            return False
        if op.sort not in {"nu", "K", "D", "profile", "value", "provider", "world", "proof"}:
            return False
        if any(declaration_scopes[dependency] not in ancestors[op.scope] for dependency in op.dependencies):
            return False
        declared.add(op.ref)
        declaration_scopes[op.ref] = op.scope
    if not {"nu", "K", "D", "profile"} <= {o.sort for o in interface.operands}:
        return False
    counts = {kind: sum(p.kind == kind for p in interface.ports) for kind in REQUIRED_PORTS}
    return all(n == 1 for n in counts.values()) and all(
        p.scope in scopes and (p.kind in REQUIRED_PORTS or p.kind == "context_value")
        and ((p.kind == "context_value" and valid_type(p.value_type))
             or (p.kind != "context_value" and p.value_type is None))
        for p in interface.ports
    )


def valid_inlet(env: Environment, inlet: WholeInlet) -> bool:
    interface = lookup(env.interfaces, inlet.interface)
    if interface is None or not valid_type(inlet.payload) or inlet.schema != "ValueInletSchema/1":
        return False
    if not has_law(env, inlet.law, "complete_whole_inlet", inlet.ref, inlet.payload, inlet.interface):
        return False
    if not unique(inlet.clauses) or not unique(inlet.residuals):
        return False
    if {c.kind for c in inlet.clauses} != INLET_CLAUSES or len(inlet.clauses) != len(INLET_CLAUSES):
        return False
    scopes = {s.ref for s in interface.scopes}
    ancestors: dict[Ref, set[Ref]] = {}
    for scope in interface.scopes:
        ancestors[scope.ref] = {scope.ref} | (
            ancestors[scope.parent] if scope.parent is not None else set()
        )
    declaration_scopes = {
        item.ref: item.scope
        for item in interface.operands + interface.evidence + interface.ports
    }
    operands = set(declaration_scopes)
    for r in inlet.residuals:
        if r.scope not in scopes or r.ref in operands or not set(r.dependencies) <= operands:
            return False
        if r.sort not in {"nu", "K", "D", "profile", "proof"}:
            return False
        if any(declaration_scopes[d] not in ancestors[r.scope] for d in r.dependencies):
            return False
        operands.add(r.ref)
        declaration_scopes[r.ref] = r.scope
    return all(c.scope in scopes and c.operands and set(c.operands) <= operands and has_law(
        env, c.law, "whole_inlet_clause:" + c.kind, c.ref, inlet.payload, inlet.interface
    ) for c in inlet.clauses)


def valid_import(env: Environment, item: PublicImport) -> bool:
    if not valid_ref(item.provider) or not valid_type(item.payload):
        return False
    if item.kind == "ground":
        if item.foreign_contract is not None or item.payload.tag != "atom":
            return False
        return {
            "Unit": item.ground_value is None,
            "Bool": type(item.ground_value) is bool,
            "Int": type(item.ground_value) is int,
        }[item.payload.name]
    if item.kind != "foreign" or item.ground_value is not None:
        return False
    c = lookup(env.foreign_values, item.foreign_contract)
    if c is None or (c.provider, c.payload) != (item.provider, item.payload):
        return False
    all_scopes = {s.ref for i in env.interfaces for s in i.scopes}
    all_operands = {o.ref for i in env.interfaces for o in i.operands + i.evidence}
    all_ports = {p.ref for i in env.interfaces for p in i.ports}
    return c.scope in all_scopes and set(c.dependencies) <= all_operands and set(c.future_ports) <= all_ports and has_law(
        env, c.law, "complete_public_value", c.ref, c.payload, None
    )


def valid_atom(env: Environment, atom: AdmissionAtom) -> bool:
    interface = lookup(env.interfaces, atom.interface)
    inlet = lookup(env.inlets, atom.inlet)
    if interface is None or inlet is None or inlet.interface != atom.interface:
        return False
    port = lookup(interface.ports, atom.context_port)
    return atom.rule == "context_value_membership" and port is not None and port.kind == "context_value" and (
        atom.scope == port.scope and valid_type(atom.value_type)
        and atom.proof_into_context_port.source == atom.value_type
        and atom.proof_into_context_port.target == port.value_type
        and check_value_proof(atom.proof_into_context_port)
    )


def valid_root(env: Environment, root: PublicRoot) -> bool:
    inlet = lookup(env.inlets, root.inlet)
    interface = lookup(env.interfaces, root.interface)
    if inlet is None or interface is None or inlet.interface != root.interface:
        return False
    if not root.ref.name.startswith("public:") or not valid_type(root.result):
        return False
    if (root.role, root.entry) != (interface.role, interface.entry):
        return False
    if root.evidence_incidence != tuple(e.ref for e in interface.evidence):
        return False
    if not isinstance(root.admission_atoms, frozenset) or not all(
        (atom := lookup(env.admission_atoms, ref)) is not None and
        (atom.inlet, atom.interface) == (root.inlet, root.interface)
        for ref in root.admission_atoms
    ):
        return False
    if root.dependency == "fixed":
        item = lookup(env.imports, root.fixed_import)
        p = root.fixed_result_proof
        return item is not None and isinstance(p, ValueProof) and (
            p.source == item.payload and p.target == root.result and check_value_proof(p)
        )
    if root.fixed_import is not None or root.fixed_result_proof is not None:
        return False
    return root.dependency == "any" or (root.dependency == "echo" and root.result == inlet.payload)


def valid_environment(env: Environment) -> bool:
    if not isinstance(env, Environment) or not all(unique(xs) for xs in (
        env.roots, env.inlets, env.interfaces, env.laws, env.imports, env.foreign_values, env.admission_atoms
    )):
        return False
    return all(valid_interface(env, i) for i in env.interfaces) and all(
        valid_inlet(env, i) for i in env.inlets
    ) and all(valid_import(env, i) for i in env.imports) and all(
        valid_atom(env, a) for a in env.admission_atoms
    ) and all(valid_root(env, r) for r in env.roots)


def check_direct_fragment(submitted_source: Ref, submitted_target: Ref,
                          env: Environment, proof: DirectProof) -> bool:
    """Conditional rule at these EXACT public operands, with no source access.

    This fragment intentionally rejects changed-I covariance. Equality of the
    COMPLETE inlet contract (all alternatives) and IF/evidence is a premise.
    Typed H only restricts admission; it never narrows production using what
    this carrier happens to return. Output uses SOURCE.result unconditionally.
    """
    if not isinstance(proof, DirectProof) or not valid_environment(env):
        return False
    source = lookup(env.roots, submitted_source)
    target = lookup(env.roots, submitted_target)
    if source is None or target is None or source != proof.source or target != proof.target:
        return False
    if source.inlet != target.inlet or source.interface != target.interface:
        return False
    if proof.inlet != lookup(env.inlets, source.inlet) or proof.interface != lookup(env.interfaces, source.interface):
        return False
    if source.evidence_incidence != target.evidence_incidence:
        return False
    imported_refs = sorted({r.fixed_import for r in (source, target) if r.fixed_import is not None}, key=lambda r: (r.name, r.epoch))
    imports = tuple(lookup(env.imports, ref) for ref in imported_refs)
    foreign_refs = sorted({item.foreign_contract for item in imports if item.foreign_contract is not None}, key=lambda r: (r.name, r.epoch))
    if proof.fixed_imports != imports or proof.foreign_contracts != tuple(lookup(env.foreign_values, ref) for ref in foreign_refs):
        return False
    if not source.admission_atoms <= target.admission_atoms:
        return False
    if target.dependency == "echo" and source.dependency != "echo":
        return False
    if target.dependency == "fixed" and (
        source.dependency != "fixed" or source.fixed_import != target.fixed_import
    ):
        return False
    outgoing = proof.output_proof
    return isinstance(outgoing, ValueProof) and outgoing.source == source.result and (
        outgoing.target == target.result and check_value_proof(outgoing)
    )


def regressions() -> dict:
    R = lambda name: Ref(name, "v1")
    integer, boolean, unit, any_t = Type("atom", name="Int"), Type("atom", name="Bool"), Type("atom", name="Unit"), Type("any")
    refl = lambda t: ValueProof("identity", t, t)
    base, event = R("scope:base"), R("scope:event")
    operands = tuple(Operand(R("field:" + sort), sort, base) for sort in ("nu", "K", "D", "profile"))
    evidence = (Operand(R("proof:entry"), "proof", event, (operands[0].ref,)),)
    ports = tuple(Port(R("port:" + k), k, event) for k in sorted(REQUIRED_PORTS)) + (Port(R("port:other"), "context_value", event, any_t),)
    interface = Interface(R("IF:projection"), R("provider:projection"), (Scope(base, None, "base"), Scope(event, base, "event")), operands, ports, evidence, R("law:IF"))
    laws = [IndependentLaw(interface.law, "complete_IF", interface.ref, None, interface.ref, R("external:IF-proof"))]

    def inlet(name: str, payload: Type) -> WholeInlet:
        ref = R("I:" + name)
        clauses = tuple(ContractClause(R(name + ":" + k), k, event, tuple(p.ref for p in ports), R("law:" + name + ":" + k)) for k in sorted(INLET_CLAUSES))
        for c in clauses:
            laws.append(IndependentLaw(c.law, "whole_inlet_clause:" + c.kind, c.ref, payload, interface.ref, R("external:" + name + ":" + c.kind)))
        law = R("law:I:" + name)
        laws.append(IndependentLaw(law, "complete_whole_inlet", ref, payload, interface.ref, R("external:I:" + name)))
        return WholeInlet(ref, interface.ref, payload, clauses, (), law)

    i_int, i_any = inlet("Int", integer), inlet("Any", any_t)
    incidence = tuple(e.ref for e in evidence)
    echo = PublicRoot(R("public:echo-int"), i_int.ref, interface.ref, integer, "echo", incidence)
    wide = replace(echo, ref=R("public:wide"), result=any_t, dependency="any")
    atom = AdmissionAtom(R("H:other-int"), i_int.ref, interface.ref, ports[-1].ref, event, integer, ValueProof("top", integer, any_t))
    narrow = replace(echo, ref=R("public:echo-H"), admission_atoms=frozenset({atom.ref}))
    broad = replace(echo, ref=R("public:echo-any"), inlet=i_any.ref, result=any_t)
    int_target = replace(wide, ref=R("public:int-target"), result=integer)
    same_any_int_target = replace(int_target, ref=R("public:same-any-int"), inlet=i_any.ref)
    z = PublicImport(R("import:z"), R("provider:z"), integer, "ground", 7)
    pick = replace(echo, ref=R("public:pick"), dependency="fixed", fixed_import=z.ref, fixed_result_proof=refl(integer))
    pick_wide = replace(pick, ref=R("public:pick-wide"), result=any_t, fixed_result_proof=ValueProof("top", integer, any_t))
    env = Environment((echo, wide, narrow, broad, int_target, same_any_int_target, pick, pick_wide), (i_int, i_any), (interface,), tuple(laws), (z,), admission_atoms=(atom,))
    checks: dict[str, bool] = {}

    def proof(s: PublicRoot, t: PublicRoot, out: ValueProof) -> DirectProof:
        refs = sorted({r.fixed_import for r in (s, t) if r.fixed_import is not None}, key=lambda r: (r.name, r.epoch))
        imports = tuple(item for ref in refs if (item := lookup(env.imports, ref)) is not None)
        return DirectProof(s, t, lookup(env.inlets, s.inlet), interface, out, imports)

    def expect(name: str, actual: bool, wanted: bool) -> None:
        checks[name] = actual == wanted
        if actual != wanted:
            raise AssertionError(name)

    p = proof(echo, wide, ValueProof("top", integer, any_t))
    expect("same_complete_I_result_widening", check_direct_fragment(echo.ref, wide.ref, env, p), True)
    expect("same_I_typed_domain_H", check_direct_fragment(echo.ref, narrow.ref, env, proof(echo, narrow, refl(integer))), True)
    expect("same_fixed_import_widening", check_direct_fragment(pick.ref, pick_wide.ref, env, proof(pick, pick_wide, ValueProof("top", integer, any_t))), True)
    expect("lost_H_domain", check_direct_fragment(narrow.ref, echo.ref, env, proof(narrow, echo, refl(integer))), False)
    # Concrete semantic discriminator: the SAME carrier actually returns Int,
    # but source Any's independent full contract permits a Bool Return; Echo
    # preserves that Bool production extra. Its actual Int payload cannot make
    # Any <= Int true or authorize changing the source's complete I to I_Int.
    extra = {"actual_carrier_payload": 7, "licensed_source_production_return": False,
             "source_return_type": "Any", "claimed_target_return_type": "Int"}
    expect("finite_Bool_extra_ground_separator", ground_member(False, any_t) and not ground_member(False, integer) and ground_member(7, integer), True)
    expect("changed_I_Bool_extra_false_proof", check_direct_fragment(broad.ref, int_target.ref, env, proof(broad, int_target, refl(integer))), False)
    expect("same_I_actual_Int_cannot_narrow_Any_output", check_direct_fragment(broad.ref, same_any_int_target.ref, env, proof(broad, same_any_int_target, refl(integer))), False)
    expect("actual_submitted_source", check_direct_fragment(R("source:lambda"), wide.ref, env, p), False)
    expect("wrong_actual_target", check_direct_fragment(echo.ref, echo.ref, env, p), False)
    stale_root = replace(echo, dependency="any")
    stale_env = replace(env, roots=(stale_root,) + env.roots[1:])
    expect("stale_root_equations", check_direct_fragment(echo.ref, wide.ref, stale_env, p), False)
    changed_if = replace(interface, evidence=(replace(evidence[0], dependencies=(operands[1].ref,)),))
    expect("stale_full_evidence_incidence", check_direct_fragment(echo.ref, wide.ref, replace(env, interfaces=(changed_if,)), p), False)
    bad_residual = Operand(R("residual:bad-base"), "proof", base, (evidence[0].ref,))
    expect("base_residual_cannot_read_event_proof", valid_inlet(env, replace(i_int, residuals=(bad_residual,))), False)
    first_residual = Operand(R("residual:event"), "proof", event, (operands[0].ref,))
    later_base = Operand(R("residual:later-base"), "proof", base, (first_residual.ref,))
    expect("prior_residual_scope_is_not_hoisted", valid_inlet(env, replace(i_int, residuals=(first_residual, later_base))), False)
    oracle = proof(echo, wide, ValueProof("semantic_inclusion", integer, any_t))
    expect("unsupported_oracle", check_direct_fragment(echo.ref, wide.ref, env, oracle), False)
    expect("fake_scalar_atom", valid_type(Type("atom", name="ImaginarySafe")), False)
    fake_result = replace(wide, result=Type("atom", name="ImaginarySafe"))
    expect("invalid_public_result_type", check_direct_fragment(echo.ref, fake_result.ref, replace(env, roots=(echo, fake_result) + env.roots[2:]), proof(echo, fake_result, ValueProof("top", integer, any_t))), False)
    expect("invalid_Int_Bool_inclusion", check_value_proof(ValueProof("identity", integer, boolean)), False)
    bad_import = replace(z, payload=boolean)  # 7 is not a Bool constructor.
    expect("fake_fixed_import_payload", check_direct_fragment(echo.ref, wide.ref, replace(env, imports=(bad_import,)), p), False)
    fake_pick = replace(pick, fixed_import=R("import:unregistered"))
    bad_env = replace(env, roots=env.roots[:-2] + (fake_pick, pick_wide))
    expect("unregistered_fixed_import", check_direct_fragment(fake_pick.ref, pick_wide.ref, bad_env, proof(fake_pick, pick_wide, ValueProof("top", integer, any_t))), False)
    fake_atom = replace(atom, ref=R("H:fake"), context_port=R("port:unregistered"))
    expect("invalid_registered_admission_atom", check_direct_fragment(echo.ref, wide.ref, replace(env, admission_atoms=(fake_atom,)), p), False)
    unknown_H = replace(narrow, admission_atoms=frozenset({R("H:unregistered")}))
    expect("unregistered_H_string", check_direct_fragment(echo.ref, unknown_H.ref, replace(env, roots=(echo, wide, unknown_H) + env.roots[3:]), proof(echo, unknown_H, refl(integer))), False)
    wrong_role = replace(wide, role="Handler")
    expect("invalid_role", check_direct_fragment(echo.ref, wrong_role.ref, replace(env, roots=(echo, wrong_role) + env.roots[2:]), proof(echo, wrong_role, ValueProof("top", integer, any_t))), False)
    wrong_entry = replace(wide, entry="Computation")
    expect("invalid_entry", check_direct_fragment(echo.ref, wrong_entry.ref, replace(env, roots=(echo, wrong_entry) + env.roots[2:]), proof(echo, wrong_entry, ValueProof("top", integer, any_t))), False)
    foreign_fake = replace(z, kind="foreign", ground_value=None, foreign_contract=R("foreign:missing"))
    expect("foreign_requires_explicit_independent_contract", check_direct_fragment(echo.ref, wide.ref, replace(env, imports=(foreign_fake,)), p), False)
    foreign_contract = ForeignValueContract(R("foreign:z"), z.provider, integer, base, (), (), R("law:foreign-z"))
    foreign_law = IndependentLaw(foreign_contract.law, "complete_public_value", foreign_contract.ref, integer, None, R("external:foreign-z-proof"))
    foreign_item = replace(foreign_fake, foreign_contract=foreign_contract.ref)
    foreign_env = replace(env, imports=(foreign_item,), foreign_values=(foreign_contract,), laws=env.laws + (foreign_law,))
    foreign_proof = replace(proof(pick, pick_wide, ValueProof("top", integer, any_t)), fixed_imports=(foreign_item,), foreign_contracts=(foreign_contract,))
    expect("foreign_contract_explicit_conditional_premise", check_direct_fragment(pick.ref, pick_wide.ref, foreign_env, foreign_proof), True)
    stale_import_env = replace(env, imports=(replace(z, ground_value=8),))
    expect("stale_actual_fixed_import", check_direct_fragment(pick.ref, pick_wide.ref, stale_import_env, proof(pick, pick_wide, ValueProof("top", integer, any_t))), False)
    no_echo = replace(echo, ref=R("public:no-echo"), dependency="any")
    expect("Echo_dependency_required", check_direct_fragment(no_echo.ref, echo.ref, replace(env, roots=(no_echo,) + env.roots), proof(no_echo, echo, refl(integer))), False)
    either = Type("union", (integer, boolean))
    union = replace(wide, ref=R("public:union"), result=either)
    union_env = replace(env, roots=env.roots + (union,))
    union_out = ValueProof("union_left", integer, either, (refl(integer),))
    expect("same_I_union_result", check_direct_fragment(echo.ref, union.ref, union_env, proof(echo, union, union_out)), True)
    expect("Compose_retained", check_value_proof(ValueProof("compose", integer, any_t, (refl(integer), ValueProof("top", integer, any_t)))), True)
    return {"claim": "conditional_native_Direct_fragment_consistency", "checks": len(checks),
            "passed": sum(checks.values()), "environment_laws": "independent semantic premises, not established by this run",
            "changed_I_counterexample": extra}


if __name__ == "__main__":
    print(json.dumps(regressions(), sort_keys=True))
