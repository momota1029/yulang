#!/usr/bin/env python3
"""Research-only decision kernel for finite id/pick *boundary arithmetic*.

This is proof-producing search, not recognition of supplied proof flags. It
does not implement source Call, complete Function semantics, worlds, W/Z/J/Car,
runtime effects, or current compiler correspondence. The only Function input
is a static whole-result boundary at the SAME already selected inlet/frame.
It is never an annotation on a value after Call. Native semantic justification
of reducing that boundary to the arithmetic here is a separate theorem.

JSON types: "Unit", "Bool", "Int", "Any", {"Union": [T, ...]}, or
{"Record": [["label", T], ...]}. Unions must be nonempty. Record labels are
unique and mandatory; the empty record is permitted. No other types occur.
Example problem (read JSON from stdin, or from the single path argument):
  {"frames": [{"key": "new-0", "kind": "id"}],
   "handles": {"f": "new-0", "alias": "new-0"},
   "lowers": [{"handle": "f", "type": "Int"}],
   "views": [{"handle": "alias", "boundary": "same-inlet-function-result",
              "type": "Any"}]}
Pick frames additionally have a "capture" type, a tight ground/record tree
with no union or Any anywhere. Each frame has at least one lower. Previously
fixed A frames are unsupported: this kernel never reselects an earlier frame.
The finite arithmetic corresponds only to sections 4--5 of the research
theorem notes/theory/2026-10-08-source-directed-joint-decision.md. That theorem's
data graph, source-owned DataArg/Car, caller/world and symbolic strategy
construction are NOT inputs or outputs encoded by this file.

Termination: parsing descends finite acyclic input, normalization descends
type trees and enumerates finite Cartesian products, and atomic checking
descends record fields. Inclusion visits the finite left x right atom matrix.
Each frame chooses A once and all routed constraints are checked in one solve.
DNF expansion can be exponential; this small reference has no production
resource claim. Python depth exhaustion is UNSUPPORTED, never UNSAT.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


GROUNDS = frozenset(("Unit", "Bool", "Int", "Any"))
BOUNDARY = "same-inlet-function-result"


class Unsupported(ValueError):
    """Malformed or out-of-fragment input, distinguished from a false constraint."""


@dataclass(frozen=True)
class Type:
    tag: str
    members: tuple[Type, ...] = ()
    fields: tuple[tuple[str, Type], ...] = ()


def parse_type(raw: Any, path: str = "type", active: set[int] | None = None) -> Type:
    """Validate the entire tree before solving, including Python cyclic inputs."""
    if isinstance(raw, str):
        if raw in GROUNDS:
            return Type(raw)
        raise Unsupported(f"{path}: unknown type {raw!r}")
    if not isinstance(raw, dict) or len(raw) != 1:
        raise Unsupported(f"{path}: expected a ground, Union or Record")
    active = set() if active is None else active
    if id(raw) in active:
        raise Unsupported(f"{path}: cyclic type")
    active.add(id(raw))
    try:
        if "Union" in raw:
            items = raw["Union"]
            if not isinstance(items, list) or not items:
                raise Unsupported(f"{path}: Union must be a nonempty list")
            return Type("Union", tuple(parse_type(x, f"{path}.Union[{i}]", active)
                                       for i, x in enumerate(items)))
        if "Record" in raw:
            items = raw["Record"]
            if not isinstance(items, list):
                raise Unsupported(f"{path}: Record must be a label/type pair list")
            fields = []
            labels: set[str] = set()
            for i, pair in enumerate(items):
                if (not isinstance(pair, list) or len(pair) != 2
                        or not isinstance(pair[0], str)):
                    raise Unsupported(f"{path}.Record[{i}]: expected [label, type]")
                label, child = pair
                if label in labels:
                    raise Unsupported(f"{path}: duplicate mandatory label {label!r}")
                labels.add(label)
                fields.append((label, parse_type(child, f"{path}.{label}", active)))
            return Type("Record", fields=tuple(sorted(fields)))
        raise Unsupported(f"{path}: unsupported constructor")
    finally:
        active.remove(id(raw))


def encode_type(typ: Type) -> Any:
    if typ.tag == "Union":
        return {"Union": [encode_type(x) for x in typ.members]}
    if typ.tag == "Record":
        return {"Record": [[label, encode_type(x)] for label, x in typ.fields]}
    return typ.tag


def normalize(typ: Type) -> tuple[Type, ...]:
    """Finite DNF, with field unions distributed even in nested records.

    Atoms reuse Type, but have no Union nodes anywhere. Deduplication preserves
    traversal order and does not delete smaller atoms or replace unions by Any.
    """
    if typ.tag == "Union":
        atoms = (a for member in typ.members for a in normalize(member))
    elif typ.tag == "Record":
        choices = [normalize(child) for _, child in typ.fields]
        atoms = (Type("Record", fields=tuple((label, child)
                  for (label, _), child in zip(typ.fields, combo)))
                 for combo in itertools.product(*choices))
    else:
        return (typ,)
    return tuple(dict.fromkeys(atoms))


def atomic_proof(left: Type, right: Type) -> dict[str, Any] | None:
    """Atomic inclusion with finite ground/top/record proof trees."""
    if right.tag == "Any":
        return {"rule": "top"}
    if left.tag in GROUNDS:
        return {"rule": "ground", "ground": left.tag} if left.tag == right.tag else None
    if left.tag != "Record" or right.tag != "Record":
        return None
    available = dict(left.fields)
    premises = []
    for label, target in right.fields:
        if label not in available:
            return None
        proof = atomic_proof(available[label], target)
        if proof is None:
            return None
        premises.append({"label": label, "proof": proof})
    return {"rule": "record-width-depth", "fields": premises}


def normalization_proof(typ: Type) -> dict[str, Any]:
    """Finite distributivity schema, interpreted in both directions.

    Union cases/injections flatten a union; record field cases/injections
    distribute its finite Cartesian product on the same field tuple. The
    result atom lists of the outer dnf-inclusion node fix every product arm.
    This structural derivation is generated, never supplied as an input flag.
    """
    if typ.tag == "Union":
        return {"rule": "union-flatten", "members": [normalization_proof(x) for x in typ.members]}
    if typ.tag == "Record":
        return {"rule": "record-field-distribute", "fields": [
            {"label": label, "proof": normalization_proof(child)} for label, child in typ.fields]}
    return {"rule": "atom-identity", "ground": typ.tag}


def characteristic(atom: Type) -> dict[str, Any]:
    """One structural separator for an atom, using exact record fields."""
    if atom.tag == "Record":
        return {"kind": "record", "fields": {
            label: characteristic(child) for label, child in atom.fields}}
    if atom.tag == "Any":
        return {"kind": "native-function-marker"}
    if atom.tag == "Unit":
        return {"kind": "unit"}
    if atom.tag == "Bool":
        return {"kind": "bool", "value": False}
    if atom.tag == "Int":
        return {"kind": "int", "value": 0}
    raise RuntimeError("characteristic requires a normalized atom")


def member(value: dict[str, Any], typ: Type) -> bool:
    """Independent evaluator on ORIGINAL types; no DNF or inclusion calls.

    Values are this reference's tagged structural values, not actual native
    runtime objects. The function marker belongs only to Any in this grammar.
    """
    if typ.tag == "Any":
        return True
    if typ.tag == "Union":
        return any(member(value, child) for child in typ.members)
    if typ.tag == "Record":
        if value["kind"] != "record":
            return False
        fields = value["fields"]
        return all(label in fields and member(fields[label], child)
                   for label, child in typ.fields)
    return value["kind"] == {"Unit": "unit", "Bool": "bool", "Int": "int"}[typ.tag]


def inclusion(left: Type, right: Type) -> dict[str, Any]:
    left_atoms, right_atoms = normalize(left), normalize(right)
    branches = []
    for i, source in enumerate(left_atoms):
        for j, target in enumerate(right_atoms):
            proof = atomic_proof(source, target)
            if proof is not None:
                branches.append({"source_index": i, "target_index": j, "proof": proof})
                break
        else:
            value = characteristic(source)
            # Validate the constructive separator independently, on original
            # undistributed types. This finite check is not a semantic oracle.
            if not member(value, left) or member(value, right):
                raise RuntimeError("internal countervalue invariant failed")
            return {"included": False, "countervalue": value,
                    "uncovered_atom": encode_type(source), "source_index": i}
    return {"included": True, "proof": {"rule": "dnf-inclusion",
            "source_normalization": normalization_proof(left),
            "target_normalization": normalization_proof(right),
            "source_atoms": [encode_type(x) for x in left_atoms],
            "target_atoms": [encode_type(x) for x in right_atoms],
            "branches": branches}}


def tight(typ: Type) -> bool:
    return typ.tag in ("Unit", "Bool", "Int") or (
        typ.tag == "Record" and all(tight(x) for _, x in typ.fields))


def exact_keys(obj: Any, required: set[str], optional: set[str], path: str) -> None:
    if not isinstance(obj, dict) or not required <= obj.keys() or obj.keys() - required - optional:
        raise Unsupported(f"{path}: expected keys {sorted(required)}, optional {sorted(optional)}")


def unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Do not silently overwrite a duplicate handle/frame/property in JSON."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise Unsupported(f"JSON object has duplicate key {key!r}")
        result[key] = value
    return result


@dataclass(frozen=True)
class Frame:
    key: str
    kind: str
    capture: Type | None


@dataclass(frozen=True)
class Constraint:
    handle: str
    frame: str
    typ: Type


def parse_problem(raw: Any) -> tuple[list[Frame], dict[str, str], list[Constraint], list[Constraint]]:
    exact_keys(raw, {"frames", "handles", "lowers", "views"}, set(), "problem")
    if not isinstance(raw["frames"], list) or not raw["frames"]:
        raise Unsupported("frames: expected a nonempty list")
    frames = []
    keys: set[str] = set()
    for i, obj in enumerate(raw["frames"]):
        path = f"frames[{i}]"
        exact_keys(obj, {"key", "kind"}, {"capture"}, path)
        key = obj["key"]
        if not isinstance(key, str) or not key or key in keys:
            raise Unsupported(f"{path}: frame key must be nonempty and unique")
        keys.add(key)
        kind = obj["kind"]
        if kind not in ("id", "pick"):
            raise Unsupported(f"{path}: only native id/pick boundary kinds supported")
        if (kind == "pick") != ("capture" in obj):
            raise Unsupported(f"{path}: exactly pick frames require capture")
        capture = parse_type(obj["capture"], f"{path}.capture") if kind == "pick" else None
        if capture is not None and not tight(capture):
            raise Unsupported(f"{path}: capture must be tight ground/record without Any or Union")
        frames.append(Frame(key, kind, capture))
    handles = raw["handles"]
    if not isinstance(handles, dict):
        raise Unsupported("handles: expected explicit handle-to-frame object")
    for handle, key in handles.items():
        if not isinstance(handle, str) or not handle or not isinstance(key, str) or key not in keys:
            raise Unsupported("handles: every nonempty handle must route to an existing frame key")
    result: list[list[Constraint]] = []
    for name in ("lowers", "views"):
        if not isinstance(raw[name], list):
            raise Unsupported(f"{name}: expected list")
        constraints = []
        for i, obj in enumerate(raw[name]):
            path = f"{name}[{i}]"
            required = {"handle", "type"} | ({"boundary"} if name == "views" else set())
            exact_keys(obj, required, set(), path)
            handle = obj["handle"]
            if not isinstance(handle, str) or handle not in handles:
                raise Unsupported(f"{path}: unknown handle")
            if name == "views" and obj["boundary"] != BOUNDARY:
                raise Unsupported(f"{path}: only whole same-inlet Function-result boundaries supported")
            constraints.append(Constraint(handle, handles[handle], parse_type(obj["type"], f"{path}.type")))
        result.append(constraints)
    lowers, views = result
    for frame in frames:
        if not any(c.frame == frame.key for c in lowers):
            raise Unsupported(f"frame {frame.key!r}: at least one lower required")
    return frames, dict(handles), lowers, views


def solve(raw: Any) -> dict[str, Any]:
    """Decide all supported constraints; unsupported inputs are never UNSAT."""
    try:
        frames, handles, lowers, views = parse_problem(raw)
        chosen: dict[str, Type] = {}
        assignments = {}
        for frame in frames:
            # One least A, shared by all aliases, chosen before any checks.
            atoms = normalize(Type("Union", tuple(c.typ for c in lowers if c.frame == frame.key)))
            chosen[frame.key] = atoms[0] if len(atoms) == 1 else Type("Union", atoms)
            assignments[frame.key] = {"kind": frame.kind, "A": encode_type(chosen[frame.key]),
                                      "selection": "least-lower-union"}
            if frame.capture is not None:
                assignments[frame.key]["B"] = encode_type(frame.capture)
        proofs = []
        for frame in frames:
            obligations = [("lower", c, c.typ, chosen[frame.key]) for c in lowers if c.frame == frame.key]
            output = chosen[frame.key] if frame.kind == "id" else frame.capture
            assert output is not None
            obligations += [("whole-result-view", c, output, c.typ) for c in views if c.frame == frame.key]
            for role, constraint, left, right in obligations:
                result = inclusion(left, right)
                evidence = {"role": role, "frame": frame.key, "handle": constraint.handle,
                            "left": encode_type(left), "right": encode_type(right), **result}
                if not result["included"]:
                    return {"status": "UNSAT", "scope": "finite-boundary-arithmetic",
                            "handles": handles, "candidate_assignments": assignments,
                            "failure": evidence,
                            "necessity": "least-lower-union" if frame.kind == "id" else "fixed-tight-capture"}
                proofs.append(evidence)
        return {"status": "SAT", "scope": "finite-boundary-arithmetic",
                "handles": handles, "assignments": assignments, "proofs": proofs}
    except (Unsupported, RecursionError) as error:
        return {"status": "UNSUPPORTED", "reason": str(error) or "Python structural depth exhausted"}


def serialize_result(result: dict[str, Any]) -> str:
    """Finish serialization before publication, including depth rejection."""
    try:
        return json.dumps(result, sort_keys=True, indent=2)
    except RecursionError:
        return json.dumps({"status": "UNSUPPORTED", "reason": "Python output depth exhausted"},
                          sort_keys=True, indent=2)


def self_test() -> dict[str, Any]:
    def record(**fields: Any) -> Any:
        return {"Record": [[k, v] for k, v in fields.items()]}

    def union(*members: Any) -> Any:
        return {"Union": list(members)}

    def problem(frames: list[dict[str, Any]], handles: dict[str, str],
                lowers: list[tuple[str, Any]], views: list[tuple[str, Any]]) -> Any:
        return {"frames": frames, "handles": handles,
                "lowers": [{"handle": h, "type": t} for h, t in lowers],
                "views": [{"handle": h, "type": t, "boundary": BOUNDARY} for h, t in views]}

    checks = 0
    def expect(raw: Any, status: str) -> dict[str, Any]:
        nonlocal checks
        result = solve(raw)
        assert result["status"] == status, (raw, result, status)
        if status == "UNSAT":
            failure = result["failure"]
            assert member(failure["countervalue"], parse_type(failure["left"]))
            assert not member(failure["countervalue"], parse_type(failure["right"]))
        checks += 1
        return result

    aliased = problem([{"key": "new0", "kind": "id"}], {"f": "new0", "g": "new0"},
                      [("f", "Int"), ("g", "Bool")], [("f", "Int"), ("g", "Bool")])
    expect(aliased, "UNSAT")
    independent = problem([{"key": "new0", "kind": "id"}, {"key": "new1", "kind": "id"}],
                          {"f": "new0", "g": "new1"}, [("f", "Int"), ("g", "Bool")],
                          [("f", "Int"), ("g", "Bool")])
    separated = expect(independent, "SAT")
    assert separated["assignments"]["new0"]["A"] == "Int"
    assert separated["assignments"]["new1"]["A"] == "Bool"
    aliased["views"] = [{"handle": "g", "type": union("Int", "Bool"), "boundary": BOUNDARY}]
    both = expect(aliased, "SAT")
    assert both["assignments"]["new0"]["A"] == union("Int", "Bool")
    broad = problem([{"key": "n", "kind": "id"}], {"f": "n"}, [("f", "Any")], [("f", "Int")])
    assert expect(broad, "UNSAT")["failure"]["countervalue"]["kind"] == "native-function-marker"
    broad["views"] = [{"handle": "f", "type": "Any", "boundary": BOUNDARY}]
    expect(broad, "SAT")
    width = problem([{"key": "n", "kind": "id"}], {"f": "n"},
                    [("f", record(x=union("Int", "Bool"), y=record(z="Int")))],
                    [("f", record(x=union("Int", "Bool"))), ("f", record(y=record(z="Any")))])
    expect(width, "SAT")
    width["views"].append({"handle": "f", "type": record(x="Int"), "boundary": BOUNDARY})
    expect(width, "UNSAT")
    pick = problem([{"key": "n", "kind": "pick", "capture": record(x="Int", y="Bool")}],
                   {"f": "n"}, [("f", "Any")], [("f", record(x="Any"))])
    captured = expect(pick, "SAT")
    assert captured["assignments"]["n"]["A"] == "Any"
    assert captured["assignments"]["n"]["B"] == record(x="Int", y="Bool")
    pick["views"] = [{"handle": "f", "type": "Bool", "boundary": BOUNDARY}]
    expect(pick, "UNSAT")
    for capture in ("Any", union("Int", "Bool"), record(x="Any"), record(x=union("Int"))):
        pick["frames"][0]["capture"] = capture
        expect(pick, "UNSUPPORTED")
    fixed = problem([{"key": "n", "kind": "id", "fixed": "Any"}], {"f": "n"},
                    [("f", "Int")], [("f", "Int")])
    expect(fixed, "UNSUPPORTED")
    fixed["frames"][0]["fixed"] = "Bool"
    expect(fixed, "UNSUPPORTED")
    fixed["frames"][0]["fixed"] = union("Int", "Bool")
    fixed["views"] = [{"handle": "f", "type": "Any", "boundary": BOUNDARY}]
    expect(fixed, "UNSUPPORTED")
    fixed_pick = problem([{"key": "n", "kind": "pick", "fixed": "Any", "capture": "Int"}],
                         {"f": "n"}, [("f", "Bool")], [("f", "Int")])
    expect(fixed_pick, "UNSUPPORTED")
    fixed_pick["frames"][0]["fixed"] = "Int"
    expect(fixed_pick, "UNSUPPORTED")
    for bad in ("Bottom", {"Union": []}, {"Function": ["Int", "Int"]},
                {"Intersection": ["Int", "Bool"]}, {"Record": [["x", "Int"], ["x", "Bool"]]}):
        broad["lowers"][0]["type"] = bad
        expect(broad, "UNSUPPORTED")
    broad["lowers"][0]["type"] = "Any"
    broad["views"][0]["boundary"] = "post-call-value-annotation"
    expect(broad, "UNSUPPORTED")
    broad["views"][0]["boundary"] = BOUNDARY
    broad["views"][0]["proof_flag"] = True
    expect(broad, "UNSUPPORTED")
    # Reject an unsupported later view before an earlier arithmetic failure.
    broad["views"] = [{"handle": "f", "type": "Int", "boundary": BOUNDARY},
                      {"handle": "f", "type": "Bottom", "boundary": BOUNDARY}]
    expect(broad, "UNSUPPORTED")
    broad["views"] = []
    broad["lowers"] = []
    expect(broad, "UNSUPPORTED")
    cyclic: dict[str, Any] = {"Union": []}
    cyclic["Union"].append(cyclic)
    broad["lowers"] = [{"handle": "f", "type": cyclic}]
    expect(broad, "UNSUPPORTED")
    try:
        json.loads('{"f":"new0","f":"new1"}', object_pairs_hook=unique_json_object)
    except Unsupported:
        checks += 1
    else:
        raise AssertionError("duplicate JSON handle silently overwritten")

    # A generated proof can exceed output depth even when solving succeeded.
    # Check the publication boundary independently of the input JSON decoder.
    deep_result: dict[str, Any] = {"status": "SAT", "proof": {}}
    cursor = deep_result["proof"]
    for _ in range(sys.getrecursionlimit() + 10):
        child: dict[str, Any] = {}
        cursor["child"] = child
        cursor = child
    assert json.loads(serialize_result(deep_result)) == {
        "status": "UNSUPPORTED", "reason": "Python output depth exhausted"}
    assert json.loads(serialize_result({"status": "SAT"})) == {"status": "SAT"}
    checks += 1

    raw_types = ["Unit", "Bool", "Int", "Any", union("Int", "Bool"), union("Int", "Any"),
                 union("Bool", "Unit"), record(), record(x="Int"), record(x="Bool"),
                 record(x="Any"), record(x=union("Int", "Bool")), record(y="Int"),
                 record(x="Int", y="Bool"), record(x=record(y="Int")),
                 record(x=record(y=union("Int", "Bool"))),
                 record(x=union("Int", "Bool"), y=union("Unit", "Int")),
                 union(record(x="Int"), record(x="Bool")),
                 union(record(x="Int"), "Bool"), record(x=record(y="Any"))]
    types = [parse_type(x) for x in raw_types]
    # A separately constructed finite test universe (not a completeness proof).
    values = [{"kind": "unit"}, {"kind": "bool", "value": False},
              {"kind": "bool", "value": True}, {"kind": "int", "value": 0},
              {"kind": "int", "value": 1}, {"kind": "native-function-marker"},
              {"kind": "record", "fields": {}}]
    base = list(values)
    values += [{"kind": "record", "fields": {label: value}}
               for label in ("x", "y", "extra") for value in base]
    values += [{"kind": "record", "fields": {"x": a, "y": b}}
               for a, b in itertools.product(base, repeat=2)]
    values += [{"kind": "record", "fields": {"x": {"kind": "record", "fields": {"y": value}}}}
               for value in base]
    countervalues = 0
    membership_checks = 0
    for left, right in itertools.product(types, repeat=2):
        decided = inclusion(left, right)
        # Evaluate the entire reported sample grid, including negative pairs.
        observed = all([not member(value, left) or member(value, right) for value in values])
        assert decided["included"] == observed, (encode_type(left), encode_type(right), decided)
        membership_checks += len(values)
        if not decided["included"]:
            countervalues += 1
            assert member(decided["countervalue"], left)
            assert not member(decided["countervalue"], right)
    # Explicitly require four Cartesian arms, and one nested distribution.
    assert len(normalize(types[16])) == 4
    assert len(normalize(types[15])) == 2
    return {"status": "PASS", "scenario_checks": checks, "inclusion_pairs": len(types) ** 2,
            "validated_countervalues": countervalues, "sample_values": len(values),
            "sample_membership_implications": membership_checks,
            "claim": "bounded executable evidence, not a mathematical proof or compiler conformance"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("input", nargs="?", type=Path, help="JSON file; omitted reads stdin")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = self_test()
    else:
        try:
            if args.input is None:
                raw = json.load(sys.stdin, object_pairs_hook=unique_json_object)
            else:
                with args.input.open(encoding="utf-8") as stream:
                    raw = json.load(stream, object_pairs_hook=unique_json_object)
            result = solve(raw)
        except (OSError, ValueError, RecursionError) as error:
            result = {"status": "UNSUPPORTED", "reason": str(error)}
    print(serialize_result(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
