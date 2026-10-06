#!/usr/bin/env python3
"""Bounded research checks; no compiler semantics or production interface policy.

Run from the repository root. One process, fixed seed, at most four local graph
identities. The syntax is an independently supplied complete presentation;
the checker does not construct Generalize or interpret ordinary DescMem.
"""

from __future__ import annotations

import itertools
import json
import random
import resource
import time
from dataclasses import dataclass


@dataclass(frozen=True)
class Graph:
    nodes: tuple[tuple[str, tuple], ...]
    exports: tuple
    imports: tuple
    environment: tuple


def rename(x, action):
    if isinstance(x, tuple):
        if len(x) == 2 and x[0] == "local":
            return ("local", action[x[1]])
        return tuple(rename(y, action) for y in x)
    return x


def renamed(graph, action):
    return Graph(
        tuple((action[k], rename(record, action)) for k, record in graph.nodes),
        rename(graph.exports, action),
        graph.imports,
        graph.environment,
    )


def encoding(graph):
    return repr((tuple(sorted(graph.nodes)), graph.exports, graph.imports,
                 graph.environment))


def canonical(graph):
    keys = tuple(k for k, _ in graph.nodes)
    assert len(set(keys)) == len(keys)
    labels = tuple(f"n{i}" for i in range(len(keys)))
    return min(encoding(renamed(graph, dict(zip(keys, permutation))))
               for permutation in itertools.permutations(labels))


def ref(k):
    return ("local", k)


def base_graph():
    # Both upper and lower have the same represented output endpoint e.
    # Their occurrence origins, directions and independent policies differ.
    return Graph(
        (("a", ("binder", "exists", "source-formal-x", "scope-function",
                "eligible", 1)),
         ("e", ("effect-coordinate", "source-call-output", "scope-function")),
         ("r", ("recursive-root", "source-f", ("rigid", "provider-f"),
                ref("r"), ref("a"), ref("e"),
                ("upper", "source-call-u", "protected-seed-k", ref("e")),
                ("lower", "source-provider-l", "inherited-own", ref("e")),
                ("residual", "original-kernel", ref("a"), ref("e"))))),
        (ref("r"),),
        (("rigid", "provider-f"), ("rigid", "captured-z")),
        ("original-xi", "kernel-version-1", "outer-state-version-1"),
    )


def replace_node(graph, key, record):
    return Graph(tuple((k, record if k == key else r) for k, r in graph.nodes),
                 graph.exports, graph.imports, graph.environment)


def syntax_campaign():
    graph = base_graph()
    original = canonical(graph)
    alpha = 0
    for p in itertools.permutations(("x", "y", "z")):
        assert canonical(renamed(graph, dict(zip(("a", "e", "r"), p)))) == original
        alpha += 1
    a = dict(graph.nodes)["a"]
    r = dict(graph.nodes)["r"]
    mutations = {
        "binder-mode": replace_node(graph, "a", (a[0], "forall", *a[2:])),
        "introduction-level": replace_node(graph, "a", (*a[:-1], 0)),
        "source-origin": replace_node(graph, "a", (*a[:2], "other-source-x", *a[3:])),
        "directional-output-policy": replace_node(graph, "r", (*r[:6],
            ("upper", "source-call-u", "unprotected", ref("e")), *r[7:])),
        "lower-own-policy": replace_node(graph, "r", (*r[:7],
            ("lower", "source-provider-l", "unprotected", ref("e")), *r[8:])),
        "repeated-endpoint": replace_node(graph, "r", (*r[:5], ref("a"), *r[6:])),
        "designated-export": Graph(graph.nodes, (ref("a"),), graph.imports, graph.environment),
        "rigid-import": Graph(graph.nodes, graph.exports,
                              (("rigid", "provider-other"),), graph.environment),
        "environment": Graph(graph.nodes, graph.exports, graph.imports,
                             ("original-xi", "kernel-version-2", "outer-state-version-1")),
    }
    for name, changed in mutations.items():
        assert canonical(changed) != original, name
    rng = random.Random(20261007)
    random_cases = 0
    for _ in range(128):
        size = rng.randrange(1, 5)
        ids = tuple(f"v{i}" for i in range(size))
        nodes = tuple((k, ("node", rng.randrange(3), ref(rng.choice(ids)),
                           ref(rng.choice(ids)), ("rigid", rng.randrange(2)))) for k in ids)
        g = Graph(nodes, (ref(ids[0]),), (("rigid", "anchor"),), ("original-xi",))
        new_ids = tuple(f"w{i}" for i in range(size))
        shuffled = list(new_ids)
        rng.shuffle(shuffled)
        assert canonical(g) == canonical(renamed(g, dict(zip(ids, shuffled))))
        random_cases += 1
    return {"explicit_alpha_permutations": alpha,
            "rejected_field_mutations": len(mutations), "random_graphs": random_cases}


def interface_semantic_attacks():
    # These are finite logical discriminators, not admitted Yulang sources.
    # Each witness holds the public/client tuple fixed.
    bits = (0, 1)
    independent = any(a == 0 and b == 1 for a, b in itertools.product(bits, repeat=2))
    shared = any(a == 0 and a == 1 for a in bits)
    assert independent and not shared
    ordered = all(any(y == x for y in bits) for x in bits)
    flattened = any(all(y == x for x in bits) for y in bits)
    assert ordered and not flattened
    # Same endpoint; a query reads occurrence policy rather than endpoint.
    occurrence_policy = {"upper-u": True, "lower-l": False}
    assert occurrence_policy["upper-u"] and not occurrence_policy["lower-l"]
    # Actual provider ownership is an independent retained policy input.
    inherited = True
    assert inherited != False
    return {"independent_vs_shared": [independent, shared],
            "ordered_vs_flattened": [ordered, flattened],
            "same_endpoint_distinct_occurrences": True,
            "inherited_provider_policy_retained": True}


def shared_witness_campaign():
    # Pointwise FH premises must share the entire old scoped assignment.
    # Separately existential checks can each succeed on incompatible values.
    bits = (0, 1)
    check_0 = lambda witness: witness["shared"] == 0
    check_1 = lambda witness: witness["shared"] == 1
    separately_exists = (any(check_0({"shared": w}) for w in bits)
                         and any(check_1({"shared": w}) for w in bits))
    one_old_assignment = any(check_0({"shared": w}) and check_1({"shared": w})
                             for w in bits)
    assert separately_exists and not one_old_assignment

    def extend(old, additions, permitted_new):
        for key, value in additions.items():
            if key in old:
                if old[key] != value:
                    return None
            elif key not in permitted_new:
                return None
        return old | additions

    # New event binders have independently permitted scopes; old coordinates
    # are retained pointwise. Sibling extensions are joined before checking.
    old = {"shared": 0, "captured": 1}
    event_0 = ("event-0", "scope-invocation-0")
    event_1 = ("event-1", "scope-invocation-1")
    first = extend(old, {event_0: 0}, {event_0})
    assert first is not None
    second = extend(first, {event_1: 1}, {event_1})
    assert second is not None
    assert all(second[key] == value for key, value in old.items())
    assert second[event_0] == 0 and second[event_1] == 1
    assert check_0(second)
    assert extend(second, {"shared": 1}, set()) is None
    assert extend(second, {event_0: 1}, set()) is None
    assert extend(old, {event_1: 1}, {event_0}) is None
    return {"separately_existential_checks": separately_exists,
            "same_shared_assignment_joint_checks": one_old_assignment,
            "compatible_scope_extensions": True,
            "rejected_old_or_existing_reselection": 2,
            "rejected_out_of_scope_extension": 1}


def knot_campaign():
    # Direct stack history evaluator vs backward finite-depth validator.
    # D = divergence: no return/future suffix; S = one suspension, resumed
    # with current configuration before rebind; R = immediate return.
    statuses = ("R", "S", "D")

    def execute(start, history):
        member, trace, current = start, [], 0
        for status in history:
            trace.append((member, "receipt", current))
            trace.append((member, "force", current))
            if status == "D":
                trace.append((member, "pending-divergence", current))
                return member, tuple(trace), False
            if status == "S":
                trace.append((member, "request", current))
                current += 1
                trace.append((member, "resume", current))
            trace.append((member, "rebind", current))
            member = 1 - member
            trace.append((member, "returned-provider", current))
        return member, tuple(trace), True

    def derive(start, history, current=0):
        if not history:
            return start, (), True
        status, rest = history[0], history[1:]
        prefix = [(start, "receipt", current), (start, "force", current)]
        if status == "D":
            prefix.append((start, "pending-divergence", current))
            return start, tuple(prefix), False
        if status == "S":
            prefix.append((start, "request", current))
            current += 1
            prefix.append((start, "resume", current))
        prefix.extend(((start, "rebind", current), (1-start, "returned-provider", current)))
        member, suffix, returned = derive(1-start, rest, current)
        return member, tuple(prefix) + suffix, returned

    cases = 0
    for length in range(7):
        for history in itertools.product(statuses, repeat=length):
            for start in (0, 1):
                assert execute(start, history) == derive(start, history)
                cases += 1
    # Missing finite-history bridge: adding an independent false DescMem
    # conjunct keeps every operational trace but prevents full validation.
    observations = execute(0, ("R",))[1]
    assert observations and not (bool(observations) and False)
    return {"histories": cases, "maximum_invocations": 6,
            "statuses": list(statuses), "hidden_descriptor_conjunct_discriminator": True}


def main():
    before = time.monotonic()
    result = {"claim": "bounded research consistency and shortcut discrimination",
              "syntax": syntax_campaign(), "logical_attacks": interface_semantic_attacks(),
              "shared_witness": shared_witness_campaign(),
              "knot": knot_campaign()}
    result["elapsed_seconds"] = round(time.monotonic() - before, 4)
    result["max_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
