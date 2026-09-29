"""Finite executable model for SCC-intrusion closure lemmas.

This is a research characterization, not the production solver. It models the
pure polarized fragment documented in
notes/design/2026-09-29-intrusion-abstract-semantics-draft.md.
"""
from collections import defaultdict, deque

BOT = ("bot",)
TOP = ("top",)
INT_P = ("int+",)
INT_N = ("int-",)


def var(v):
    return ("var", v)


def fun_p(arg_n, ret_p):
    return ("fun+", arg_n, ret_p)


def fun_n(arg_p, ret_n):
    return ("fun-", arg_p, ret_n)


def con_p(path, args=()):
    return ("con+", path, tuple(args))


def con_n(path, args=()):
    return ("con-", path, tuple(args))


def union_p(left, right):
    return ("union", left, right)


def intersection_n(left, right):
    return ("intersection", left, right)


def rename_type(ty, renaming):
    tag = ty[0]
    if tag == "var":
        return (tag, renaming.get(ty[1], ty[1]))
    if tag == "fun+":
        return (tag, rename_type(ty[1], renaming), rename_type(ty[2], renaming))
    if tag == "fun-":
        return (tag, rename_type(ty[1], renaming), rename_type(ty[2], renaming))
    if tag in ("con+", "con-"):
        return (tag, ty[1], tuple((rename_type(p, renaming), rename_type(n, renaming)) for p, n in ty[2]))
    if tag == "union":
        return (tag, rename_type(ty[1], renaming), rename_type(ty[2], renaming))
    if tag == "intersection":
        return (tag, rename_type(ty[1], renaming), rename_type(ty[2], renaming))
    return ty


def rename_constraints(constraints, renaming):
    return {(rename_type(p, renaming), rename_type(n, renaming)) for p, n in constraints}


def close(constraints):
    """Compute lower/upper rows under the finite core's closure rules."""
    lowers = defaultdict(set)
    uppers = defaultdict(set)
    queue = deque(constraints)
    seen = set()

    def add_lower(v, p):
        if p in lowers[v]:
            return
        lowers[v].add(p)
        queue.extend((p, n) for n in tuple(uppers[v]))

    def add_upper(v, n):
        if n in uppers[v]:
            return
        uppers[v].add(n)
        queue.extend((p, n) for p in tuple(lowers[v]))

    while queue:
        p, n = queue.popleft()
        pair = (p, n)
        if pair in seen:
            continue
        seen.add(pair)
        if p == BOT or n == TOP:
            continue
        if p[0] == "union":
            queue.extend(((p[1], n), (p[2], n)))
            continue
        if n[0] == "intersection":
            queue.extend(((p, n[1]), (p, n[2])))
            continue
        if p[0] == "var":
            v = p[1]
            if n[0] == "var":
                w = n[1]
                if v != w:
                    add_lower(w, p)
                    add_upper(v, n)
            else:
                add_upper(v, n)
            continue
        if n[0] == "var":
            add_lower(n[1], p)
            continue
        if p[0] == "fun+" and n[0] == "fun-":
            # Contravariant argument, covariant result.
            queue.extend(((n[1], p[1]), (p[2], n[2])))
            continue
        if p[0] == "con+" and n[0] == "con-" and p[1] == n[1] and len(p[2]) == len(n[2]):
            for (lower_p, lower_n), (upper_p, upper_n) in zip(p[2], n[2]):
                queue.extend(((lower_p, upper_n), (upper_p, lower_n)))
            continue
        if p == INT_P and n == INT_N:
            continue
        # Other concrete head pairs are outside this model's input envelope.

    return (
        {v: frozenset(bounds) for v, bounds in lowers.items()},
        {v: frozenset(bounds) for v, bounds in uppers.items()},
    )


def rename_rows(rows, renaming):
    renamed = defaultdict(set)
    for v, bounds in rows.items():
        renamed[renaming.get(v, v)].update(rename_type(ty, renaming) for ty in bounds)
    return {v: frozenset(bounds) for v, bounds in renamed.items()}


def check_transport(name, constraints, renaming):
    before = close(constraints)
    after = close(rename_constraints(constraints, renaming))
    expected = (rename_rows(before[0], renaming), rename_rows(before[1], renaming))
    assert after == expected, (name, after, expected)


def main():
    # Identity: one variable occurs at both polarities beneath a Function.
    identity = {(fun_p(var("a"), var("a")), var("root"))}
    check_transport("identity/bipolar", identity, {"a": "a_parent"})
    identity_rows = close(identity)
    assert fun_p(var("a"), var("a")) in identity_rows[0]["root"]

    # Directed flow: a <: b is two bound edges, not equality.
    flow = {(var("a"), var("b"))}
    flow_rows = close(flow)
    assert var("a") in flow_rows[0]["b"]
    assert var("b") in flow_rows[1]["a"]
    check_transport("directed-flow", flow, {"a": "pa", "b": "pb"})

    # Function subtyping reverses argument flow and preserves result flow.
    function_flow = {(fun_p(var("a"), var("b")), fun_n(var("c"), var("d")))}
    function_rows = close(function_flow)
    assert var("c") in function_rows[0]["a"]
    assert var("a") in function_rows[1]["c"]
    assert var("b") in function_rows[0]["d"]
    assert var("d") in function_rows[1]["b"]
    check_transport("function-polarity", function_flow,
                    {"a": "pa", "b": "pb", "c": "pc", "d": "pd"})

    # Same nominal head has invariant arguments.
    invariant = {(con_p("Pair", ((var("a"), var("a")),)),
                  con_n("Pair", ((var("b"), var("b")),)))}
    invariant_rows = close(invariant)
    assert var("a") in invariant_rows[0]["b"]
    assert var("b") in invariant_rows[0]["a"]
    check_transport("invariant-constructor", invariant, {"a": "pa", "b": "pb"})

    # Shared diamond: both paths retain their common endpoint c.
    diamond = {(var("a"), var("c")), (var("b"), var("c"))}
    check_transport("shared-diamond", diamond, {"a": "pa", "b": "pb", "c": "pc"})

    # Capture avoidance: the outer vertex remains the same identity after copy.
    captured = {(var("outer"), var("local")), (var("local"), var("outer"))}
    check_transport("outer-capture", captured, {"local": "local_parent"})
    captured_rows = close(rename_constraints(captured, {"local": "local_parent"}))
    assert "outer" in captured_rows[0] and "local_parent" in captured_rows[0]

    # Productive regular cycle: a parent copy points back through a nominal constructor.
    recursive = {(con_p("Loop", ((var("r"), var("r")),)), var("r"))}
    check_transport("nominal-guarded-cycle", recursive, {"r": "r_parent"})
    recursive_rows = close(rename_constraints(recursive, {"r": "r_parent"}))
    assert con_p("Loop", ((var("r_parent"), var("r_parent")),)) in recursive_rows[0]["r_parent"]

    # Positive unions and negative intersections retain both branch obligations.
    branching = {(union_p(var("a"), var("b")), var("c")),
                 (var("c"), intersection_n(var("d"), var("e")))}
    branching_rows = close(branching)
    assert {var("a"), var("b")} <= branching_rows[0]["c"]
    assert {var("d"), var("e")} <= branching_rows[1]["c"]
    check_transport("union/intersection", branching,
                    {"a": "pa", "b": "pb", "c": "pc", "d": "pd", "e": "pe"})

    # Non-injective quotient is unsound: it erases a directed flow edge as reflexive.
    quotient = close(flow)
    renamed_quotient = tuple(rename_rows(rows, {"a": "p", "b": "p"}) for rows in quotient)
    collapsed = close(rename_constraints(flow, {"a": "p", "b": "p"}))
    assert renamed_quotient != collapsed
    assert not collapsed[0] and not collapsed[1]

    # Two incoming-use overlays receive distinct parent identities and bounds.
    use1 = close({(INT_P, var("p1"))})
    use2 = close({(fun_p(TOP, INT_P), var("p2"))})
    assert INT_P in use1[0]["p1"]
    assert fun_p(TOP, INT_P) in use2[0]["p2"]
    assert "p2" not in use1[0] and "p1" not in use2[0]

    print("finite intrusion closure model: 10 cases passed")
    print("cases: identity, directed flow, Function polarity, invariant constructor,")
    print("       diamond, outer capture, nominal cycle, union/intersection,")
    print("       non-injective quotient, independent use overlays")
    print("scope: closure transport only; no principal projection theorem")


if __name__ == "__main__":
    main()
