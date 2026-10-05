#!/usr/bin/env python3
"""Bounded admission-retraction premise checks; no source/implementation authority."""
import itertools
import json
import resource
import signal
import time

BASELINE = "4b093702f"
KA, KB, INT = "kappa_a", "kappa_b", "Int"
HIDDEN = (KA, KB)
LABELS = ("a", "b", "c")


def record(**fields):
    return ("Record", tuple((k, fields[k]) for k in LABELS if fields.get(k) is not None))


def function(a, b):
    return ("Function", (("arg", a), ("result", b)))


def reachable(g):
    seen, todo = {0}, [0]
    while todo:
        for _, t in g[todo.pop()][1]:
            if isinstance(t, int) and t not in seen:
                seen.add(t)
                todo.append(t)
    return seen


def sources(h):
    extra = "b" if len(h) == 1 else "c"
    fixed = dict(h)
    for n in (1, 2):
        choices = (None, KA, KB, INT, *range(n))
        for child in choices:
            root = record(**fixed, **{extra: child})
            if n == 1:
                yield (root,)
            else:
                for xs in itertools.product(choices, repeat=3):
                    g = (root, record(**dict(zip(LABELS, xs))))
                    if len(reachable(g)) == n:
                        yield g
                for a, b in itertools.product(choices[1:], repeat=2):
                    g = (root, function(a, b))
                    if len(reachable(g)) == n:
                        yield g


def projection(g):
    available = {(n, p) for n in range(len(g)) for p in (1, -1)}

    def ok(t, p):
        return (t, p) in available if isinstance(t, int) else t not in HIDDEN

    def polarity(head, label, p):
        return -p if head == "Function" and label == "arg" else p

    while True:
        bad = {(n, p) for n, p in available
               if not (g[n][0] == "Record" and p == 1)
               and not all(ok(t, polarity(g[n][0], label, p)) for label, t in g[n][1])}
        if not bad:
            break
        available -= bad
    assert (0, 1) in available
    names, todo, out = {(0, 1): 0}, [(0, 1)], []
    for n, p in todo:
        head, fields = g[n]
        result = []
        for label, t in fields:
            q = polarity(head, label, p)
            if head == "Record" and p == 1 and not ok(t, q):
                continue
            assert ok(t, q)
            if isinstance(t, int):
                if (t, q) not in names:
                    names[t, q] = len(names)
                    todo.append((t, q))
                t = names[t, q]
            result.append((label, t))
        out.append((head, tuple(result)))
    return tuple(out)


def graft(v, h):
    shift = lambda t: t + 1 if isinstance(t, int) else t
    copied = tuple((head, tuple((label, shift(t)) for label, t in fields))
                   for head, fields in v)
    fields = dict(h)
    assert not fields.keys() & dict(v[0][1]).keys()
    fields.update((label, shift(t)) for label, t in v[0][1])
    return (record(**fields), *copied)


def key(g):
    blocks = [0] * len(g)
    while True:
        names, new = {}, []
        for head, fs in g:
            sig = (head, tuple((l, ("ref", blocks[t]) if isinstance(t, int)
                               else ("atom", t)) for l, t in fs))
            names.setdefault(sig, len(names))
            new.append(names[sig])
        if new == blocks:
            break
        blocks = new
    reps = {b: i for i, b in enumerate(blocks)}
    names, todo, result = {blocks[0]: 0}, [blocks[0]], []
    for b in todo:
        head, fs = g[reps[b]]
        fields = []
        for label, t in fs:
            if isinstance(t, int):
                target = blocks[t]
                if target not in names:
                    names[target] = len(names)
                    todo.append(target)
                t = ("ref", names[target])
            else:
                t = ("atom", t)
            fields.append((label, t))
        result.append((head, tuple(fields)))
    return tuple(result)


def subtype(g, u):
    """Reference: find a local mismatch in the finite required-pair graph."""
    graphs = (g, u)
    seen, todo = set(), [((0, 0), (1, 0))]
    while todo:
        a, b = todo.pop()
        if (a, b) in seen:
            continue
        seen.add((a, b))
        x, y = a[1], b[1]
        if not isinstance(x, int) or not isinstance(y, int):
            if x != y:
                return False
            continue
        hx, fx = graphs[a[0]][x]
        hy, fy = graphs[b[0]][y]
        if hx != hy:
            return False
        fx, fy = dict(fx), dict(fy)
        if not fy.keys() <= fx.keys():
            return False
        for label, t in fy.items():
            p, q = (a[0], fx[label]), (b[0], t)
            todo.append((q, p) if hx == "Function" and label == "arg" else (p, q))
    return True


def hidden_mask(g):
    atoms = {t for n in reachable(g) for _, t in g[n][1] if isinstance(t, str)}
    return sum(1 << i for i, t in enumerate(HIDDEN) if t in atoms)


def queries():
    # Every visible Record query with <=1 constructor over this alphabet.
    return tuple((record(**dict(zip(LABELS, xs))),)
                 for xs in itertools.product((None, INT, 0), repeat=3))


def check():
    qs = queries()
    omega = tuple(itertools.product(range(4), range(4), range(2), range(2)))
    phi_names = ("true", "extra_hidden", "invariant_fixed", "request_owner",
                 "request_sensitive_extra", "visible_query")
    result, total_comparisons = {}, 0
    for h in ((("a", KA),), (("a", KA), ("b", KB))):
        src = tuple(sources(h))
        images = {key(projection(g)): projection(g) for g in src}
        canonical = {k: graft(v, h) for k, v in images.items()}
        domain = tuple(dict.fromkeys((*src, *canonical.values())))
        extra = "b" if len(h) == 1 else "c"
        fixed = (record(**dict(h), **{extra: KA}),)
        anchor_key = key(fixed)
        facts = {}
        for g in domain:
            v = projection(g)
            k = key(v)
            assert k in canonical
            c = canonical[k]
            assert key(projection(c)) == k
            assert dict(g[0][1]).items() >= dict(h).items()
            assert hidden_mask(c) & ~hidden_mask(g) == 0
            bits = tuple(subtype(g, q) for q in qs)
            assert bits == tuple(subtype(v, q) for q in qs)
            assert bits == tuple(subtype(c, q) for q in qs)
            total_comparisons += 3 * len(qs)
            facts[g] = (k, hidden_mask(g), dict(g[0][1]).get(extra) == KA,
                        key(g) == anchor_key, bits)
        mandatory = sum(1 << HIDDEN.index(t) for _, t in h)

        def admit(g, w, phi):
            k, mask, extra_present, invariant, bits = facts[g]
            permissions, guard_atoms, request, owner = w
            # Propagated permission intersection is represented by permissions.
            # Guards check original bound and required atomic child comparisons.
            if mask & ~permissions or mandatory & ~guard_atoms:
                return False
            clauses = (True, extra_present, invariant, request == owner,
                       (request == owner and (extra_present if request == 0 else not extra_present)),
                       bits[1])
            return clauses[phi]

        summary = {}
        for phi, name in enumerate(phi_names):
            passes = failures = differences = 0
            first = None
            for w in omega:
                original = {facts[g][0] for g in domain if admit(g, w, phi)}
                picked = {k for k, g in canonical.items() if admit(g, w, phi)}
                retracts = all(not admit(g, w, phi)
                               or admit(canonical[facts[g][0]], w, phi) for g in domain)
                if retracts:
                    passes += 1
                    assert original == picked
                    for qi in range(len(qs)):
                        left = any(admit(g, w, phi) and facts[g][4][qi] for g in domain)
                        right = any(admit(g, w, phi) and facts[g][4][qi]
                                    for g in canonical.values())
                        assert left == right
                else:
                    failures += 1
                    if first is None:
                        first = w
                differences += original != picked
            summary[name] = {"premise_pass_omega": passes, "premise_fail_omega": failures,
                             "image_inequality_omega": differences,
                             "first_failure_omega": first}
        assert summary["extra_hidden"]["image_inequality_omega"] > 0
        assert summary["invariant_fixed"]["image_inequality_omega"] > 0
        assert summary["true"]["premise_fail_omega"] == 0
        assert summary["request_owner"]["premise_fail_omega"] == 0
        result[str(h)] = {"source_graphs": len(src), "image_classes": len(images),
                          "closed_finite_domain_graphs": len(domain), "predicates": summary}

    # Smallest nonempty-H extra-hidden-field and invariant counterexample.
    t, c = (record(a=KA, b=KA),), (record(a=KA),)
    assert key(projection(t)) == key(projection(c))
    assert subtype(t, t) and not (subtype(t, c) and subtype(c, t))
    # Root-identity predicate is outside the bisimulation-invariant contract.
    s, duplicate = (record(c=0),), (record(c=1), record(c=0))
    assert key(s) == key(duplicate) and s != duplicate
    # Same witness/request coordinate: changing request could mask failed route.
    assert dict(t[0][1]).get("b") == KA and dict(c[0][1]).get("b") != KA
    # Contravariant feedback: mutating the old root drops the Function field.
    v = (record(c=1), function(0, INT))
    naive = (record(a=KA, c=1), function(0, INT))
    proper = graft(v, (("a", KA),))
    assert projection(naive) == (record(),)
    assert key(projection(proper)) == key(v)
    # Exhaustive arbitrary admission predicates on a three-point closed fiber.
    # Two preimages share empty image; one has a distinct visible c:Int image.
    small = ((record(a=KA),), (record(a=KA, b=KA),), (record(a=KA, c=INT),))
    classes = (0, 0, 1)
    selected = (0, 2)
    passing = 0
    for mask in range(8):
        accepted = lambda i: bool(mask & (1 << i))
        premise = all(not accepted(i) or accepted(selected[classes[i]]) for i in range(3))
        before = {classes[i] for i in range(3) if accepted(i)}
        after = {classes[i] for i in selected if accepted(i)}
        if premise:
            passing += 1
            assert before == after
    return {"baseline": BASELINE, "claim": "bounded conditional characterization; unreviewed research",
            "omega_count_per_predicate": len(omega), "visible_upper_queries": len(qs),
            "subtype_reference_comparisons": total_comparisons,
            "ranges": result, "arbitrary_three_point_admission_masks": 8,
            "three_point_premise_pass_masks": passing,
            "targeted_attacks": "extra hidden fields, invariant original equality, fixed request/owner, graph identity exclusion, contravariant feedback: PASS",
            "budget": "single process; <=5s CPU/wall; <=256MiB address space"}


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    signal.setitimer(signal.ITIMER_REAL, 5)
    start = time.monotonic()
    output = check()
    output["wall_seconds"] = round(time.monotonic() - start, 6)
    output["cpu_seconds"] = round(time.process_time(), 6)
    status = dict(line.split(":", 1) for line in open("/proc/self/status", encoding="ascii") if ":" in line)
    output["vm_hwm"] = status["VmHWM"].strip()
    output["vm_peak"] = status["VmPeak"].strip()
    output["resource_note"] = "Linux /proc self high-water used; getrusage ru_maxrss can inherit launcher history"
    print(json.dumps(output, indent=2, sort_keys=True))
