#!/usr/bin/env python3
"""Finite two-hidden-atom structural projection model; no language authority."""

import itertools
import json
import resource
import signal


BASELINE = "caad6f1676867bfc46631119eadce925f1d4fafa"
KA, KB, INT = "kappa_a", "kappa_b", "Int"
HIDDEN = (KA, KB)
LABELS = ("a", "b", "c")

# Nodes are (head, ordered children); integers reference constructor nodes,
# strings are identity atoms, None denotes an absent Record label only.
def record(a=None, b=None, c=None):
    return ("Record", tuple((label, child)
                            for label, child in zip(LABELS, (a, b, c))
                            if child is not None))


def function(arg, result):
    return ("Function", (("arg", arg), ("result", result)))


def reachable(graph):
    seen, pending = {0}, [0]
    while pending:
        for _, child in graph[pending.pop()][1]:
            if isinstance(child, int) and child not in seen:
                seen.add(child)
                pending.append(child)
    return seen


def admitted(graph):
    if graph[0][0] != "Record":
        return False
    fields = dict(graph[0][1])
    return fields.get("a") == KA and fields.get("b") == KB


def source_graphs():
    """All reachable 1..2-constructor sources in the specified alphabet."""
    for size in (1, 2):
        atoms_refs = (KA, KB, INT, *range(size))
        for root_c in (None, *atoms_refs):
            if size == 1:
                yield (record(KA, KB, root_c),)
            else:
                for fields in itertools.product((None, *atoms_refs), repeat=3):
                    graph = (record(KA, KB, root_c), record(*fields))
                    if len(reachable(graph)) == size:
                        yield graph
                for children in itertools.product(atoms_refs, repeat=2):
                    graph = (record(KA, KB, root_c), function(*children))
                    if len(reachable(graph)) == size:
                        yield graph


def projection(graph, leak=None, sign_blind=False):
    """Supplied greatest signed availability, then shared construction."""
    states = tuple((node, sign) for node in range(len(graph)) for sign in (1, -1))
    available = set(states)

    def child_available(child, sign):
        return ((child, sign) in available if isinstance(child, int)
                else child not in HIDDEN or child == leak)

    def child_sign(head, label, sign):
        return (-sign if head == "Function" and label == "arg"
                and not sign_blind else sign)

    while True:
        removed = set()
        for node, sign in available:
            head, fields = graph[node]
            if head == "Record" and sign == 1:
                continue
            if not all(child_available(child, child_sign(head, label, sign))
                       for label, child in fields):
                removed.add((node, sign))
        if not removed:
            break
        available -= removed
    assert (0, 1) in available
    names, queue, output = {(0, 1): 0}, [(0, 1)], []
    for node, sign in queue:
        head, fields = graph[node]
        projected = []
        for label, child in fields:
            polarity = child_sign(head, label, sign)
            if head == "Record" and sign == 1 and not child_available(child, polarity):
                continue
            assert child_available(child, polarity)
            if isinstance(child, int):
                target = (child, polarity)
                if target not in names:
                    names[target] = len(names)
                    queue.append(target)
                projected.append((label, names[target]))
            else:
                projected.append((label, INT if child == leak else child))
        output.append((head, tuple(projected)))
    return tuple(output)


def negative_root_reachable(graph):
    """Independent signed-path grammar side condition; no availability call."""
    seen, pending = {(0, 1)}, [(0, 1)]
    while pending:
        node, sign = pending.pop()
        head, children = graph[node]
        for label, child in children:
            if not isinstance(child, int):
                continue
            target = (child, -sign if head == "Function" and label == "arg" else sign)
            if target == (0, -1):
                return True
            if target not in seen:
                seen.add(target)
                pending.append(target)
    return False


def visible_candidates():
    """Independent grammar: visible root omits a,b; <=2 constructors."""
    yield (record(),)
    yield (record(c=INT),)
    yield (record(c=0),)
    # Reachability forces c to reference node 1 in a two-node presentation.
    for fields in itertools.product((None, INT, 0, 1), repeat=3):
        yield (record(c=1), record(*fields))
    for children in itertools.product((INT, 0, 1), repeat=2):
        yield (record(c=1), function(*children))


def tree_key(graph):
    """Rooted regular-tree bisimulation quotient, including exact heads."""
    blocks = [0] * len(graph)
    while True:
        names, refined = {}, []
        for head, fields in graph:
            signature = (head, tuple((label, ("ref", blocks[child])
                                      if isinstance(child, int) else ("atom", child))
                                     for label, child in fields))
            names.setdefault(signature, len(names))
            refined.append(names[signature])
        if refined == blocks:
            break
        blocks = refined
    representatives = {}
    for node, block in enumerate(blocks):
        representatives.setdefault(block, node)
    names, queue, result = {blocks[0]: 0}, [blocks[0]], []
    for block in queue:
        head, fields = graph[representatives[block]]
        output = []
        for label, child in fields:
            if isinstance(child, int):
                target = blocks[child]
                if target not in names:
                    names[target] = len(names)
                    queue.append(target)
                output.append((label, ("ref", names[target])))
            else:
                output.append((label, ("atom", child)))
        result.append((head, tuple(output)))
    return tuple(result)


def check():
    sources = tuple(source_graphs())
    broad_candidates = tuple(visible_candidates())
    candidates = tuple(g for g in broad_candidates if not negative_root_reachable(g))
    assert all(admitted(g) and len(reachable(g)) == len(g) for g in sources)
    assert all(len(reachable(g)) == len(g) for g in broad_candidates)
    outputs = {tree_key(projection(g)) for g in sources}
    language = {tree_key(g) for g in candidates}
    broad_language = {tree_key(g) for g in broad_candidates}
    assert outputs == language, (outputs - language, language - outputs)
    assert broad_language - outputs

    empty = (record(),)
    self_cycle = (record(c=0),)
    double_cycle = (record(c=1), record(c=0))
    assert tree_key(self_cycle) == tree_key(double_cycle)
    assert tree_key(self_cycle) == tree_key((record(c=0), record(a=INT)))
    assert tree_key(self_cycle) != tree_key(empty)
    assert tree_key((function(INT, INT),)) != tree_key((record(a=INT, b=INT),))
    assert tree_key((record(a=KA),)) != tree_key((record(a=KB),))

    minimal = (record(KA, KB),)
    assert projection(minimal) == empty
    leak_counts = {}
    for hidden, label in ((KA, "a"), (KB, "b")):
        mutant = projection(minimal, leak=hidden)
        assert mutant == (("Record", ((label, INT),)),)
        assert tree_key(mutant) not in language
        leaked = {tree_key(projection(g, leak=hidden)) for g in sources}
        leak_counts[hidden] = len(leaked - language)

    # Removing either requirement admits a missing-field source. Its image
    # is already legitimate, so image equality cannot certify admission.
    for bad in ((record(b=KB),), (record(a=KA),), (record(KB, KA),)):
        assert not admitted(bad)
        assert tree_key(projection(bad)) in language
    for bad in ((record(INT, KB),), (record(KA, INT),)):
        assert not admitted(bad)
        assert tree_key(projection(bad)) not in language

    recursive = (record(KA, KB, 1), record(INT, KB, 0))
    recursive_visible = (record(c=1), record(a=INT, c=0))
    assert tree_key(projection(recursive)) == tree_key(recursive_visible)
    assert len(tree_key(recursive_visible)) == 2
    assert tree_key(recursive_visible) in language
    assert tree_key(projection((record(KA, KB, 0),))) == tree_key(self_cycle)

    variance_source = (record(KA, KB, 1), function(0, INT))
    assert projection(variance_source) == empty
    sign_blind_output = projection(variance_source, sign_blind=True)
    assert tree_key(sign_blind_output) in broad_language - language

    # One targeted, non-enumerated three-node source shows that the grammar's
    # signed-root restriction is a two-source-node cap, not a general law.
    clone_source = (record(KA, KB, 1), function(2, INT), record(c=1))
    assert admitted(clone_source)
    assert tree_key(projection(clone_source)) == tree_key(sign_blind_output)

    return {
        "claim": "finite characterization only; statically reviewed, not independently rerun; no implementation authority",
        "baseline": BASELINE,
        "range": "exhaustive 1..2 reachable constructors; Record root; labels a,b,c; two hidden identities and Int",
        "source_graphs_by_size": {str(n): sum(len(g) == n for g in sources) for n in (1, 2)},
        "source_graphs": len(sources),
        "source_classes": len({tree_key(g) for g in sources}),
        "broad_candidate_graphs": len(broad_candidates),
        "candidate_graphs_by_size": {str(n): sum(len(g) == n for g in candidates) for n in (1, 2)},
        "candidate_graphs": len(candidates),
        "image_classes": len(outputs),
        "candidate_classes": len(language),
        "equality": outputs == language,
        "broad_root_omission_false_positive_classes": len(broad_language - outputs),
        "leak_mutant_false_positive_classes": leak_counts,
        "admission_checks": "missing a, missing b, swapped identities reject but images legitimate; visible replacements reject and images excess",
        "additional_targeted_source_count": 1,
        "additional_targeted_source_size": 3,
        "self_checks": "PASS: image equality; bisimulation; distinct atoms; both leaks; admission; recursive extras; Function variance; clone witness",
        "budget": "one computation process; 5 s wall; 5 s CPU; 256 MiB address space",
    }


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    signal.setitimer(signal.ITIMER_REAL, 5)
    print(json.dumps(check(), indent=2, sort_keys=True))
