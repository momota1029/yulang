#!/usr/bin/env python3
"""Bounded Record/atom projection characterization; no theorem or source claim."""

import itertools
import json
import resource
import signal


HIDDEN = "kappa"
VISIBLE = "Int"
ABSENT = None
LABELS = ("a", "b")
BASELINE = "f65d68c5d43623f0d8a02194142828ec144755ab"

# An integer is a Record-node reference; a string is an atom. A graph is a
# tuple of Records, each an ordered tuple of (label, child) pairs; root is 0.


def record(a=ABSENT, b=ABSENT):
    return tuple((label, child) for label, child in zip(LABELS, (a, b))
                 if child is not ABSENT)


def reachable(graph):
    seen = {0}
    pending = [0]
    while pending:
        for _, child in graph[pending.pop()]:
            if isinstance(child, int) and child not in seen:
                seen.add(child)
                pending.append(child)
    return seen


def source_admitted(graph):
    """The supplied upper-only atomic fiber X <= {a:kappa}, unguarded."""
    return dict(graph[0]).get("a") == HIDDEN


def source_graphs():
    # Exhaustive lexicographic range: 1..2 reachable labelled Record nodes.
    # The root has mandatory a:kappa; all other label slots are optional.
    for size in (1, 2):
        choices = (ABSENT, HIDDEN, VISIBLE, *range(size))
        for root_b in choices:
            for tail_slots in itertools.product(choices, repeat=2 * (size - 1)):
                tail = tuple(record(*tail_slots[i:i + 2])
                             for i in range(0, len(tail_slots), 2))
                graph = (record(HIDDEN, root_b), *tail)
                if len(reachable(graph)) == size:
                    yield graph


def positive_reference(graph, leak_hidden=False):
    """Direct A+ for this fragment: Records always available, kappa never.

    Each Record edge is inspected once. Record targets remain references,
    including cycles; visible atom edges remain; hidden atom edges vanish.
    The mutant incorrectly gives a hidden leaf the visible result Int.
    """
    output = []
    for fields in graph:
        projected = []
        for label, child in fields:
            if child == HIDDEN:
                if leak_hidden:
                    projected.append((label, VISIBLE))
            else:
                projected.append((label, child))
        output.append(tuple(projected))
    return tuple(output)


def visible_candidates():
    """Independent grammar: no root a; visible children and <=2 Records.

    This does not inspect sources or call the projection reference.
    Nonroot Records may carry a or b. All node references are constructor
    guarded; only fully reachable presentations enter the candidate family.
    """
    yield ((),)
    yield ((("b", VISIBLE),),)
    yield ((("b", 0),),)
    # In a reachable two-node candidate, root b must refer to node 1.
    choices = (ABSENT, VISIBLE, 0, 1)
    for a_child in choices:
        for b_child in choices:
            secondary = []
            if a_child is not ABSENT:
                secondary.append(("a", a_child))
            if b_child is not ABSENT:
                secondary.append(("b", b_child))
            yield ((("b", 1),), tuple(secondary))


def tree_key(graph):
    """Canonical rooted bisimulation quotient, independent of node IDs.

    Refine the universal Record partition until stable using exact label
    sets, atom identities, and successor blocks. Then number the reachable
    quotient in root-first breadth-first order with ordered field labels.
    """
    blocks = [0] * len(graph)
    while True:
        signatures = [tuple((label, ("ref", blocks[child])
                            if isinstance(child, int) else ("atom", child))
                            for label, child in fields) for fields in graph]
        names = {}
        refined = []
        for signature in signatures:
            if signature not in names:
                names[signature] = len(names)
            refined.append(names[signature])
        if refined == blocks:
            break
        blocks = refined
    representatives = {}
    for node, block in enumerate(blocks):
        representatives.setdefault(block, node)
    numbered = {blocks[0]: 0}
    queue = [blocks[0]]
    result = []
    for block in queue:
        fields = []
        for label, child in graph[representatives[block]]:
            if isinstance(child, int):
                target = blocks[child]
                if target not in numbered:
                    numbered[target] = len(numbered)
                    queue.append(target)
                fields.append((label, ("ref", numbered[target])))
            else:
                fields.append((label, ("atom", child)))
        result.append(tuple(fields))
    return tuple(result)


def check():
    sources = tuple(source_graphs())
    candidates = tuple(visible_candidates())
    assert all(source_admitted(graph) for graph in sources)
    assert all(len(reachable(graph)) == len(graph) for graph in candidates)
    assert all("a" not in dict(graph[0]) for graph in candidates)
    assert all(child != HIDDEN for graph in candidates
               for fields in graph for _, child in fields)
    outputs = {tree_key(positive_reference(graph)) for graph in sources}
    language = {tree_key(graph) for graph in candidates}
    assert outputs == language, (outputs - language, language - outputs)

    # Genuine equivalence with different presentations, including a cycle;
    # unreachable nodes must not influence rooted equality either.
    self_cycle = ((("b", 0),),)
    doubled_cycle = ((("b", 1),), (("b", 0),))
    detached = ((("b", 0),), (("a", VISIBLE),))
    assert tree_key(self_cycle) == tree_key(doubled_cycle) == tree_key(detached)
    assert tree_key(((),)) != tree_key(self_cycle)
    assert tree_key(((("b", VISIBLE),),)) != tree_key(self_cycle)

    recursive_source = (record(HIDDEN, 1), record(VISIBLE, 0))
    recursive_output = ((("b", 1),), record(VISIBLE, 0))
    assert len(tree_key(recursive_output)) == 2
    assert tree_key(positive_reference(recursive_source)) == tree_key(recursive_output)
    assert tree_key(recursive_output) in language
    assert tree_key(positive_reference((record(HIDDEN, 0),))) in language

    # Smallest source presentation: one Record and its mandatory hidden atom.
    leak_source = (record(HIDDEN),)
    leak_output = positive_reference(leak_source, leak_hidden=True)
    assert leak_output == (record(VISIBLE),)
    assert tree_key(leak_output) not in language
    leaked = {tree_key(positive_reference(graph, leak_hidden=True))
              for graph in sources}
    assert leaked - language

    # Independent admissibility mutant: accepting a:Int violates X<=a:kappa.
    # Ordinary A+ now retains a, producing a false positive in the image.
    bad_source = (record(VISIBLE),)
    assert not source_admitted(bad_source)
    assert tree_key(positive_reference(bad_source)) not in language
    # Dropping a entirely violates the source fiber too, but its image {} is
    # legitimate. Image-set equality alone cannot detect that weaker mutant.
    missing_required = ((),)
    assert not source_admitted(missing_required)
    assert tree_key(positive_reference(missing_required)) in language

    return {
        "claim": "finite characterization only; no theorem promotion",
        "baseline": BASELINE,
        "range": "exhaustive, no random seed; reachable Record nodes 1..2; labels a,b",
        "source_graphs_by_size": {str(n): sum(len(g) == n for g in sources)
                                  for n in (1, 2)},
        "source_graphs": len(sources),
        "source_bisimulation_classes": len({tree_key(g) for g in sources}),
        "candidate_graphs_by_size": {str(n): sum(len(g) == n for g in candidates)
                                     for n in (1, 2)},
        "candidate_graphs": len(candidates),
        "projection_classes": len(outputs),
        "candidate_classes": len(language),
        "equality": outputs == language,
        "equality_criterion": "rooted deterministic labelled-tree bisimulation",
        "leak_mutant_false_positive_classes": len(leaked - language),
        "smallest_leak_witness": "{a:kappa} -> mutant {a:Int}; correct {}",
        "admissibility_mutant_witness": "accept {a:Int} as X<= {a:kappa}; A+ retains a",
        "missing_a_mutant": "{} fails source admissibility but its image is legitimate",
        "recursive_witness": "r0={a:kappa,b:r1}; r1={a:Int,b:r0}; retains b cycle",
        "self_checks": "PASS: image equality, bisimulation, mutations, recursive witnesses",
        "budget": "one computation process; wall 5 s; CPU 5 s; address space 256 MiB",
    }


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    signal.setitimer(signal.ITIMER_REAL, 5)
    print(json.dumps(check(), indent=2, sort_keys=True))
