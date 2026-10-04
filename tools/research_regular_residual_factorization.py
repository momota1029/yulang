#!/usr/bin/env python3
"""Search recursive regular graphs for residual-normalization mismatches.

The checker compares direct greatest-fixed-point structural subtyping on
instantiated regular graphs with finite open-head residual normalization.
It uses mandatory Records and contravariant Function arguments. Joint tests
retain supplied finite extensional Phi relations. The model does not generate
source-derived Phi/K,D, interpret lexical guards or effects, or model source
packages.

Run: python3 -B tools/research_regular_residual_factorization.py
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from random import Random
from typing import TypeAlias


Node: TypeAlias = tuple


@dataclass(frozen=True)
class Graph:
    nodes: tuple[Node, ...]
    root: int


@dataclass(frozen=True)
class Bound:
    nodes: tuple[Node, ...]
    left: int
    right: int


def atom(name: str) -> Node:
    return ("atom", name)


def variable(name: str) -> Node:
    return ("var", name)


def function(argument: int, result: int) -> Node:
    return ("fun", argument, result)


def record(fields: tuple[tuple[str, int], ...]) -> Node:
    return ("record", fields)


def refs(node: Node) -> tuple[int, ...]:
    if node[0] == "fun":
        return node[1:]
    if node[0] == "record":
        return tuple(child for _, child in node[1])
    return ()


def reachable(nodes: tuple[Node, ...], root: int) -> frozenset[int]:
    seen: set[int] = set()
    todo = [root]
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        todo.extend(refs(nodes[current]))
    return frozenset(seen)


def is_closed(graph: Graph) -> bool:
    return all(graph.nodes[index][0] != "var" for index in reachable(graph.nodes, graph.root))


def instantiate(bound: Bound, assignment: dict[str, Graph]) -> tuple[tuple[Node, ...], dict[int, int]]:
    """Copy the bound and replace each variable node by one shared graph copy."""
    combined = list(bound.nodes)
    assignment_roots: dict[str, int] = {}
    for name in sorted(assignment):
        graph = assignment[name]
        offset = len(combined)
        for node in graph.nodes:
            if node[0] == "fun":
                combined.append(function(offset + node[1], offset + node[2]))
            elif node[0] == "record":
                combined.append(
                    record(tuple((label, offset + child) for label, child in node[1]))
                )
            else:
                combined.append(node)
        assignment_roots[name] = offset + graph.root

    def map_ref(index: int) -> int:
        target = bound.nodes[index]
        if target[0] == "var":
            return assignment_roots[target[1]]
        return index

    rewritten: list[Node] = []
    for node in bound.nodes:
        if node[0] == "fun":
            rewritten.append(function(map_ref(node[1]), map_ref(node[2])))
        elif node[0] == "record":
            rewritten.append(record(tuple((label, map_ref(child)) for label, child in node[1])))
        else:
            rewritten.append(node)
    combined[: len(bound.nodes)] = rewritten
    root_map = {index: map_ref(index) for index in range(len(bound.nodes))}
    return tuple(combined), root_map


def compatible_children(left: Node, right: Node) -> tuple[tuple[int, int], ...] | None:
    if left[0] == "atom" and right[0] == "atom":
        return () if left[1] == right[1] else None
    if left[0] == "fun" and right[0] == "fun":
        return ((right[1], left[1]), (left[2], right[2]))
    if left[0] == "record" and right[0] == "record":
        left_fields = dict(left[1])
        right_fields = dict(right[1])
        if not right_fields.keys() <= left_fields.keys():
            return None
        return tuple((left_fields[label], child) for label, child in right[1])
    return None


def subtype_gfp(nodes: tuple[Node, ...], left: int, right: int) -> bool:
    """Greatest structural simulation by descending from all node pairs."""
    pairs = {(i, j) for i in range(len(nodes)) for j in range(len(nodes))}
    changed = True
    while changed:
        changed = False
        remove = []
        for i, j in pairs:
            children = compatible_children(nodes[i], nodes[j])
            if children is None or any(pair not in pairs for pair in children):
                remove.append((i, j))
        if remove:
            pairs.difference_update(remove)
            changed = True
    return (left, right) in pairs


def normalize(bound: Bound) -> tuple[bool, tuple[tuple[int, int], ...], int]:
    residuals: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    todo = [(bound.left, bound.right)]
    while todo:
        left, right = todo.pop()
        pair = (left, right)
        if pair in seen:
            continue
        seen.add(pair)
        left_node, right_node = bound.nodes[left], bound.nodes[right]
        if left_node[0] == "var" or right_node[0] == "var":
            residuals.append(pair)
            continue
        children = compatible_children(left_node, right_node)
        if children is None:
            return False, tuple(residuals), len(seen)
        todo.extend(children)
    return True, tuple(residuals), len(seen)


def residual_holds(
    bound: Bound,
    residuals: tuple[tuple[int, int], ...],
    assignment: dict[str, Graph],
) -> bool:
    nodes, root_map = instantiate(bound, assignment)
    return all(subtype_gfp(nodes, root_map[left], root_map[right]) for left, right in residuals)


def generated_closed_graphs() -> tuple[Graph, ...]:
    graphs = {
        Graph((atom("A"),), 0),
        Graph((atom("B"),), 0),
        Graph((function(0, 0),), 0),
        Graph((record(()),), 0),
        Graph((record((("a", 0),)),), 0),
        Graph((record((("b", 0),)),), 0),
        Graph((record((("a", 0), ("b", 0))),), 0),
        Graph((function(1, 0), atom("A")), 0),
        Graph((function(0, 1), atom("B")), 0),
        Graph((record((("a", 1),)), record((("b", 0),))), 0),
        Graph((record((("a", 1), ("b", 0))), function(0, 0)), 0),
        Graph((function(1, 0), function(0, 1)), 0),
    }
    return tuple(sorted(graphs, key=repr))


def graph_equal(left: Graph, right: Graph) -> bool:
    """Equality of regular constructor unfoldings, independent of sharing."""
    seen: set[tuple[int, int]] = set()
    todo = [(left.root, right.root)]
    while todo:
        i, j = todo.pop()
        if (i, j) in seen:
            continue
        seen.add((i, j))
        left_node, right_node = left.nodes[i], right.nodes[j]
        if left_node[0] != right_node[0]:
            return False
        if left_node[0] == "atom":
            if left_node[1] != right_node[1]:
                return False
        elif left_node[0] == "fun":
            todo.extend(((left_node[1], right_node[1]), (left_node[2], right_node[2])))
        elif left_node[0] == "record":
            left_fields, right_fields = dict(left_node[1]), dict(right_node[1])
            if left_fields.keys() != right_fields.keys():
                return False
            todo.extend((left_fields[label], right_fields[label]) for label in left_fields)
        else:
            return False
    return True


def joint_phi_relations(domain: tuple[Graph, ...]):
    all_pairs = frozenset((i, j) for i in range(len(domain)) for j in range(len(domain)))
    return (
        all_pairs,
        frozenset((i, j) for i, j in all_pairs if graph_equal(domain[i], domain[j])),
        frozenset((i, j) for i, j in all_pairs if not graph_equal(domain[i], domain[j])),
        frozenset((i, j) for i, j in all_pairs if domain[i].nodes[domain[i].root][0] == "atom"),
        frozenset((i, j) for i, j in all_pairs if domain[j].nodes[domain[j].root][0] == "record"),
        frozenset((i, j) for i, j in all_pairs if (i + 2 * j) % 3 == 0),
        frozenset((i, j) for i, j in all_pairs if i < j),
        frozenset((i, j) for i, j in all_pairs if (i, j) not in {(0, 1), (1, 0)}),
    )


def package_solution_sets(bounds: tuple[Bound, ...], x: Graph, y: Graph):
    direct = True
    normalized = True
    for bound in bounds:
        form_ok, residuals, _ = normalize(bound)
        instance, roots = instantiate(bound, {"x": x, "y": y})
        direct = direct and subtype_gfp(instance, roots[bound.left], roots[bound.right])
        normalized = normalized and form_ok and residual_holds(
            bound, residuals, {"x": x, "y": y}
        )
    return direct, normalized


def check_recursive_joint_packages():
    domain = (
        Graph((atom("A"),), 0),
        Graph((atom("B"),), 0),
        Graph((function(0, 0),), 0),
        Graph((record((("a", 0),)),), 0),
        Graph((record((("a", 1),)), atom("A")), 0),
    )
    phi_relations = joint_phi_relations(domain)
    rng = Random(20261006)
    pool = tuple(random_bound(rng, rng.choice((2, 3, 4))) for _ in range(48))
    packages_checked = 0
    pair_checks = 0
    bound_checks = 0
    recursive_packages = 0
    nonempty_packages = 0
    direct_projections: list[tuple[frozenset[int], frozenset[int]]] = []
    normalized_projections: list[tuple[frozenset[int], frozenset[int]]] = []

    for package_id in range(192):
        count = 1 + rng.randrange(3)
        selected = tuple(pool[index] for index in rng.sample(range(len(pool)), count))
        phi = phi_relations[package_id % len(phi_relations)]
        if any(has_cycle(bound.nodes, (bound.left, bound.right)) for bound in selected):
            recursive_packages += 1
        direct_solutions: set[tuple[int, int]] = set()
        normalized_solutions: set[tuple[int, int]] = set()
        for i, x in enumerate(domain):
            for j, y in enumerate(domain):
                if (i, j) not in phi:
                    continue
                direct, normalized = package_solution_sets(selected, x, y)
                assert direct == normalized, (package_id, selected, phi, x, y, direct, normalized)
                pair_checks += 1
                bound_checks += count
                if direct:
                    direct_solutions.add((i, j))
                if normalized:
                    normalized_solutions.add((i, j))
        assert direct_solutions == normalized_solutions
        if direct_solutions:
            nonempty_packages += 1
        direct_projections.append(
            (frozenset(i for i, _ in direct_solutions), frozenset(j for _, j in direct_solutions))
        )
        normalized_projections.append(
            (
                frozenset(i for i, _ in normalized_solutions),
                frozenset(j for _, j in normalized_solutions),
            )
        )
        packages_checked += 1

    assert direct_projections == normalized_projections
    return packages_checked, pair_checks, bound_checks, recursive_packages, nonempty_packages


def check_joint_phi_obstruction():
    # Each bound has a Phi-admitted witness alone, but no common tuple satisfies
    # both bounds. Projecting and recombining each bound independently is unsound.
    nodes_x = (variable("x"), atom("A"))
    nodes_y = (variable("y"), atom("A"))
    x_bound = Bound(nodes_x, 0, 1)
    y_bound = Bound(nodes_y, 0, 1)
    domain = (Graph((atom("A"),), 0), Graph((atom("B"),), 0))
    phi = frozenset({(0, 1), (1, 0)})
    x_only = any(
        i == 0 and j == 1 and package_solution_sets((x_bound,), domain[i], domain[j])[0]
        for i, j in phi
    )
    y_only = any(
        i == 1 and j == 0 and package_solution_sets((y_bound,), domain[i], domain[j])[0]
        for i, j in phi
    )
    joint = any(
        package_solution_sets((x_bound, y_bound), domain[i], domain[j])[0]
        for i, j in phi
    )
    without_phi = any(
        package_solution_sets((x_bound, y_bound), x, y)[0]
        for x in domain
        for y in domain
    )
    assert x_only and y_only and not joint and without_phi
    return x_only, y_only, joint, without_phi


def one_node_bound_nodes() -> tuple[Node, ...]:
    nodes: list[Node] = [atom("A"), atom("B"), variable("x"), variable("y")]
    nodes.extend(function(child, child) for child in (0, 1))
    for left in (None, 0, 1):
        for right in (None, 0, 1):
            fields = tuple((label, child) for label, child in (("a", left), ("b", right)) if child is not None)
            nodes.append(record(fields))
    return tuple(nodes)


def random_bound(rng: Random, node_count: int) -> Bound:
    nodes: list[Node] = []
    for _ in range(node_count):
        choice = rng.randrange(7)
        if choice == 0:
            nodes.append(atom(rng.choice(("A", "B"))))
        elif choice == 1:
            nodes.append(variable(rng.choice(("x", "y"))))
        elif choice <= 4:
            nodes.append(function(rng.randrange(node_count), rng.randrange(node_count)))
        else:
            labels = [label for label in ("a", "b") if rng.randrange(2)]
            nodes.append(record(tuple((label, rng.randrange(node_count)) for label in labels)))
    variables = [index for index, node in enumerate(nodes) if node[0] == "var"]
    if not variables:
        nodes[rng.randrange(node_count)] = variable(rng.choice(("x", "y")))
        variables = [index for index, node in enumerate(nodes) if node[0] == "var"]
    left = rng.randrange(node_count)
    right = rng.randrange(node_count)
    if not (reachable(tuple(nodes), left) | reachable(tuple(nodes), right)) & frozenset(variables):
        right = rng.choice(variables)
    reached = reachable(tuple(nodes), left) | reachable(tuple(nodes), right)
    # Compact away unreachable vertices while preserving cycles.
    order = sorted(reached)
    remap = {old: new for new, old in enumerate(order)}
    compact: list[Node] = []
    for old in order:
        node = nodes[old]
        if node[0] == "fun":
            compact.append(function(remap[node[1]], remap[node[2]]))
        elif node[0] == "record":
            compact.append(record(tuple((label, remap[child]) for label, child in node[1])))
        else:
            compact.append(node)
    return Bound(tuple(compact), remap[left], remap[right])


def has_cycle(nodes: tuple[Node, ...], roots: tuple[int, ...]) -> bool:
    active: set[int] = set()
    done: set[int] = set()

    def visit(index: int) -> bool:
        if index in active:
            return True
        if index in done:
            return False
        active.add(index)
        if any(visit(child) for child in refs(nodes[index])):
            return True
        active.remove(index)
        done.add(index)
        return False

    return any(visit(root) for root in roots)


def check_exhaustive_one_node(assignments: tuple[Graph, ...]):
    nodes = one_node_bound_nodes()
    checked = 0
    residuals_total = 0
    visited_total = 0
    for left, left_node in enumerate(nodes):
        for right, right_node in enumerate(nodes):
            bound = Bound(nodes, left, right)
            closed_ok, residuals, visited = normalize(bound)
            for x in assignments:
                for y in assignments:
                    if not is_closed(x) or not is_closed(y):
                        raise AssertionError("assignment domain must be closed")
                    instance, roots = instantiate(bound, {"x": x, "y": y})
                    direct = subtype_gfp(instance, roots[left], roots[right])
                    normalized = closed_ok and residual_holds(bound, residuals, {"x": x, "y": y})
                    assert direct == normalized, (bound, x, y, closed_ok, residuals, direct, normalized)
                    checked += 1
                    residuals_total += len(residuals)
                    visited_total += visited
    return checked, residuals_total, visited_total


def check_recursive_assignment_copy():
    bound = Bound(
        (variable("x"), atom("A"), record((("a", 1),))),
        0,
        2,
    )
    recursive_record = Graph((record((("a", 0),)),), 0)
    instantiated, roots = instantiate(bound, {"x": recursive_record, "y": recursive_record})
    assigned_root = roots[bound.left]
    assert instantiated[assigned_root] == record((("a", assigned_root),))
    direct = subtype_gfp(instantiated, assigned_root, roots[bound.right])
    closed_ok, residuals, _ = normalize(bound)
    normalized = closed_ok and residual_holds(
        bound, residuals, {"x": recursive_record, "y": recursive_record}
    )
    assert direct is False and normalized is False
    return assigned_root, direct, normalized


def check_cyclic_residual_both_outcomes():
    # Two distinct recursive Function roots revisit the same descriptor pair.
    # Their argument comparison is residual and determines satisfiability.
    bound = Bound(
        (variable("x"), atom("A"), function(0, 2), function(1, 3)),
        2,
        3,
    )
    closed_ok, residuals, visits = normalize(bound)
    assert closed_ok and len(residuals) == 1 and visits == 2
    good = {"x": Graph((atom("A"),), 0), "y": Graph((atom("A"),), 0)}
    bad = {"x": Graph((atom("B"),), 0), "y": Graph((atom("A"),), 0)}
    good_nodes, good_roots = instantiate(bound, good)
    bad_nodes, bad_roots = instantiate(bound, bad)
    direct_good = subtype_gfp(good_nodes, good_roots[2], good_roots[3])
    direct_bad = subtype_gfp(bad_nodes, bad_roots[2], bad_roots[3])
    normalized_good = residual_holds(bound, residuals, good)
    normalized_bad = residual_holds(bound, residuals, bad)
    assert direct_good and normalized_good
    assert not direct_bad and not normalized_bad
    return visits, len(residuals), direct_good, direct_bad


def check_random_recursive(assignments: tuple[Graph, ...]):
    rng = Random(20261005)
    checked = 0
    residuals_total = 0
    visited_total = 0
    recursive_bounds = 0
    compact_sizes: list[int] = []
    for _ in range(320):
        bound = random_bound(rng, rng.choice((2, 3, 4)))
        compact_sizes.append(len(bound.nodes))
        closed_ok, residuals, visited = normalize(bound)
        if has_cycle(bound.nodes, (bound.left, bound.right)):
            recursive_bounds += 1
        for _ in range(48):
            x, y = rng.choice(assignments), rng.choice(assignments)
            instance, roots = instantiate(bound, {"x": x, "y": y})
            direct = subtype_gfp(instance, roots[bound.left], roots[bound.right])
            normalized = closed_ok and residual_holds(bound, residuals, {"x": x, "y": y})
            assert direct == normalized, (bound, x, y, closed_ok, residuals, direct, normalized)
            checked += 1
            residuals_total += len(residuals)
            visited_total += visited
    return (
        checked,
        residuals_total,
        visited_total,
        recursive_bounds,
        min(compact_sizes),
        max(compact_sizes),
        Counter(compact_sizes),
    )


def main() -> None:
    assignments = generated_closed_graphs()
    exhaustive = check_exhaustive_one_node(assignments)
    copy_root, copy_direct, copy_normalized = check_recursive_assignment_copy()
    cycle_visits, cycle_residuals, cycle_good, cycle_bad = check_cyclic_residual_both_outcomes()
    recursive = check_random_recursive(assignments)
    joint = check_recursive_joint_packages()
    x_only, y_only, common, without_phi = check_joint_phi_obstruction()
    print(
        "selected 15-node shallow endpoint graph: "
        f"{len(one_node_bound_nodes()) ** 2} endpoint pairs × {len(assignments) ** 2} assignments "
        f"= {exhaustive[0]} checks; residual instances={exhaustive[1]}; visits={exhaustive[2]}"
    )
    print(
        "assignment graph-copy check: recursive Record child points to its copied self "
        f"at node {copy_root}; direct={copy_direct}, normalized={copy_normalized}"
    )
    print(
        "distinct cyclic-bound witness: "
        f"{cycle_visits} normalized pair visits, {cycle_residuals} residual; "
        f"x=A direct={cycle_good}, x=B direct={cycle_bad}, both match residual replay"
    )
    print(
        "seeded recursive bounds: 320 graphs sampled with 2–4 slots "
        f"({recursive[4]}–{recursive[5]} reachable nodes after compaction; "
        f"histogram={dict(sorted(recursive[6].items()))}), "
        f"{recursive[3]} cyclic graphs × 48 assignments = {recursive[0]} checks; "
        f"residual instances={recursive[1]}; visits={recursive[2]}"
    )
    print(
        "recursive joint packages: "
        f"{joint[0]} packages, {joint[1]} Phi-admitted assignment pairs, "
        f"{joint[2]} bound checks; {joint[3]} include cycles; "
        f"{joint[4]} have a joint solution; exact x/y projections preserved"
    )
    print(
        f"retained-Phi witness: separate x-bound={x_only}, "
        f"separate y-bound={y_only}, common tuple={common}, "
        f"dropping Phi admits a tuple={without_phi}"
    )
    print(
        "scope: pure regular graphs with atoms A/B, Function and mandatory "
        "Records {a,b}, plus supplied finite extensional Phi; no source-derived "
        "Phi/K,D, lexical guards, effects, source generation, or production solver"
    )


if __name__ == "__main__":
    main()
