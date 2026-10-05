#!/usr/bin/env python3
"""Probe one possible source-evidence projection for protection release.

BoundaryProfile, Flow, Observe, Receive, Path, and Incidence are modeled as
query-time evidence. All source attribution, event paths, handler grants, and
fixed K,D dependencies are supplied. The candidate that a qualifying typed
route crosses a marked slot is only one possible way to locate release; it is
not the definition of `'e?` and is not established source semantics. The local
protection-only frame is the selected meaning; this probe asks whether one
existing-evidence projection could identify its scope. It is not a source
elaborator or a production solver model.
"""

from dataclasses import dataclass, replace
from collections import deque
from itertools import product


@dataclass(frozen=True)
class Effect:
    event: str
    source: str
    family: str
    arguments: tuple[str, ...]
    origin: str
    k: tuple[str, ...]
    d: tuple[str, ...]


@dataclass(frozen=True)
class Profile:
    profile: str
    component: str
    source_slot: str
    receiver: str


@dataclass(frozen=True)
class Flow:
    component: str
    path: str
    source_slot: str
    target_slot: str


@dataclass(frozen=True)
class Observe:
    event: str
    view: str
    slot: str
    component: str
    path: str


@dataclass(frozen=True)
class Receive:
    receiver: str
    view: str
    path: str


@dataclass(frozen=True)
class ReleaseMark:
    component: str
    slot: str


@dataclass(frozen=True)
class PathWitness:
    event: str
    profile: str
    component: str
    view: str
    path: str
    source_slot: str
    target_slot: str


@dataclass(frozen=True)
class Case:
    effects: tuple[Effect, ...]
    profiles: tuple[Profile, ...]
    flows: tuple[Flow, ...]
    observations: tuple[Observe, ...]
    receives: tuple[Receive, ...]
    marks: tuple[ReleaseMark, ...]
    active_owners: frozenset[str]
    active_handlers: frozenset[str]
    handler_owners: tuple[tuple[str, str], ...]
    handler_families: tuple[tuple[str, frozenset[str]], ...]
    grants: frozenset[tuple[str, str]]


def flow_reaches(case: Case, profile: Profile, target: str, path: str) -> bool:
    """Mark-independent reachability for the ordinary typed Path relation."""
    adjacency: dict[str, list[str]] = {}
    for edge in case.flows:
        if edge.component == profile.component and edge.path == path:
            adjacency.setdefault(edge.source_slot, []).append(edge.target_slot)
    queue = deque([profile.source_slot])
    seen = {profile.source_slot}
    while queue:
        current = queue.popleft()
        if current == target:
            return True
        for nxt in adjacency.get(current, ()):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return False


def release_route_states(case: Case, witness: PathWitness) -> frozenset[bool]:
    """Candidate query: whether typed routes cross a marked slot.

    This is a tested projection hypothesis, not the semantic meaning of the
    marker. Path/lineage evidence locates a contribution and candidate slot;
    it does not define the protection transition.
    """
    marks = {mark.slot for mark in case.marks
             if mark.component == witness.component}
    start_crossed = witness.source_slot in marks
    start = (witness.source_slot, start_crossed)
    queue = deque([start])
    seen = {start}
    outcomes: set[bool] = set()
    adjacency: dict[str, list[str]] = {}
    for edge in case.flows:
        if edge.component == witness.component and edge.path == witness.path:
            adjacency.setdefault(edge.source_slot, []).append(edge.target_slot)
    while queue:
        slot, crossed = queue.popleft()
        if slot == witness.target_slot:
            outcomes.add(crossed)
        # Keep exploring after exposure: cyclic paths may reach the same target
        # again after crossing the marked slot.
        for nxt in adjacency.get(slot, ()):
            state = (nxt, crossed or nxt in marks)
            if state not in seen:
                seen.add(state)
                queue.append(state)
    return frozenset(outcomes)


def graph_release_states(size: int, edges: frozenset[tuple[int, int]],
                         marks: frozenset[int], source: int,
                         target: int) -> frozenset[bool]:
    """Product-graph reachability for a finite typed Flow graph."""
    adjacency = {node: [] for node in range(size)}
    for left, right in edges:
        adjacency[left].append(right)
    initial = (source, source in marks)
    queue = deque([initial])
    seen = {initial}
    outcomes: set[bool] = set()
    while queue:
        node, crossed = queue.popleft()
        if node == target:
            outcomes.add(crossed)
        for nxt in adjacency[node]:
            state = (nxt, crossed or nxt in marks)
            if state not in seen:
                seen.add(state)
                queue.append(state)
    return frozenset(outcomes)


def bounded_walk_release_states(size: int, edges: frozenset[tuple[int, int]],
                                marks: frozenset[int], source: int,
                                target: int) -> frozenset[bool]:
    """Independent bounded-walk reference for the finite product query.

    The product graph has 2*size states, so any reachable outcome has a
    simple product-state witness of at most 2*size-1 edges.
    """
    adjacency = {node: [] for node in range(size)}
    for left, right in edges:
        adjacency[left].append(right)
    outcomes: set[bool] = set()

    def walk(node: int, crossed: bool, remaining: int) -> None:
        if node == target:
            outcomes.add(crossed)
        if remaining == 0:
            return
        for nxt in adjacency[node]:
            walk(nxt, crossed or nxt in marks, remaining - 1)

    walk(source, source in marks, 2 * size - 1)
    return frozenset(outcomes)


def path_witnesses(case: Case, event: str, handler: str) -> frozenset[PathWitness]:
    owner = dict(case.handler_owners)[handler]
    receives = {(r.receiver, r.view, r.path) for r in case.receives}
    witnesses: set[PathWitness] = set()
    for profile in case.profiles:
        for obs in case.observations:
            if obs.event != event or obs.component != profile.component:
                continue
            if (owner, obs.view, obs.path) not in receives:
                continue
            if flow_reaches(case, profile, obs.slot, obs.path):
                witnesses.add(PathWitness(event, profile.profile, profile.component,
                                          obs.view, obs.path, profile.source_slot,
                                          obs.slot))
    return frozenset(witnesses)


def incidences(case: Case, event: str, handler: str) -> frozenset[PathWitness]:
    owner = dict(case.handler_owners)[handler]
    if handler not in case.active_handlers or owner not in case.active_owners:
        return frozenset()
    return frozenset(
        witness for witness in path_witnesses(case, event, handler)
        if next(profile.receiver for profile in case.profiles
                if profile.profile == witness.profile) in case.active_owners
    )


def released(case: Case, witness: PathWitness) -> bool:
    """Candidate route-crossing projection for the local release operation."""
    states = release_route_states(case, witness)
    # Preserve protection if any actual typed route bypasses the marked slot.
    return bool(states) and False not in states


def visible(case: Case, effect: Effect, handler: str) -> bool:
    if handler not in case.active_handlers:
        return False
    owner = dict(case.handler_owners)[handler]
    if owner not in case.active_owners:
        return False
    if effect.family not in dict(case.handler_families)[handler]:
        return False
    witnesses = incidences(case, effect.event, handler)
    protected = any(
        False in release_route_states(case, witness) for witness in witnesses
    )
    return not protected or (effect.event, handler) in case.grants


def family_wide_visible(case: Case, effect: Effect, handler: str) -> bool:
    """Deliberately wrong: any marked source family releases all its events."""
    if handler not in case.active_handlers:
        return False
    if effect.family not in dict(case.handler_families)[handler]:
        return False
    released_families = {
        candidate.family for candidate in case.effects
        if candidate.source == "e"
    }
    witnesses = incidences(case, effect.event, handler)
    protected = any(
        not (witness.component == "e" or effect.family in released_families)
        for witness in witnesses
    )
    return not protected or (effect.event, handler) in case.grants


def sticky_visible(case: Case, effect: Effect, handler: str) -> bool:
    """Deliberately wrong: every raw incidence remains protective forever."""
    if handler not in case.active_handlers:
        return False
    if effect.family not in dict(case.handler_families)[handler]:
        return False
    return not incidences(case, effect.event, handler) or (effect.event, handler) in case.grants


def make_case(*, source: str, local_event: bool, active_receiver: bool,
              active_handler: bool, latent: bool = False, overlap: bool = False,
              resumed: bool = False, handler_owner: str = "receiver",
              active_handler_owner: bool = True) -> Case:
    event = "q-resumed" if resumed else "q-input"
    e_path = "typed-e-path"
    e_source = "arg.e"
    e_output = "result.latent.e" if latent else "result.e"
    e_observe = "later.latent.e" if latent else e_output
    flows = [Flow(source, e_path, e_source, e_output)]
    if latent:
        flows.append(Flow(source, e_path, e_output, e_observe))
    profiles = [Profile("profile-e", source, e_source, "receiver")]
    observations = [Observe(event, "later-view", e_observe, source, e_path)]
    receives = [Receive("receiver", "later-view", e_path),
                Receive(handler_owner, "later-view", e_path)]
    effects = [Effect(event, source, "foo", ("int",), "origin-e", ("K-e",), ("D-e",))]
    marks = [ReleaseMark("e", e_output)]
    handler = "receiver-handler"
    families = [(handler, frozenset({"foo"}))]

    if local_event:
        local_path = "typed-local-path"
        profiles.append(Profile("profile-local", "local", "body.local", "receiver"))
        flows.append(Flow("local", local_path, "body.local", "result.local"))
        effects.append(Effect("q-local", "local", "foo", ("int",), "origin-local",
                              ("K-local",), ("D-local",)))
        observations.append(Observe("q-local", "later-view", "result.local",
                                     "local", local_path))
        receives.extend((Receive("receiver", "later-view", local_path),
                         Receive(handler_owner, "later-view", local_path)))

    if overlap:
        # Same dynamic event has another independently attributed path. The e
        # path is released; the local profile remains protective.
        local_path = "overlap-local-path"
        profiles.append(Profile("profile-overlap", "local", "body.overlap", "receiver"))
        flows.append(Flow("local", local_path, "body.overlap", e_observe))
        observations.append(Observe(event, "later-view", e_observe, "local", local_path))
        receives.extend((Receive("receiver", "later-view", local_path),
                         Receive(handler_owner, "later-view", local_path)))

    active_owners = set()
    if active_receiver:
        active_owners.add("receiver")
    if active_handler_owner:
        active_owners.add(handler_owner)
    active_handlers = frozenset({handler}) if active_handler else frozenset()
    return Case(tuple(effects), tuple(profiles), tuple(flows), tuple(observations),
                tuple(receives), tuple(marks), frozenset(active_owners), active_handlers,
                ((handler, handler_owner),), tuple(families), frozenset())


def main() -> None:
    checked = 0
    for source, active_receiver, active_handler in product(
        ("e", "local"), (False, True), (False, True)
    ):
        case = make_case(source=source, local_event=True,
                         active_receiver=active_receiver,
                         active_handler=active_handler,
                         active_handler_owner=active_receiver)
        before = case
        event = case.effects[0]
        e_attributed = source == "e"
        expected = active_handler and active_receiver and e_attributed
        assert visible(case, event, "receiver-handler") == expected
        assert case == before  # Release is a query projection, not evidence mutation.
        raw_incidence = incidences(case, event.event, "receiver-handler")
        if active_handler and active_receiver and e_attributed:
            assert raw_incidence
            assert all(released(case, path) for path in raw_incidence)
        if active_handler and active_receiver and not e_attributed:
            assert raw_incidence
            assert all(not released(case, path) for path in raw_incidence)
        checked += 1

    # Same family does not transfer the e path's release to a local event.
    same_family = make_case(source="e", local_event=True,
                            active_receiver=True, active_handler=True)
    local = next(effect for effect in same_family.effects if effect.source == "local")
    assert local.family == same_family.effects[0].family
    assert not visible(same_family, local, "receiver-handler")
    assert family_wide_visible(same_family, local, "receiver-handler")
    checked += 1

    # A later latent observation reaches the mark on its typed result path.
    latent = make_case(source="e", local_event=False, active_receiver=True,
                       active_handler=True, latent=True)
    assert visible(latent, latent.effects[0], "receiver-handler")
    latent_paths = incidences(latent, latent.effects[0].event, "receiver-handler")
    assert latent_paths and all(released(latent, path) for path in latent_paths)
    assert not sticky_visible(latent, latent.effects[0], "receiver-handler")
    # Mark changes affect only the eligibility projection, never raw Path or
    # Incidence identity.
    unmarked = replace(latent, marks=())
    assert path_witnesses(unmarked, latent.effects[0].event,
                          "receiver-handler") == path_witnesses(
                              latent, latent.effects[0].event, "receiver-handler")
    assert incidences(unmarked, latent.effects[0].event,
                      "receiver-handler") == latent_paths
    checked += 1

    # A provenance-erasure mutant removes the observation/path edge. The
    # original evidence is retained and still proves attribution after release.
    erased = replace(latent, observations=())
    assert latent_paths
    assert not incidences(erased, latent.effects[0].event, "receiver-handler")
    assert incidences(latent, latent.effects[0].event, "receiver-handler") == latent_paths
    checked += 1

    # A separate local path for the same event preserves one unreleased
    # protection witness, so releasing e does not erase independent protection.
    overlap = make_case(source="e", local_event=False, active_receiver=True,
                        active_handler=True, latent=True, overlap=True)
    overlap_paths = incidences(overlap, overlap.effects[0].event, "receiver-handler")
    assert any(released(overlap, path) for path in overlap_paths)
    assert any(not released(overlap, path) for path in overlap_paths)
    assert not visible(overlap, overlap.effects[0], "receiver-handler")
    checked += 1

    # A resumed dynamic event keeps its own identity but can traverse the same
    # source-typed path and fixed symbolic dependencies.
    resumed = make_case(source="e", local_event=False, active_receiver=True,
                        active_handler=True, latent=True, resumed=True)
    assert resumed.effects[0].event != latent.effects[0].event
    assert resumed.effects[0].origin == latent.effects[0].origin
    assert resumed.effects[0].k == latent.effects[0].k
    assert resumed.effects[0].d == latent.effects[0].d
    assert visible(resumed, resumed.effects[0], "receiver-handler")
    checked += 1

    # Raw Path persists after the maker receiver expires; Incidence filters it.
    # The independent outer handler remains active and uses ordinary coverage.
    expired = make_case(source="e", local_event=False, active_receiver=False,
                        active_handler=True, latent=True, handler_owner="outer",
                        active_handler_owner=True)
    assert path_witnesses(expired, expired.effects[0].event, "receiver-handler")
    assert not incidences(expired, expired.effects[0].event, "receiver-handler")
    assert visible(expired, expired.effects[0], "receiver-handler")
    checked += 1

    # Candidate-owner expiry independently suppresses incidence and visibility
    # even when the original callback receiver remains active.
    owner_expired = make_case(source="e", local_event=False, active_receiver=True,
                              active_handler=True, latent=True, handler_owner="outer",
                              active_handler_owner=False)
    assert path_witnesses(owner_expired, owner_expired.effects[0].event,
                          "receiver-handler")
    assert not incidences(owner_expired, owner_expired.effects[0].event,
                          "receiver-handler")
    assert not visible(owner_expired, owner_expired.effects[0], "receiver-handler")
    checked += 1

    # A cyclic Flow graph may have both a path crossing the marked slot and a
    # bypass path. The product-state search finds both; the unreleased witness
    # conservatively keeps this event protected.
    cyclic = make_case(source="e", local_event=False, active_receiver=True,
                       active_handler=True)
    cyclic = replace(
        cyclic,
        marks=(ReleaseMark("e", "marked.e"),),
        flows=cyclic.flows + (
            Flow("e", "typed-e-path", "arg.e", "marked.e"),
            Flow("e", "typed-e-path", "marked.e", "arg.e"),
        ),
    )
    cyclic_paths = incidences(cyclic, cyclic.effects[0].event, "receiver-handler")
    assert {state for path in cyclic_paths
            for state in release_route_states(cyclic, path)} == {False, True}
    assert not visible(cyclic, cyclic.effects[0], "receiver-handler")
    checked += 1

    # A finite walk may reach the exposure slot, leave it, cross the marker,
    # then revisit exposure. The product-state search must continue afterward.
    after_target_cycle = replace(
        cyclic,
        marks=(ReleaseMark("e", "after.exposure"),),
        flows=(
            Flow("e", "typed-e-path", "arg.e", "result.e"),
            Flow("e", "typed-e-path", "result.e", "after.exposure"),
            Flow("e", "typed-e-path", "after.exposure", "result.e"),
        ),
    )
    after_paths = incidences(after_target_cycle,
                             after_target_cycle.effects[0].event,
                             "receiver-handler")
    assert {state for path in after_paths
            for state in release_route_states(after_target_cycle, path)} == {False, True}
    assert not visible(after_target_cycle, after_target_cycle.effects[0],
                       "receiver-handler")
    checked += 1

    # Exhaust all directed typed-Flow graphs through three positions, every
    # marker subset, and every source/observation pair. Compare the worklist
    # product query with bounded raw walks, which includes cycle-then-return
    # paths that a node-simple walk would miss.
    graph_graphs = 0
    graph_configurations = 0
    for size in range(1, 4):
        possible_edges = tuple(product(range(size), repeat=2))
        for edge_bits in range(1 << len(possible_edges)):
            graph_graphs += 1
            edges = frozenset(edge for index, edge in enumerate(possible_edges)
                              if edge_bits & (1 << index))
            for mark_bits in range(1 << size):
                marks = frozenset(node for node in range(size)
                                  if mark_bits & (1 << node))
                for source, target in product(range(size), repeat=2):
                    assert graph_release_states(size, edges, marks, source, target) == \
                        bounded_walk_release_states(size, edges, marks, source, target)
                    graph_configurations += 1

    print(f"typed-path projection cases checked: {checked}")
    print(f"finite Flow graph structures checked: {graph_graphs} (all through 3 positions)")
    print(f"Flow graph/mark/source/target configurations checked: {graph_configurations}")
    print("candidate slot-location query preserves raw Path/Incidence: confirmed")
    print("same-family local path and independent overlapping protection survive: confirmed")
    print("latent/resumed paths, receiver/owner expiry, and cyclic Flow characterized: confirmed")
    print("family-wide, sticky-protection, and provenance-erasure mutants rejected: confirmed")
    print("scope: route-crossing is only a projection hypothesis; protection-only meaning is separate")
    print("scope: supplied Flow/Observe/Receive/Rel_C-shaped evidence; no source derivation or adequacy theorem")


if __name__ == "__main__":
    main()
