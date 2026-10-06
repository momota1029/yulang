#!/usr/bin/env python3
"""Two source-constructor path placements, not a parsed-program checker.

The exact approved apply/step body supplies its static upper fragment. An
independently typed open-client factory emits a request and returns a callable.
This model tests WHERE formal-local introduction can put that fragment before
Value entry rebind. It proves neither SourceViewInst nor factory admission.
"""
from dataclasses import dataclass
import json
import resource


@dataclass(frozen=True)
class Position:
    source: str
    path: tuple[str, ...]


@dataclass(frozen=True)
class Fragment:
    seed: str
    upper_use: str
    source_position: Position
    current_path: tuple[str, ...]
    receiver: str


def argument_result_path(path: tuple[str, ...]) -> tuple[str, ...]:
    # Whole argument is a computation producing the formal's value.
    return ("result",) + path


def rebind_result(fragment: Fragment) -> Fragment | None:
    # Entry Force returns the value. Only result paths reach that value.
    if fragment.current_path[:1] != ("result",):
        return None
    return Fragment(fragment.seed, fragment.upper_use, fragment.source_position,
                    fragment.current_path[1:], fragment.receiver)


def checks() -> dict[str, object]:
    # Registration -> Name resolved to that formal -> original upper Call.
    # There is no arbitrary At flag, solved type, Q, or global value equality.
    formal = "apply/formal:f"
    captured_name = {"step/name:f": formal}
    assert captured_name["step/name:f"] == formal
    original_upper = Position("step/call:f-x:upper", ("call", "effect"))
    original_lower = Position("provider:lower", ("call", "effect"))
    seed = "absence-of-annotation:" + formal
    # Candidate formal-local introduction uses the original receiving apply
    # invocation; this is a placement candidate, not a proved source boundary.
    correct = Fragment(seed, original_upper.source, original_upper,
                       argument_result_path(original_upper.path), "apply#1")
    flattened = Fragment(seed, original_upper.source, original_upper,
                         ("effect",), "apply#1")
    # Source constructor observations in the independently typed factory graph:
    # Request is at the carrier computation port; Return moves the returned
    # callable under result, and its later Call uses its own call.effect path.
    factory_request = ("effect",)
    returned_callable_call = ("result", "call", "effect")
    def incidence(mark: Fragment, observed: tuple[str, ...]) -> bool:
        return mark.current_path == observed
    # Literal independent path expectations from Comp(E_arg, Value(Function)).
    assert correct.current_path == ("result", "call", "effect")
    assert (incidence(correct, factory_request),
            incidence(correct, returned_callable_call)) == (False, True)
    assert (incidence(flattened, factory_request),
            incidence(flattened, returned_callable_call)) == (True, False)
    rebound = rebind_result(correct)
    assert rebound is not None and rebound.current_path == ("call", "effect")
    assert rebind_result(flattened) is None
    assert rebound.receiver == "apply#1"
    assert rebound.source_position == original_upper != original_lower
    # Equal endpoint valuations cannot collapse original upper/lower positions.
    endpoints = {original_upper: 0, original_lower: 0}
    assert endpoints[original_upper] == endpoints[original_lower]
    assert original_lower != rebound.source_position
    # A protection-sensitive predicate can discriminate BEFORE receiver expiry:
    # use only the supplied Boolean kernel, not an implementation of Visible.
    active_no_grant_kernel = lambda protected: not protected
    assert active_no_grant_kernel(incidence(correct, factory_request))
    assert not active_no_grant_kernel(incidence(flattened, factory_request))
    return {"source_fixture": "approved apply/step plus supplied typed factory client",
            "correct_before_rebind": list(correct.current_path),
            "correct_after_rebind": list(rebound.current_path),
            "correct_incidence_make_call": [False, True],
            "flattened_incidence_make_call": [True, False],
            "placement_shortcut_rejected": "formal value path becomes carrier effect",
            "source_view_inst_totality_proved": False,
            "factory_admission_proved": False,
            "production_acceptance_tested": False}


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (55, 55))
    print(json.dumps(checks(), sort_keys=True))
