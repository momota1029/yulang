#!/usr/bin/env python3
"""Check the 36 captured F5c resource matrix rows; never launch a solve."""

import argparse
from pathlib import Path
import struct
import sys

PREFIX = "F5C_RESOURCE_MATRIX_ROW\t"
OWNER_PREFIX = "F5C_RESOURCE_MATRIX_OWNER\t"
SIDECAR_PREFIX = "F5C_RESOURCE_MATRIX_SIDECAR\t"
EVENT_MAGIC = b"F5CRES01"
EVENT = struct.Struct("<8Q")
MAX_RECORD_LENGTH = 65536
SIZES = (1000, 2000, 4000)
FAMILY_ENDS = (18, 24, 45, 65, 101, 129, 230, 237)
FRONT = (
    "live_components", "value_bounds", "effect_bounds", "value_levels",
    "effect_levels", "value_metadata", "effect_metadata", "extrusion_stack",
    "extrusion_value_marks", "extrusion_effect_marks", "value_direct_lower",
    "value_direct_upper", "value_exact_lower", "value_exact_upper",
    "effect_direct_lower", "effect_direct_upper", "effect_exact_lower",
    "effect_exact_upper", *(f"term_{i}" for i in range(6)),
    "typed_pairs", "diagnostic_edges", "typed_worklist", "diagnostic_delta",
    "diagnostic_delta_indices", "diagnostic_reverse_offsets", "diagnostic_reverse_edges",
    "diagnostic_reverse_cursors", "diagnostic_dfs_stack", "diagnostic_finish_order",
    "diagnostic_scc_indices", "diagnostic_scc_nodes", "diagnostic_scc_offsets",
    "diagnostic_scc_pending_children", "diagnostic_scc_worklist", "diagnostic_bucket_heads",
    "diagnostic_bucket_tails", "diagnostic_bucket_candidates", "diagnostic_node_witnesses",
    "errors", "reported_errors",
)
LANE_NAMES = (
    *FRONT, *(f"component_memo_{i}" for i in range(20)),
    *(f"closed_arena_{i}" for i in range(8)),
    *(f"closed_scratch_{i}" for i in range(17)),
    *(f"closed_indexed_{i}" for i in range(11)),
    *(f"normalization_{i}" for i in range(28)),
    "aggregate_source_draft_slots", "aggregate_source_bound_tokens",
    "aggregate_source_recursive_bounds",
    *(f"generalization_walker_{i}" for i in range(98)),
    *(f"instantiation_{i}" for i in range(7)),
    *(f"route_store_{i}" for i in range(4)),
    *(f"routed_use_{i}" for i in range(2)),
)
FAMILY_NAMES = (
    "live_variable_tables", "inference_type_arena", "structured_pair_memo",
    "component_expansion_memo", "closed_type_arena", "closed_normalization_index",
    "generalization_scratch", "instantiation_substitution", "outside_family",
)
LANE_IDENTITIES = tuple(
    f"{FAMILY_NAMES[next((family for family, end in enumerate(FAMILY_ENDS) if index < end), 8)]}/{name}"
    for index, name in enumerate(LANE_NAMES)
)
SERIES = {
    ("IndependentIdentities", "D", "none"),
    ("IdentityAliases", "U", "none"),
    ("ArenaFactor", "M", "1000"),
    ("ArenaFactor", "U", "1000"),
}
for family in ("SharedAcyclic", "IndependentAcyclic", "Normalization"):
    SERIES.add((family, "D", "8"))
    SERIES.add((family, "K", "8"))
SERIES.add(("GuardedCycle", "D", "4000"))
SERIES.add(("GuardedCycle", "K", "8"))


def parse_line(line, source):
    fields = dict(part.split("=", 1) for part in line[len(PREFIX):].split("\t"))
    if set(fields) != {"family", "dimension", "size", "companion", "family_ends", "family_totals", "family1_event", "family3_event", "family4_event", "family6_event", "semantic_retained", "semantic_peak", "session_retained", "session_peak", "lanes"}:
        raise ValueError(f"{source}: unexpected or missing row fields")
    key = (fields["family"], fields["dimension"], fields["companion"])
    size = int(fields["size"])
    if key not in SERIES or size not in SIZES:
        raise ValueError(f"{source}: unexpected row {key} size {size}")
    ends = tuple(int(n.strip()) for n in fields["family_ends"].strip("[]").split(","))
    totals = tuple(tuple(int(n) for n in family.split(","))
                   for family in fields["family_totals"].split(";"))
    family6_event = tuple(int(n) for n in fields["family6_event"].split(","))
    family3_event = tuple(int(n) for n in fields["family3_event"].split(","))
    family4_event = tuple(int(n) for n in fields["family4_event"].split(","))
    family1_event = tuple(int(n) for n in fields["family1_event"].split(","))
    if len(family1_event) != 3 or min(family1_event) < 0:
        raise ValueError(f"{source}: incomplete family-1 owner event witness")
    if len(family6_event) != 6 or min(family6_event) < 0 or family6_event[3] == 0 or family6_event[4] == 0:
        raise ValueError(f"{source}: incomplete family-6 owner event witness")
    if len(family3_event) != 3 or min(family3_event) < 0:
        raise ValueError(f"{source}: incomplete family-3 owner event witness")
    if len(family4_event) != 3 or min(family4_event) < 0:
        raise ValueError(f"{source}: incomplete family-4 owner event witness")
    aggregate = tuple(int(fields[name]) for name in
                      ("semantic_retained", "semantic_peak", "session_retained", "session_peak"))
    if min(aggregate) < 0 or aggregate[1] < aggregate[0] or aggregate[3] < aggregate[2]:
        raise ValueError(f"{source}: invalid aggregate retained/peak values")
    named_lanes = tuple(lane.split(":", 1) for lane in fields["lanes"].split(";"))
    if tuple(name for name, _ in named_lanes) != LANE_IDENTITIES:
        raise ValueError(f"{source}: missing, duplicate, reordered, or unexpected lane identity")
    lanes = tuple(tuple(int(n) for n in values.split(",")) for _, values in named_lanes)
    if ends != FAMILY_ENDS:
        raise ValueError(f"{source}: invalid eight-family boundaries")
    if ends[-1] + 6 != len(lanes) or any(len(lane) != 6 or min(lane) < 0 for lane in lanes):
        raise ValueError(f"{source}: invalid physical lane data")
    if len(totals) != 8 or any(len(total) != 3 or min(total) < 0 for total in totals):
        raise ValueError(f"{source}: expected eight family reductions")
    for lane in lanes:
        actual, maximum, retained, observed_retained, peak, slot_size = lane
        if retained != actual * slot_size or maximum < actual or observed_retained < retained or peak < observed_retained:
            raise ValueError(f"{source}: inconsistent physical lane tuple")
    start = 0
    for end, (capacity, retained, peak) in zip(ends, totals):
        if capacity != sum(lane[0] for lane in lanes[start:end]) or retained != sum(lane[2] for lane in lanes[start:end]) or peak < retained:
            raise ValueError(f"{source}: family reduction does not reconcile")
        start = end
    if family6_event[2] != totals[6][2]:
        raise ValueError(f"{source}: family-6 event and owner aggregate peaks differ")
    if family3_event != totals[2]:
        raise ValueError(f"{source}: family-3 event and owner aggregate differ")
    if family4_event != totals[3]:
        raise ValueError(f"{source}: family-4 event and owner aggregate differ")
    if family1_event != totals[0]:
        raise ValueError(f"{source}: family-1 event and owner aggregate differ")
    return key, size, ends, totals, aggregate, lanes, family1_event, family3_event, family4_event, family6_event


def parse_owner(line, source):
    fields = dict(part.split("=", 1) for part in line[len(OWNER_PREFIX):].split("\t"))
    names = {"family", "dimension", "size", "companion", "component", "id", "kind",
             "requested", "peak_requested", "capacity", "peak_capacity", "slot_size",
             "retained", "peak_bytes", "growths", "transfers", "released"}
    if set(fields) != names:
        raise ValueError(f"{source}: incomplete family-6 physical owner")
    key = (fields["family"], fields["dimension"], fields["companion"])
    size = int(fields["size"])
    numeric = {name: int(fields[name]) for name in names - {"family", "dimension", "size", "companion", "kind"}}
    if min(numeric.values()) < 0 or numeric["released"] not in (0, 1):
        raise ValueError(f"{source}: invalid owner numeric field")
    if numeric["requested"] > numeric["peak_requested"] or numeric["capacity"] > numeric["peak_capacity"]:
        raise ValueError(f"{source}: invalid owner requested/capacity peak")
    if numeric["retained"] != numeric["capacity"] * numeric["slot_size"] or numeric["peak_bytes"] != numeric["peak_capacity"] * numeric["slot_size"]:
        raise ValueError(f"{source}: invalid owner byte equation")
    if numeric["released"] and (numeric["capacity"] or numeric["requested"]):
        raise ValueError(f"{source}: released owner retains capacity or requested slots")
    if fields["kind"] == "Unclassified":
        raise ValueError(f"{source}: unclassified family-6 owner")
    return key, size, fields["kind"], numeric


def replay_f6_events(path, expected_count, expected_checksum):
    """Replay family-tagged owner events in file order with simultaneous lane peaks."""
    owners = {}
    last_id = 0
    family_current = {1: [0, 0], 3: [0, 0], 4: [0, 0], 6: [0, 0]}
    family_peak = {1: 0, 3: 0, 4: 0, 6: 0}
    lane_current = {}
    lane_peak = {}
    checkpoints = {}
    checkpoint_by_kind = None
    family3_transfers = 0
    count = checksum = 0

    def family_of(kind):
        if 551 <= kind < 571:
            return 4
        if 530 <= kind < 551:
            return 3
        if 512 <= kind < 530:
            return 1
        if 0 <= kind < 512:
            return 6
        raise ValueError(f"{path}: unknown owner kind {kind}")

    def adjust(kind, capacity_delta, bytes_delta):
        family = family_of(kind)
        totals = family_current[family]
        totals[0] += capacity_delta
        totals[1] += bytes_delta
        if min(totals) < 0:
            raise ValueError(f"{path}: negative family-{family} total")
        family_peak[family] = max(family_peak[family], totals[1])
        lane = lane_current.setdefault(kind, [0, 0])
        lane[0] += capacity_delta
        lane[1] += bytes_delta
        if min(lane) < 0:
            raise ValueError(f"{path}: negative lane {kind}")
        maxima = lane_peak.setdefault(kind, [0, 0])
        maxima[0] = max(maxima[0], lane[0])
        maxima[1] = max(maxima[1], lane[1])

    with path.open("rb") as stream:
        if stream.read(len(EVENT_MAGIC)) != EVENT_MAGIC:
            raise ValueError(f"{path}: invalid event header")
        while block := stream.read(EVENT.size):
            if len(block) != EVENT.size:
                raise ValueError(f"{path}: truncated event")
            component, owner_id, op, kind, requested, actual, size, target = EVENT.unpack(block)
            count += 1
            checksum = (checksum + sum(EVENT.unpack(block))) & ((1 << 64) - 1)
            key = (component, owner_id)
            if op == 6:
                family = 1 if kind == 512 else 3 if kind == 530 else 4 if kind == 551 else 6 if kind == 0 else None
                if family is None or owner_id or requested or target or (actual, size) != tuple(family_current[family]):
                    raise ValueError(f"{path}: invalid family checkpoint")
                if family in (1, 3, 4) and family in checkpoints:
                    raise ValueError(f"{path}: duplicate family-{family} checkpoint")
                checkpoints[family] = (actual, size)
                if family == 6:
                    if any(owner_kind == 0 for owner_kind, *_ in owners.values()):
                        raise ValueError(f"{path}: unclassified owner at family-6 checkpoint")
                    checkpoint_by_kind = {lane_kind: [*current, *lane_peak[lane_kind]]
                        for lane_kind, current in lane_current.items() if family_of(lane_kind) in (4, 6)}
                continue
            if 1 in checkpoints and family_of(kind) == 1 and op != 5:
                raise ValueError(f"{path}: family-1 mutation after checkpoint")
            if 3 in checkpoints and family_of(kind) == 3 and op != 5 and not (op == 4 and kind == 549):
                raise ValueError(f"{path}: family-3 mutation after checkpoint")
            if 4 in checkpoints and family_of(kind) == 4:
                raise ValueError(f"{path}: family-4 mutation after checkpoint")
            if op == 1:
                if owner_id <= last_id:
                    raise ValueError(f"{path}: owner IDs are not strictly increasing")
                last_id = owner_id
                if key in owners or requested > actual or size == 0 or target:
                    raise ValueError(f"{path}: invalid create {key}")
                owners[key] = (kind, requested, actual, size)
                adjust(kind, actual, actual * size)
            else:
                if key not in owners:
                    raise ValueError(f"{path}: mutation of unknown owner {key}")
                old_kind, old_requested, old_actual, old_size = owners[key]
                if op == 5:
                    if old_kind == 0 or actual or requested or kind != old_kind or size != old_size or target:
                        raise ValueError(f"{path}: release retains owner {key}")
                    del owners[key]
                    adjust(old_kind, -old_actual, -old_actual * old_size)
                elif op in (2, 3, 4):
                    if requested > actual or size == 0:
                        raise ValueError(f"{path}: invalid owner shape {key}")
                    if family_of(old_kind) == 4 and (op == 4 or kind != old_kind or size != old_size):
                        raise ValueError(f"{path}: family-4 lane cannot transfer or change slot size")
                    if op == 2 and family_of(old_kind) in (1, 3, 4) and (kind != old_kind or size != old_size or
                                    actual != old_actual or requested == old_requested):
                        raise ValueError(f"{path}: shape changes family-1/family-3 allocation or repeats shape {key}")
                    if op == 2 and target:
                        raise ValueError(f"{path}: invalid shape target {key}")
                    if op == 3 and (kind != old_kind or size != old_size or
                                    actual <= old_actual):
                        raise ValueError(f"{path}: growth changes owner shape {key}")
                    if op == 4 and target != kind:
                        raise ValueError(f"{path}: invalid atomic transfer {key}")
                    if op == 4 and family_of(kind) == 3:
                        if 3 not in checkpoints or kind != 549:
                            raise ValueError(f"{path}: only the errors owner may transfer after family-3 checkpoint")
                        if (kind != old_kind or requested != old_requested or
                                actual != old_actual or size != old_size):
                            raise ValueError(f"{path}: family-3 transfer changes the physical owner {key}")
                        family3_transfers += 1
                    if family_of(kind) != family_of(old_kind):
                        raise ValueError(f"{path}: cross-family owner transfer {key}")
                    adjust(old_kind, -old_actual, -old_actual * old_size)
                    owners[key] = (kind, requested, actual, size)
                    adjust(kind, actual, actual * size)
                else:
                    raise ValueError(f"{path}: unknown event operation {op}")
    if count != expected_count or checksum != expected_checksum:
        raise ValueError(f"{path}: event count/checksum mismatch")
    if set(checkpoints) != {1, 3, 4, 6} or any(any(family_current[family]) for family in (1, 4, 6)):
        raise ValueError(f"{path}: missing terminal checkpoint or unreleased owner capacity")
    if any(family_of(kind) == 4 for kind, *_ in owners.values()):
        raise ValueError(f"{path}: family-4 owner survives EOF")
    family3_live = [
        (kind, requested, capacity, size)
        for (component, owner_id), (kind, requested, capacity, size) in owners.items()
        if family_of(kind) == 3
    ]
    if len(family3_live) != 1 or family3_live[0][0] != 549 or family3_transfers != 1:
        raise ValueError(f"{path}: family-3 EOF must retain only the errors owner")
    if family_current[3] != [family3_live[0][2], family3_live[0][2] * family3_live[0][3]]:
        raise ValueError(f"{path}: family-3 EOF errors owner does not reconcile")
    return (
        (*checkpoints[6], family_peak[6]),
        checkpoint_by_kind,
        (*checkpoints[1], family_peak[1]),
        (*checkpoints[3], family_peak[3]),
        (*checkpoints[4], family_peak[4]),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", type=Path, nargs="+", help="captured matrix process logs")
    args = parser.parse_args()
    rows = {}
    owner_aggregates = {}
    for path in args.logs:
        with path.open(encoding="utf-8") as log:
            record = None
            sidecar = None
            while line := log.readline(MAX_RECORD_LENGTH + 1):
                if len(line) > MAX_RECORD_LENGTH:
                    raise ValueError(f"{path}: record exceeds {MAX_RECORD_LENGTH} characters")
                if line.startswith(PREFIX):
                    if record is not None:
                        raise ValueError(f"{path}: second matrix row")
                    record = line.rstrip("\n")
                elif line.startswith(SIDECAR_PREFIX):
                    if sidecar is not None:
                        raise ValueError(f"{path}: duplicate resource sidecar")
                    fields = dict(part.split("=", 1) for part in
                                  line[len(SIDECAR_PREFIX):].rstrip("\n").split("\t"))
                    if set(fields) != {"path"}:
                        raise ValueError(f"{path}: invalid resource sidecar record")
                    sidecar = Path(fields["path"])
        if record is None:
            raise ValueError(f"{path}: expected exactly one matrix row, found 0")
        if sidecar is None:
            raise ValueError(f"{path}: missing resource sidecar")
        key, size, ends, totals, aggregate, lanes, family1_event, family3_event, family4_event, family6_event = parse_line(record, path)
        if (key, size) in rows:
            raise ValueError(f"{path}: duplicate matrix row {key} size {size}")
        folded, by_kind, folded_family1, folded_family3, folded_family4 = replay_f6_events(sidecar, family6_event[4], family6_event[5])
        if folded != family6_event[:3]:
            raise ValueError(f"{path}: family-6 event fold differs from matrix row")
        if folded_family1 != family1_event:
            raise ValueError(f"{path}: family-1 event fold differs from matrix row")
        if folded_family3 != family3_event:
            raise ValueError(f"{path}: family-3 event fold differs from matrix row")
        if folded_family4 != family4_event:
            raise ValueError(f"{path}: family-4 event fold differs from matrix row")
        for lane, values in enumerate(lanes[45:65]):
            kind_values = by_kind.get(551 + lane, [0, 0, 0, 0])
            if (kind_values[0] != values[0] or kind_values[1] != values[2]
                    or kind_values[2] < values[1] or kind_values[3] < values[4]):
                raise ValueError(f"{path}: family-4 lane {lane} owner shape differs from matrix row")
        owner_aggregates[key, size] = by_kind
        rows[key, size] = ends, totals, aggregate, lanes
    expected = {(key, size) for key in SERIES for size in SIZES}
    if set(rows) != expected:
        raise ValueError(f"missing={sorted(expected - set(rows))}; unexpected={sorted(set(rows) - expected)}")
    for key in sorted(SERIES):
        for small, large in zip(SIZES, SIZES[1:]):
            old_kinds = owner_aggregates[key, small]
            new_kinds = owner_aggregates[key, large]
            for kind in sorted(set(old_kinds) | set(new_kinds)):
                old_values = old_kinds.get(kind, [0, 0, 0, 0])
                new_values = new_kinds.get(kind, [0, 0, 0, 0])
                for field, a, b in zip(("aggregate_current_capacity", "aggregate_current_retained",
                                        "aggregate_sum_instance_peak_capacity", "aggregate_sum_instance_peak_bytes"),
                                       old_values, new_values):
                    if a == b == 0:
                        continue
                    if a == 0 or 2 * b >= 5 * a:
                        raise ValueError(f"{key} {small}->{large} owner kind {kind} {field}: {b}/{a} is not <2.5")
            old_ends, _, old_aggregate, old_lanes = rows[key, small]
            new_ends, _, new_aggregate, new_lanes = rows[key, large]
            if old_ends != new_ends:
                raise ValueError(f"{key}: physical lane layout differs between {small} and {large}")
            for index, (old, new) in enumerate(zip(old_lanes, new_lanes)):
                for field, a, b in (
                    ("actual_capacity", old[0], new[0]),
                    ("retained_bytes", old[2], new[2]),
                    ("peak_bytes", old[4], new[4]),
                    ("maximum_capacity", old[1], new[1]),
                    ("maximum_retained_bytes", old[3], new[3]),
                ):
                    if a == 0 and b == 0:
                        continue
                    if a == 0:
                        raise ValueError(f"{key} {small}->{large} lane {index} {field}: undefined zero-to-nonzero ratio")
                    if 2 * b >= 5 * a:
                        raise ValueError(f"{key} {small}->{large} lane {index} {field}: {b}/{a} is not <2.5")
            old_totals = rows[key, small][1]
            new_totals = rows[key, large][1]
            for index, (old, new) in enumerate(zip(old_totals, new_totals)):
                for field, a, b in zip(("actual_capacity", "retained_bytes", "peak_bytes"), old, new):
                    if a == 0 and b == 0:
                        continue
                    if a == 0:
                        raise ValueError(f"{key} {small}->{large} family {index} {field}: undefined zero-to-nonzero ratio")
                    if 2 * b >= 5 * a:
                        raise ValueError(f"{key} {small}->{large} family {index} {field}: {b}/{a} is not <2.5")
            for field, a, b in zip(("semantic_retained", "semantic_peak", "session_retained", "session_peak"), old_aggregate, new_aggregate):
                if a == 0 and b == 0:
                    continue
                if a == 0:
                    raise ValueError(f"{key} {small}->{large} aggregate {field}: undefined zero-to-nonzero ratio")
                if 2 * b >= 5 * a:
                    raise ValueError(f"{key} {small}->{large} aggregate {field}: {b}/{a} is not <2.5")
    print("F5c resource matrix: 36 unique rows, 12 series, all adjacent physical ratios <2.5")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
