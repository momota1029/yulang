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
FAMILY_ENDS = (18, 24, 45, 65, 101, 129, 248, 255)
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
    *(f"source_nested_payload_{i}" for i in range(6)),
    "staged_outer", *(f"staged_buffer_{i}" for i in range(6)),
    *(f"indexed_buffer_{i}" for i in range(5)),
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


def parse_line(line, source, diagnostic=False):
    fields = dict(part.split("=", 1) for part in line[len(PREFIX):].split("\t"))
    if set(fields) != {"family", "dimension", "size", "companion", "family_ends", "family_totals", "family1_event", "family2_event", "family3_event", "family4_event", "closed_type_event", "closed_type_checkpoint_peak", "family5_event", "family5_growths", "family8_event", "family6_event", "semantic_retained", "semantic_peak", "session_retained", "session_peak", "lanes"}:
        raise ValueError(f"{source}: unexpected or missing row fields")
    key = (fields["family"], fields["dimension"], fields["companion"])
    size = int(fields["size"])
    if not (diagnostic and key == ("GuardedCycle", "D", "4000") and size == 32) and (key not in SERIES or size not in SIZES):
        raise ValueError(f"{source}: unexpected row {key} size {size}")
    ends = tuple(int(n.strip()) for n in fields["family_ends"].strip("[]").split(","))
    totals = tuple(tuple(int(n) for n in family.split(","))
                   for family in fields["family_totals"].split(";"))
    family6_event = tuple(int(n) for n in fields["family6_event"].split(","))
    family3_event = tuple(int(n) for n in fields["family3_event"].split(","))
    family4_event = tuple(int(n) for n in fields["family4_event"].split(","))
    closed_type_event = tuple(int(n) for n in fields["closed_type_event"].split(","))
    closed_type_checkpoint_peak = int(fields["closed_type_checkpoint_peak"])
    family5_event = tuple(int(n) for n in fields["family5_event"].split(","))
    family5_growths = tuple(int(n) for n in fields["family5_growths"].split(","))
    family8_event = tuple(int(n) for n in fields["family8_event"].split(","))
    family1_event = tuple(int(n) for n in fields["family1_event"].split(","))
    family2_event = tuple(int(n) for n in fields["family2_event"].split(","))
    if len(family1_event) != 3 or min(family1_event) < 0:
        raise ValueError(f"{source}: incomplete family-1 owner event witness")
    if len(family2_event) != 3 or min(family2_event) < 0:
        raise ValueError(f"{source}: incomplete family-2 owner event witness")
    if len(family6_event) != 6 or min(family6_event) < 0 or family6_event[3] == 0 or family6_event[4] == 0:
        raise ValueError(f"{source}: incomplete family-6 owner event witness")
    if len(family3_event) != 3 or min(family3_event) < 0:
        raise ValueError(f"{source}: incomplete family-3 owner event witness")
    if len(family4_event) != 3 or min(family4_event) < 0:
        raise ValueError(f"{source}: incomplete family-4 owner event witness")
    if len(closed_type_event) != 3 or min(closed_type_event) < 0 or closed_type_checkpoint_peak < 0:
        raise ValueError(f"{source}: incomplete closed-type owner witness")
    if len(family5_event) != 3 or min(family5_event) < 0:
        raise ValueError(f"{source}: incomplete family-5 owner event witness")
    if len(family5_growths) != 28 or min(family5_growths) < 0:
        raise ValueError(f"{source}: incomplete family-5 lane growth witness")
    if len(family8_event) != 3 or min(family8_event) < 0:
        raise ValueError(f"{source}: incomplete family-8 owner event witness")
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
    closed_lanes = lanes[65:101]
    if (closed_type_event != totals[4]
            or closed_type_event[:2] != (sum(lane[0] for lane in closed_lanes),
                                          sum(lane[2] for lane in closed_lanes))
            or closed_type_event[2] < max(lane[4] for lane in closed_lanes)
            or closed_type_event[2] > closed_type_checkpoint_peak
            or any(lane[0] or lane[2] for lane in lanes[73:101])):
        raise ValueError(f"{source}: closed-type aggregate owner witness differs from lanes or checkpoint")
    if family6_event[2] != totals[6][2]:
        raise ValueError(f"{source}: family-6 event and owner aggregate peaks differ")
    if family3_event != totals[2]:
        raise ValueError(f"{source}: family-3 event and owner aggregate differ")
    if family4_event != totals[3]:
        raise ValueError(f"{source}: family-4 event and owner aggregate differ")
    if family5_event != totals[5]:
        raise ValueError(f"{source}: family-5 event and owner aggregate differ")
    if family8_event != totals[7]:
        raise ValueError(f"{source}: family-8 event and owner aggregate differ")
    if family1_event != totals[0]:
        raise ValueError(f"{source}: family-1 event and owner aggregate differ")
    if family2_event != totals[1]:
        raise ValueError(f"{source}: family-2 event and owner aggregate differ")
    return key, size, ends, totals, aggregate, lanes, family1_event, family2_event, family3_event, family4_event, family5_event, family5_growths, family8_event, family6_event


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
    family_current = {1: [0, 0], 2: [0, 0], 3: [0, 0], 4: [0, 0], 5: [0, 0], 6: [0, 0], 8: [0, 0]}
    family_peak = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 8: 0}
    lane_current = {}
    lane_peak = {}
    row_current = {}
    row_peak = {}
    row_sizes = {}
    normalization_growth = {}
    checkpoints = {}
    checkpoint_by_kind = None
    term_checkpoint_by_kind = None
    instantiation_checkpoint_by_kind = None
    normalization_checkpoint_by_kind = None
    family3_transfers = 0
    family2_transfers = set()
    count = checksum = 0

    def family_of(kind):
        if 584 <= kind < 612:
            return 5
        if 577 <= kind < 584:
            return 8
        if 571 <= kind < 577:
            return 2
        if 551 <= kind < 571:
            return 4
        if 530 <= kind < 551:
            return 3
        if 512 <= kind < 530:
            return 1
        if 0 <= kind < 512:
            return 6
        raise ValueError(f"{path}: unknown owner kind {kind}")

    def row_lane(kind):
        if 512 <= kind < 530:
            return kind - 512
        if 530 <= kind < 551:
            return 24 + kind - 530
        if kind == 1:
            return 129
        if kind == 2:
            return 130
        if kind in (3, 4):
            return 131
        if 5 <= kind <= 22:
            return 132 + kind - 5
        if 32 <= kind < 130:
            return 150 + kind - 32
        return None

    def check_admitted_owner(kind, requested, actual, size):
        family = family_of(kind)
        if family == 6:
            if kind == 0:
                if requested or actual or actual * size:
                    raise ValueError(f"{path}: unclassified owner has nonzero capacity or bytes")
            elif row_lane(kind) is None:
                raise ValueError(f"{path}: unmapped family-6 owner kind {kind}")
        if family in (1, 3, 6) and kind != 0 and row_lane(kind) is None:
            raise ValueError(f"{path}: owner kind {kind} lacks a physical row")

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
        row = row_lane(kind)
        if row is not None:
            current = row_current.setdefault(row, [0, 0])
            current[0] += capacity_delta
            current[1] += bytes_delta
            if min(current) < 0:
                raise ValueError(f"{path}: negative physical row lane {row}")
            peak = row_peak.setdefault(row, [0, 0])
            peak[0] = max(peak[0], current[0])
            peak[1] = max(peak[1], current[1])

    def check_row_size(kind, size, actual):
        row = row_lane(kind)
        if row is not None and actual:
            previous = row_sizes.setdefault(row, size)
            if previous != size:
                raise ValueError(f"{path}: physical row lane {row} combines unequal slot sizes {previous} and {size}")

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
                family = 1 if kind == 512 else 2 if kind == 571 else 3 if kind == 530 else 4 if kind == 551 else 5 if kind == 584 else 8 if kind == 577 else 6 if kind == 0 else None
                if family is None or owner_id or requested or target or (actual, size) != tuple(family_current[family]):
                    raise ValueError(f"{path}: invalid family checkpoint")
                if family in (1, 2, 3, 4, 5, 8) and family in checkpoints:
                    raise ValueError(f"{path}: duplicate family-{family} checkpoint")
                checkpoints[family] = (actual, size)
                if family == 2:
                    term_checkpoint_by_kind = {lane_kind: [*current, *lane_peak[lane_kind]]
                        for lane_kind, current in lane_current.items() if family_of(lane_kind) == 2}
                if family == 8:
                    instantiation_checkpoint_by_kind = {lane_kind: [*current, *lane_peak[lane_kind]]
                        for lane_kind, current in lane_current.items() if family_of(lane_kind) == 8}
                if family == 5:
                    normalization_checkpoint_by_kind = {lane_kind: [*current, *lane_peak[lane_kind]]
                        for lane_kind, current in lane_current.items() if family_of(lane_kind) == 5}
                if family == 6:
                    if any(owner_kind == 0 for owner_kind, *_ in owners.values()):
                        raise ValueError(f"{path}: unclassified owner at family-6 checkpoint")
                    checkpoint_by_kind = {lane_kind: [*current, *lane_peak[lane_kind]]
                        for lane_kind, current in lane_current.items() if family_of(lane_kind) in (4, 6)}
                continue
            if 1 in checkpoints and family_of(kind) == 1 and op != 5:
                raise ValueError(f"{path}: family-1 mutation after checkpoint")
            if 2 in checkpoints and family_of(kind) == 2 and op != 4:
                raise ValueError(f"{path}: family-2 mutation after checkpoint")
            if 3 in checkpoints and family_of(kind) == 3 and op != 5 and not (op == 4 and kind == 549):
                raise ValueError(f"{path}: family-3 mutation after checkpoint")
            if 4 in checkpoints and family_of(kind) == 4:
                raise ValueError(f"{path}: family-4 mutation after checkpoint")
            if 5 in checkpoints and family_of(kind) == 5:
                raise ValueError(f"{path}: family-5 mutation after checkpoint")
            if 8 in checkpoints and family_of(kind) == 8:
                raise ValueError(f"{path}: family-8 mutation after checkpoint")
            if op == 1:
                if owner_id <= last_id:
                    raise ValueError(f"{path}: owner IDs are not strictly increasing")
                last_id = owner_id
                if key in owners or requested > actual or size == 0 or target:
                    raise ValueError(f"{path}: invalid create {key}")
                check_admitted_owner(kind, requested, actual, size)
                owners[key] = (kind, requested, actual, size)
                check_row_size(kind, size, actual)
                adjust(kind, actual, actual * size)
            else:
                if key not in owners:
                    raise ValueError(f"{path}: mutation of unknown owner {key}")
                old_kind, old_requested, old_actual, old_size = owners[key]
                check_admitted_owner(old_kind, old_requested, old_actual, old_size)
                if op == 5:
                    if old_kind == 0 or actual or requested or kind != old_kind or size != old_size or target:
                        raise ValueError(f"{path}: release retains owner {key}")
                    del owners[key]
                    adjust(old_kind, -old_actual, -old_actual * old_size)
                elif op in (2, 3, 4, 7):
                    if requested > actual or size == 0:
                        raise ValueError(f"{path}: invalid owner shape {key}")
                    check_admitted_owner(kind, requested, actual, size)
                    if family_of(old_kind) in (4, 8) and (op == 4 or kind != old_kind or size != old_size):
                        raise ValueError(f"{path}: family-{family_of(old_kind)} lane cannot transfer or change slot size")
                    if op == 2 and family_of(old_kind) in (1, 2, 3, 4, 5, 8) and (kind != old_kind or size != old_size or
                                    actual != old_actual or requested == old_requested):
                        raise ValueError(f"{path}: shape changes family-1/family-3 allocation or repeats shape {key}")
                    if op == 2 and target:
                        raise ValueError(f"{path}: invalid shape target {key}")
                    if op == 3 and (kind != old_kind or size != old_size or
                                    actual <= old_actual):
                        raise ValueError(f"{path}: growth changes owner shape {key}")
                    if op == 7 and (not (family_of(old_kind) == 4 or 32 <= old_kind < 130) or kind != old_kind or
                                    size != old_size or actual >= old_actual or target):
                        raise ValueError(f"{path}: invalid capacity decrease {key}")
                    if op == 3 and family_of(kind) == 5:
                        normalization_growth[kind] = normalization_growth.get(kind, 0) + 1
                    if op == 4 and target != kind:
                        raise ValueError(f"{path}: invalid atomic transfer {key}")
                    if op == 4 and family_of(kind) == 3:
                        if 3 not in checkpoints or kind != 549:
                            raise ValueError(f"{path}: only the errors owner may transfer after family-3 checkpoint")
                        if (kind != old_kind or requested != old_requested or
                                actual != old_actual or size != old_size):
                            raise ValueError(f"{path}: family-3 transfer changes the physical owner {key}")
                        family3_transfers += 1
                    if op == 4 and family_of(kind) == 2:
                        if 2 not in checkpoints or key in family2_transfers or (kind, requested, actual, size) != (old_kind, old_requested, old_actual, old_size):
                            raise ValueError(f"{path}: family-2 finish transfer changes or repeats owner {key}")
                        family2_transfers.add(key)
                    normalization_output_transfer = (
                        op == 4 and family_of(old_kind) == 5 and family_of(kind) == 6
                        and 584 + 21 <= old_kind <= 584 + 26
                        and kind == 12 + old_kind - (584 + 21)
                        and (requested, actual, size) == (old_requested, old_actual, old_size)
                    )
                    if op == 4 and family_of(old_kind) == 5 and not normalization_output_transfer:
                        raise ValueError(f"{path}: only normalization output lanes may transfer")
                    if family_of(kind) != family_of(old_kind) and not normalization_output_transfer:
                        raise ValueError(f"{path}: cross-family owner transfer {key}")
                    adjust(old_kind, -old_actual, -old_actual * old_size)
                    owners[key] = (kind, requested, actual, size)
                    check_row_size(kind, size, actual)
                    adjust(kind, actual, actual * size)
                else:
                    raise ValueError(f"{path}: unknown event operation {op}")
    if count != expected_count or checksum != expected_checksum:
        raise ValueError(f"{path}: event count/checksum mismatch")
    if set(checkpoints) != {1, 2, 3, 4, 5, 6, 8} or any(any(family_current[family]) for family in (1, 4, 5, 6, 8)):
        raise ValueError(f"{path}: missing terminal checkpoint or unreleased owner capacity")
    if any(family_of(kind) == 4 for kind, *_ in owners.values()):
        raise ValueError(f"{path}: family-4 owner survives EOF")
    if any(family_of(kind) == 8 for kind, *_ in owners.values()):
        raise ValueError(f"{path}: family-8 owner survives EOF")
    if any(family_of(kind) == 5 for kind, *_ in owners.values()):
        raise ValueError(f"{path}: family-5 owner survives EOF")
    if tuple(family_current[2]) != checkpoints[2]:
        raise ValueError(f"{path}: family-2 retained owners changed after finish")
    family2_live_ids = {key for key, (kind, *_rest) in owners.items() if family_of(kind) == 2}
    if family2_transfers != family2_live_ids:
        raise ValueError(f"{path}: family-2 finish did not transfer every retained owner")
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
        (*checkpoints[2], family_peak[2]),
        term_checkpoint_by_kind,
        (*checkpoints[3], family_peak[3]),
        (*checkpoints[4], family_peak[4]),
        (*checkpoints[5], family_peak[5]),
        normalization_checkpoint_by_kind,
        normalization_growth,
        (*checkpoints[8], family_peak[8]),
        instantiation_checkpoint_by_kind,
        row_current,
        row_peak,
        row_sizes,
    )


def check_walker_shadow_witness(sidecar, totals_path):
    """Replay the complete witness sidecar with the matrix replay's owner rules."""
    expected = totals_path.read_text(encoding="ascii").splitlines()
    header = expected[0].split()
    if len(header) != 2:
        raise ValueError("walker shadow witness needs count and checksum")
    expected_count, expected_checksum = map(int, header)
    expected_rows = {}
    for line in expected[1:]:
        fields = line.split()
        if len(fields) != 5:
            raise ValueError("walker shadow witness row needs a key and four totals")
        key, *values = fields
        key = key if key == "combined" else int(key)
        if key in expected_rows:
            raise ValueError(f"duplicate walker shadow witness row {key}")
        expected_rows[key] = tuple(map(int, values))
    if set(expected_rows) != (set(range(12, 18)) | set(range(129, 139)) | set(range(145, 248)) | set(range(512, 612)) | {"combined"}):
        raise ValueError("walker shadow witness needs all 219 event lane rows and combined totals")
    owners = {}
    rows = {kind: [0, 0, 0, 0] for kind in (*range(12, 18), *range(129, 139), *range(145, 248), *range(512, 612))}
    combined = [0, 0, 0, 0]
    count = checksum = last_id = 0
    staged_transfers = {}
    staged_releases = set()
    term_checkpoint = None
    term_checkpoint_owners = None
    term_transfers = set()
    term_releases = set()
    live_checkpoint = None
    live_checkpoint_owners = None
    live_releases = set()
    pair_checkpoint = None
    pair_checkpoint_owners = None
    pair_releases = set()
    pair_transfer = None
    pair_shapes = set()
    pair_growths = set()
    normalization_checkpoint = None
    normalization_checkpoint_owners = None
    normalization_transfers = {}
    normalization_releases = set()
    normalization_shapes = set()
    normalization_growths = set()
    source_kinds = set()
    source_transfers = {}
    source_releases = set()
    source_classifications = set()
    source_growths = {}
    failed_source_owner = None
    failed_source_released = False

    def physical_kind(kind):
        if kind == 1:
            return 129
        if kind == 2:
            return 130
        if kind in (3, 4):
            return 131
        if 5 <= kind <= 11:
            return kind + 127
        if 18 <= kind <= 22:
            return kind + 127
        if 32 <= kind < 130:
            return kind + 118
        return kind

    def adjust(kind, old, new, size):
        kind = physical_kind(kind)
        if kind not in rows:
            return
        for totals in (rows[kind], combined):
            totals[0] = totals[0] - old + new
            totals[2] = totals[2] - old * size + new * size
            if totals[0] < 0 or totals[2] < 0:
                raise ValueError(f"negative online total for kind {kind}")
            totals[1] = max(totals[1], totals[0])
            totals[3] = max(totals[3], totals[2])

    def move_staged(source, target, capacity, size):
        # The physical allocation survives this same-ID owner move unchanged.
        for kind, delta in ((physical_kind(source), -capacity), (physical_kind(target), capacity)):
            totals = rows[kind]
            totals[0] += delta
            totals[2] += delta * size
            if totals[0] < 0 or totals[2] < 0:
                raise ValueError(f"negative staged transfer total for kind {kind}")
            totals[1] = max(totals[1], totals[0])
            totals[3] = max(totals[3], totals[2])

    with sidecar.open("rb") as stream:
        if stream.read(8) != EVENT_MAGIC:
            raise ValueError("invalid witness sidecar header")
        while block := stream.read(EVENT.size):
            if len(block) != EVENT.size:
                raise ValueError("truncated witness sidecar")
            component, owner_id, op, kind, requested, actual, size, target = EVENT.unpack(block)
            count += 1
            checksum = (checksum + sum(EVENT.unpack(block))) & ((1 << 64) - 1)
            key = (component, owner_id)
            if op == 6:
                if kind == 584:
                    if (component, owner_id, requested, target) != (0, 0, 0, 0) or normalization_checkpoint is not None:
                        raise ValueError("invalid normalization witness checkpoint shape")
                    if (actual, size) != (sum(rows[k][0] for k in range(584, 612)),
                                           sum(rows[k][2] for k in range(584, 612))):
                        raise ValueError("normalization witness checkpoint differs from live rows")
                    if any(rows[k][0] == 0 for k in (*range(584, 600), *range(601, 612))) or rows[600] != [0, 0, 0, 0]:
                        raise ValueError("normalization witness lacks a physical lane or lane 16 is owned")
                    normalization_checkpoint_owners = {key: value for key, value in owners.items()
                                                       if 584 <= value[0] < 612}
                    expected_kinds = (*range(584, 600), *range(601, 612))
                    if (len(normalization_checkpoint_owners) != 27
                            or sorted(value[0] for value in normalization_checkpoint_owners.values())
                            != list(expected_kinds)):
                        raise ValueError("normalization checkpoint needs exactly one owner per physical lane")
                    normalization_checkpoint = (actual, size)
                    continue
                if kind == 530:
                    if (component, owner_id, requested, target) != (0, 0, 0, 0) or pair_checkpoint is not None:
                        raise ValueError("invalid family-3 witness checkpoint shape")
                    if not all(rows[lane_kind][0] > 0 for lane_kind in range(530, 551)):
                        raise ValueError("family-3 witness checkpoint lacks a live lane")
                    if (actual, size) != (sum(rows[k][0] for k in range(530, 551)),
                                           sum(rows[k][2] for k in range(530, 551))):
                        raise ValueError("family-3 witness checkpoint differs from live rows")
                    pair_checkpoint = (actual, size)
                    pair_checkpoint_owners = {key for key, (owner_kind, *_rest) in owners.items()
                                              if 530 <= owner_kind < 551}
                    if len([key for key in pair_checkpoint_owners if owners[key][0] == 531]) < 2:
                        raise ValueError("family-3 witness needs overlapping child owners")
                    continue
                if kind == 512:
                    if (component, owner_id, requested, target) != (0, 0, 0, 0) or live_checkpoint is not None:
                        raise ValueError("invalid family-1 witness checkpoint shape")
                    if not all(rows[lane_kind][0] > 0 for lane_kind in range(512, 530)):
                        raise ValueError("family-1 witness checkpoint lacks a live lane")
                    if (actual, size) != (sum(rows[k][0] for k in range(512, 530)),
                                           sum(rows[k][2] for k in range(512, 530))):
                        raise ValueError("family-1 witness checkpoint differs from live rows")
                    live_checkpoint = (actual, size)
                    live_checkpoint_owners = {key for key, (owner_kind, *_rest) in owners.items()
                                              if 512 <= owner_kind < 530}
                    continue
                term_lanes_live = all(rows[lane_kind][0] > 0 for lane_kind in range(571, 577))
                if ((kind, component, owner_id, requested, target) != (571, 0, 0, 0, 0)
                        or term_checkpoint is not None
                        or not term_lanes_live
                        or (actual, size) != (
                            sum(rows[lane_kind][0] for lane_kind in range(571, 577)),
                            sum(rows[lane_kind][2] for lane_kind in range(571, 577)))):
                    raise ValueError("invalid family-2 witness checkpoint")
                term_checkpoint = (actual, size)
                term_checkpoint_owners = {key for key, (owner_kind, *_rest) in owners.items() if 571 <= owner_kind < 577}
                continue
            if requested > actual or size == 0:
                raise ValueError(f"invalid witness shape {key}")
            if op == 1:
                if 12 <= kind < 18:
                    raise ValueError(f"staged witness owner must arrive by transfer {key}")
                if pair_checkpoint is not None and 530 <= kind < 551:
                    raise ValueError("family-3 witness creation after checkpoint")
                if live_checkpoint is not None and 512 <= kind < 530:
                    raise ValueError("family-1 witness creation after checkpoint")
                if term_checkpoint is not None and 571 <= kind < 577:
                    raise ValueError("family-2 witness creation after checkpoint")
                if kind == 600:
                    raise ValueError("normalization lane 16 must remain ownerless")
                if normalization_checkpoint is not None and 584 <= kind < 612:
                    raise ValueError("normalization witness creation after checkpoint")
                if owner_id <= last_id or key in owners or target:
                    raise ValueError(f"invalid witness create {key}")
                last_id = owner_id
                owners[key] = (kind, requested, actual, size)
                adjust(kind, 0, actual, size)
                if kind in (*range(1, 12), *range(18, 23)) and actual > 0:
                    source_kinds.add(kind)
                continue
            if key not in owners:
                raise ValueError(f"unknown witness owner {key}")
            old_kind, old_requested, old_actual, old_size = owners[key]
            if op == 4 and 584 <= kind < 612:
                raise ValueError(f"transfer into normalization lane {key}")
            if 12 <= old_kind < 18 and op != 5:
                raise ValueError(f"staged witness owner changed after transfer {key}")
            if normalization_checkpoint is not None and 584 <= old_kind < 612 and op != 5:
                if not (op == 4 and key in normalization_checkpoint_owners
                        and 605 <= old_kind < 611
                        and kind == old_kind - 605 + 12
                        and key not in normalization_transfers
                        and (requested, actual, size, target) ==
                        (old_requested, old_actual, old_size, kind)):
                    raise ValueError(f"normalization witness mutation after checkpoint {key}")
            if op == 4 and (530 <= old_kind < 551 or 530 <= kind < 551):
                if (pair_checkpoint is None or old_kind != 549 or kind != 549
                        or pair_transfer is not None or
                        (requested, actual, size, target) !=
                        (old_requested, old_actual, old_size, old_kind)):
                    raise ValueError(f"invalid family-3 witness transfer {key}")
            if 530 <= old_kind < 551:
                if op == 7:
                    raise ValueError(f"family-3 witness decrease {key}")
                if pair_checkpoint is not None and op not in (4, 5):
                    raise ValueError(f"family-3 witness mutation after checkpoint {key}")
            if 512 <= old_kind < 530 and op in (4, 7):
                raise ValueError(f"family-1 witness has invalid transfer/decrease {key}")
            if live_checkpoint is not None and 512 <= old_kind < 530 and op != 5:
                raise ValueError(f"family-1 witness mutation after checkpoint {key}")
            if op == 5:
                if (kind, requested, actual, size, target) != (old_kind, 0, 0, old_size, 0):
                    raise ValueError(f"invalid witness release {key}")
                if key in staged_transfers:
                    staged_releases.add(key)
                if key in source_transfers:
                    source_releases.add(key)
                if key == failed_source_owner:
                    failed_source_released = True
                if normalization_checkpoint_owners is not None and key in normalization_checkpoint_owners:
                    normalization_releases.add(key)
                if key in term_transfers:
                    term_releases.add(key)
                if live_checkpoint is not None and key in live_checkpoint_owners:
                    live_releases.add(key)
                if pair_checkpoint is not None and key in pair_checkpoint_owners:
                    pair_releases.add(key)
                adjust(kind, old_actual, 0, size)
                del owners[key]
            elif op in (2, 3, 4, 7):
                if term_checkpoint is not None and 571 <= old_kind < 577 and op != 4:
                    raise ValueError(f"family-2 witness mutation after checkpoint {key}")
                if size != old_size and old_actual != 0:
                    raise ValueError(f"witness slot size changed {key}")
                if op == 2 and (kind != old_kind and old_kind != 0
                                and (old_kind, kind) != (4, 3)
                                or actual != old_actual or target):
                    raise ValueError(f"invalid witness shape event {key}")
                if op == 3 and (kind != old_kind or actual <= old_actual or target):
                    raise ValueError(f"invalid witness growth {key}")
                if op == 7 and (kind != old_kind or actual >= old_actual or target):
                    raise ValueError(f"invalid witness decrease {key}")
                if op == 4 and (target != kind or actual != old_actual):
                    raise ValueError(f"invalid witness transfer {key}")
                if op == 4 and 571 <= old_kind < 577:
                    if term_checkpoint is None or key in term_transfers or (kind, requested, actual, size) != (old_kind, old_requested, old_actual, old_size):
                        raise ValueError(f"invalid family-2 witness transfer {key}")
                    term_transfers.add(key)
                if op == 4 and 530 <= old_kind < 551:
                    pair_transfer = key
                if op == 2 and 530 <= old_kind < 551 and requested != old_requested:
                    pair_shapes.add(key)
                if op == 3 and 530 <= old_kind < 551:
                    pair_growths.add(key)
                if op == 2 and 584 <= old_kind < 612 and requested != old_requested:
                    normalization_shapes.add(old_kind)
                if op == 3 and 584 <= old_kind < 612:
                    normalization_growths.add(old_kind)
                if op == 3 and kind == 1:
                    source_growths[key] = source_growths.get(key, 0) + 1
                    if source_growths[key] >= 2 and failed_source_owner is None:
                        failed_source_owner = key
                if op == 2 and (old_kind, kind) == (4, 3) and actual > 0:
                    source_classifications.add(key)
                if op == 4 and 32 <= old_kind < 130 and kind in (2, 9, 10):
                    if key in source_transfers or (requested, actual, size) != (old_requested, old_actual, old_size):
                        raise ValueError(f"invalid source witness transfer {key}")
                    source_transfers[key] = kind
                if kind in (*range(1, 12), *range(18, 23)) and actual > 0:
                    source_kinds.add(kind)
                if op == 4 and 584 <= old_kind < 612:
                    if (normalization_checkpoint is None or old_kind not in range(605, 611)
                            or kind != old_kind - 605 + 12
                            or (requested, actual, size) != (old_requested, old_actual, old_size)
                            or old_kind in normalization_transfers.values()):
                        raise ValueError(f"invalid normalization output transfer {key}")
                    normalization_transfers[key] = old_kind
                if op == 4 and (32 <= old_kind < 130 or 605 <= old_kind < 611) and 12 <= kind < 18:
                    if (kind in staged_transfers.values() or
                            (605 <= old_kind < 611 and kind != old_kind - 605 + 12) or
                            requested != old_requested):
                        raise ValueError(f"duplicate staged witness transfer for kind {kind}")
                    staged_transfers[key] = kind
                if 12 <= kind < 18:
                    if op != 4 or not (32 <= old_kind < 130 or 605 <= old_kind < 611):
                        raise ValueError(f"invalid staged witness source {key}")
                    move_staged(old_kind, kind, old_actual, size)
                elif op == 4 and physical_kind(old_kind) == physical_kind(kind):
                    pass
                else:
                    adjust(old_kind, old_actual, 0, size)
                owners[key] = (kind, requested, actual, size)
                if not (12 <= kind < 18) and not (op == 4 and physical_kind(old_kind) == physical_kind(kind)):
                    adjust(kind, 0, actual, size)
            else:
                raise ValueError(f"unexpected witness op {op}")
    if (count, checksum) != (expected_count, expected_checksum):
        raise ValueError("witness event count/checksum mismatch")
    if set(staged_transfers.values()) != set(range(12, 18)) or staged_releases != set(staged_transfers):
        raise ValueError("witness needs six same-ID FlatDraft transfers and adopted-owner releases")
    if (normalization_checkpoint is None or set(normalization_transfers.values()) != set(range(605, 611))
            or normalization_releases != set(normalization_checkpoint_owners)
            or not normalization_shapes or not normalization_growths):
        raise ValueError("witness needs normalization checkpoint, shapes, growths, and six exact output releases")
    if term_checkpoint is None or not term_transfers or term_transfers != term_checkpoint_owners or term_transfers != term_releases:
        raise ValueError("witness needs all family-2 same-ID transfers and releases")
    if live_checkpoint is None or not live_checkpoint_owners or live_releases != live_checkpoint_owners:
        raise ValueError("witness needs family-1 checkpoint and release-only owner suffix")
    if (pair_checkpoint is None or pair_transfer is None or pair_transfer not in pair_checkpoint_owners
            or pair_transfer not in pair_releases or pair_releases != pair_checkpoint_owners
            or not pair_shapes or not pair_growths):
        raise ValueError("witness needs family-3 checkpoint, kind-549 transfer, and exact releases")
    if any(rows[kind][1] == 0 or rows[kind][0] != 0 for kind in range(530, 551)):
        raise ValueError("witness needs all 21 released family-3 physical lanes")
    if any(rows[kind][1] == 0 or rows[kind][0] != 0 for kind in range(512, 530)):
        raise ValueError("witness needs all 18 released family-1 physical lanes")
    if any(rows[kind][1] == 0 or rows[kind][0] != 0 for kind in (*range(584, 600), *range(601, 612))):
        raise ValueError("witness needs all 27 released normalization lanes")
    if rows[600] != [0, 0, 0, 0]:
        raise ValueError("normalization lane 16 must remain zero")
    if any(rows[kind][0] != 0 or rows[kind][2] != 0 or
           rows[kind][1] == 0 or rows[kind][3] == 0 for kind in range(12, 18)):
        raise ValueError("witness needs six released staged lanes with nonzero peaks")
    if any(rows[kind][1] == 0 for kind in range(571, 577)):
        raise ValueError("witness needs all six family-2 physical lanes")
    if owners or tuple(combined) != expected_rows["combined"]:
        raise ValueError("witness retained owner or combined shadow mismatch")
    for kind, totals in rows.items():
        if tuple(totals) != expected_rows[kind]:
            raise ValueError(f"lane {kind} shadow mismatch: {totals} != {expected_rows[kind]}")
    if any(rows[k][0] or rows[k][2] or rows[k][1] == 0 or rows[k][3] == 0 for k in (*range(129, 139), *range(145, 150))):
        raise ValueError("witness needs all 15 released source rows with nonzero peaks")
    if (source_kinds != set((*range(1, 12), *range(18, 23)))
            or not source_classifications
            or set(source_transfers.values()) != {2, 9, 10}
            or source_releases != set(source_transfers)
            or failed_source_owner is None or not failed_source_released):
        raise ValueError("witness needs source kinds, classification, same-ID transfers, failed growth and releases")
    print(f"F5c online owner shadow: {count} full sidecar events, 219 exact lane rows and joint total")


def check_joint_session_witness(sidecar, totals_path):
    """Replay event current plus independently sampled session decompositions."""
    expected = tuple(map(int, totals_path.read_text(encoding="ascii").split()))
    if len(expected) != 7:
        raise ValueError("joint witness needs count, checksum, current, peak, samples, calls, adjustments")
    owners = {}
    owner_current = 0
    owner_peak = 0
    closed_peak = route_peak = other_peak = 0
    other = closed = route = current = peak = 0
    samples = calls = count = checksum = 0
    baseline_seen = False
    route_values = []
    other_values = []
    finalizer_overlap = 0
    indexed_live = source_live = 0
    previous_boundary = None
    pending_member = False
    member_rebase = False
    route_growth = route_decrease = False
    previous_route = None

    def physical(kind):
        if kind == 1:
            return 129
        if kind == 2:
            return 130
        if kind in (3, 4):
            return 131
        if 5 <= kind <= 11 or 18 <= kind <= 22:
            return kind + 127
        if 32 <= kind < 130:
            return kind + 118
        return kind

    def tracked(kind):
        kind = physical(kind)
        return (12 <= kind < 18 or 129 <= kind < 139
                or 145 <= kind < 248 or 512 <= kind < 612)

    def indexed(kind):
        return 145 <= physical(kind) < 150

    def source(kind):
        kind = physical(kind)
        return 129 <= kind < 139 or 12 <= kind < 18

    with sidecar.open("rb") as stream:
        if stream.read(8) != EVENT_MAGIC:
            raise ValueError("invalid joint witness sidecar header")
        while block := stream.read(EVENT.size):
            if len(block) != EVENT.size:
                raise ValueError("truncated joint witness sidecar")
            words = EVENT.unpack(block)
            boundary, owner_id, op, kind, requested, actual, size, target = words
            count += 1
            checksum = (checksum + sum(words)) & ((1 << 64) - 1)
            if op == 8:
                if owner_id or kind or boundary > 13 or actual != owner_current:
                    raise ValueError(f"invalid joint baseline ordering or owner subtotal: event {count}, boundary {boundary}, online {actual}, replay {owner_current}")
                if not baseline_seen and (boundary != 0 or owner_current != 0):
                    raise ValueError("joint witness needs the initial zero-owner baseline")
                if pending_member and boundary != 7:
                    raise ValueError("finalizer must be followed by DraftMember sample")
                decomposed = actual + size + target
                if decomposed > requested:
                    raise ValueError("joint baseline exceeds independent session sample")
                previous_other = other
                other, closed, route = requested - decomposed, size, target
                if boundary == 7 and baseline_seen:
                    member_rebase |= other != previous_other
                if pending_member:
                    pending_member = False
                if boundary == 9:
                    if previous_route is not None:
                        route_growth |= route > previous_route
                        route_decrease |= route < previous_route
                    previous_route = route
                closed_peak = max(closed_peak, closed)
                route_peak = max(route_peak, route)
                other_peak = max(other_peak, other)
                if other + owner_current + closed + route != requested:
                    raise ValueError("joint baseline decomposition mismatch")
                current = requested
                peak = max(peak, current)
                samples += 1
                baseline_seen = True
                previous_boundary = boundary
                route_values.append(route)
                other_values.append(other)
                continue
            if op == 9:
                if (not baseline_seen or pending_member or previous_boundary != 13
                        or boundary or owner_id or kind or target or requested != closed):
                    raise ValueError("invalid finalizer continuity")
                if size < requested or size < actual:
                    raise ValueError("finalizer call peak below retained baseline")
                if indexed_live and source_live:
                    finalizer_overlap += 1
                candidate = other + owner_current + route + size
                peak = max(peak, candidate)
                closed = actual
                closed_peak = max(closed_peak, size)
                current = other + owner_current + route + closed
                peak = max(peak, current)
                calls += 1
                pending_member = True
                continue
            key = (boundary, owner_id)
            if op == 6:
                continue
            if op == 1:
                if key in owners or actual or target:
                    raise ValueError("invalid joint owner create")
                owners[key] = (kind, 0, size)
            elif op == 5:
                old_kind, old_capacity, old_size = owners.pop(key)
                if (kind, requested, actual, size, target) != (old_kind, 0, 0, old_size, 0):
                    raise ValueError("invalid joint owner release")
                if tracked(old_kind):
                    owner_current -= old_capacity * old_size
                if old_capacity:
                    indexed_live -= indexed(old_kind)
                    source_live -= source(old_kind)
            elif op in (2, 3, 4, 7):
                old_kind, old_capacity, old_size = owners[key]
                if old_capacity and size != old_size:
                    raise ValueError("joint owner size changed")
                if op == 4 and (target != kind or actual != old_capacity):
                    raise ValueError("invalid joint owner transfer")
                if op == 3 and actual <= old_capacity:
                    raise ValueError("invalid joint owner growth")
                if op == 7 and actual >= old_capacity:
                    raise ValueError("invalid joint owner decrease")
                if op == 2 and kind != old_kind and old_kind != 0 and (old_kind, kind) != (4, 3):
                    raise ValueError("invalid joint owner classification")
                if tracked(old_kind):
                    owner_current -= old_capacity * old_size
                if tracked(kind):
                    owner_current += actual * size
                if old_capacity:
                    indexed_live -= indexed(old_kind)
                    source_live -= source(old_kind)
                if actual:
                    indexed_live += indexed(kind)
                    source_live += source(kind)
                owners[key] = (kind, actual, size)
            else:
                raise ValueError(f"unexpected joint witness op {op}")
            if owner_current < 0:
                raise ValueError("negative joint owner subtotal")
            owner_peak = max(owner_peak, owner_current)
            if baseline_seen:
                current = other + owner_current + closed + route
                peak = max(peak, current)
    if (count, checksum, current, peak, samples, calls) != expected[:6] or expected[6] <= 0:
        raise ValueError("joint witness replay differs from online totals")
    if (not baseline_seen or pending_member or calls < 2 or finalizer_overlap < 2
            or not route_growth or not route_decrease or not member_rebase
            or len(set(other_values)) < 2):
        raise ValueError(f"joint witness lacks finalizer overlap or route/member rebases: calls={calls}, overlap={finalizer_overlap}, route_growth={route_growth}, route_decrease={route_decrease}, member_rebase={member_rebase}")
    if owner_peak + closed_peak + route_peak + other_peak <= peak:
        raise ValueError("joint witness lacks a non-co-temporal historical-peak counterexample")
    print(f"F5c joint session: E={expected[6]} owner adjustments, S={samples} baselines, F={calls} finalizers, 64*(S+F)={64 * (samples + calls)} boundary bytes")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--walker-shadow-witness", type=Path,
                        help="complete small sidecar emitted by f5c_walker_online_shadow_witness")
    parser.add_argument("--walker-shadow-totals", type=Path,
                        help="online totals emitted by f5c_walker_online_shadow_witness")
    parser.add_argument("--joint-session-witness", type=Path,
                        help="live-session owner and boundary sidecar")
    parser.add_argument("--joint-session-totals", type=Path,
                        help="online joint totals emitted by the live-session witness")
    parser.add_argument("--diagnostic-cycle-32-4000", action="store_true",
                        help="replay only the isolated guarded_cycle(D=32,K=4000) row")
    parser.add_argument("logs", type=Path, nargs="*", help="captured matrix process logs")
    args = parser.parse_args()
    if args.joint_session_witness is not None or args.joint_session_totals is not None:
        if args.joint_session_witness is None or args.joint_session_totals is None or args.logs:
            parser.error("joint session witness requires both paths and no matrix logs")
        check_joint_session_witness(args.joint_session_witness, args.joint_session_totals)
        return
    if args.walker_shadow_witness is not None or args.walker_shadow_totals is not None:
        if args.walker_shadow_witness is None or args.walker_shadow_totals is None or args.logs:
            parser.error("walker shadow witness requires both paths and no matrix logs")
        check_walker_shadow_witness(args.walker_shadow_witness, args.walker_shadow_totals)
        return
    if not args.logs:
        parser.error("matrix replay requires captured process logs")
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
        key, size, ends, totals, aggregate, lanes, family1_event, family2_event, family3_event, family4_event, family5_event, family5_growths, family8_event, family6_event = parse_line(record, path, args.diagnostic_cycle_32_4000)
        if (key, size) in rows:
            raise ValueError(f"{path}: duplicate matrix row {key} size {size}")
        folded, by_kind, folded_family1, folded_family2, term_by_kind, folded_family3, folded_family4, folded_family5, normalization_by_kind, normalization_growth, folded_family8, instantiation_by_kind, row_current, row_peak, row_sizes = replay_f6_events(sidecar, family6_event[4], family6_event[5])
        if folded != family6_event[:3]:
            raise ValueError(f"{path}: family-6 event fold differs from matrix row")
        if folded_family1 != family1_event:
            raise ValueError(f"{path}: family-1 event fold differs from matrix row")
        if folded_family2 != family2_event:
            raise ValueError(f"{path}: family-2 event fold differs from matrix row")
        if folded_family3 != family3_event:
            raise ValueError(f"{path}: family-3 event fold differs from matrix row")
        if folded_family4 != family4_event:
            raise ValueError(f"{path}: family-4 event fold differs from matrix row")
        if folded_family5 != family5_event:
            raise ValueError(f"{path}: family-5 event fold differs from matrix row")
        if folded_family8 != family8_event:
            raise ValueError(f"{path}: family-8 event fold differs from matrix row")
        canonical_lanes = list(lanes)
        # Lane snapshots witness sampled state. The offline event replay supplies
        # the authoritative same-time current and actual physical row peak.
        for lane in (*range(0, 18), *range(24, 45), *range(129, 248)):
            values = lanes[lane]
            current = row_current.get(lane, [0, 0])
            peak = row_peak.get(lane, [0, 0])
            size = row_sizes.get(lane, values[5])
            if (current[0] != values[0] or current[1] != values[2]
                    or current[1] != current[0] * size
                    or (values[5] not in (0, size))
                    or peak[0] < values[1] or peak[1] < values[4]
                    or peak[1] != peak[0] * size):
                raise ValueError(f"{path}: physical row lane {lane} owner shape differs from matrix row")
            canonical_lanes[lane] = (current[0], peak[0], current[1], peak[1], peak[1], size)
        for lane, values in enumerate(lanes[18:24]):
            kind_values = term_by_kind.get(571 + lane, [0, 0, 0, 0])
            if (kind_values[0] != values[0] or kind_values[1] != values[2]
                    or kind_values[2] < values[1] or kind_values[3] < values[4]):
                raise ValueError(f"{path}: family-2 lane {lane} owner shape differs from matrix row")
        for lane, values in enumerate(lanes[45:65]):
            kind_values = by_kind.get(551 + lane, [0, 0, 0, 0])
            if (kind_values[0] != values[0] or kind_values[1] != values[2]
                    or kind_values[2] < values[1] or kind_values[3] < values[4]):
                raise ValueError(f"{path}: family-4 lane {lane} owner shape differs from matrix row")
        for lane, values in enumerate(lanes[101:129]):
            kind_values = normalization_by_kind.get(584 + lane, [0, 0, 0, 0])
            if (kind_values[0] != values[0] or kind_values[1] != values[2]
                    or kind_values[2] < values[1] or kind_values[3] < values[4]
                    or normalization_growth.get(584 + lane, 0) != family5_growths[lane]):
                raise ValueError(f"{path}: family-5 lane {lane} owner shape differs from matrix row")
        for lane, values in enumerate(lanes[248:255]):
            kind_values = instantiation_by_kind.get(577 + lane, [0, 0, 0, 0])
            if (kind_values[0] != values[0] or kind_values[1] != values[2]
                    or kind_values[2] != values[1] or kind_values[3] != values[4]):
                raise ValueError(f"{path}: family-8 lane {lane} owner shape differs from matrix row")
        owner_aggregates[key, size] = by_kind
        rows[key, size] = ends, totals, aggregate, tuple(canonical_lanes)
    expected = ({(("GuardedCycle", "D", "4000"), 32)} if args.diagnostic_cycle_32_4000
                else {(key, size) for key in SERIES for size in SIZES})
    if set(rows) != expected:
        raise ValueError(f"missing={sorted(expected - set(rows))}; unexpected={sorted(set(rows) - expected)}")
    if args.diagnostic_cycle_32_4000:
        print("F5c guarded cycle diagnostic: one D=32 K=4000 row replayed; 158 event-backed physical rows reconciled")
        return
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
    print("F5c resource matrix: 36 unique rows, 12 series, 158 event-backed physical rows per run reconciled, all adjacent physical ratios <2.5")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
