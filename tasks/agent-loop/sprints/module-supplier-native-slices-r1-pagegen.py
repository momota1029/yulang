import hashlib
import json
from pathlib import Path

ROOT = Path('.')
OUT = Path('tasks/agent-loop/sprints/module-supplier-native-slices-r1-pages')
PINS = {
    'crates/yu-solver/src/candidate_source.rs': '96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a',
    'crates/yu-solver/src/lib.rs': 'ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07',
    'crates/yu-solver/src/candidate_scheme.rs': '31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707',
    'crates/yu-solver/src/shadow_apply.rs': 'c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff',
}
RANGES = {
    'crates/yu-solver/src/candidate_source.rs': [(1762, 1808, 'Name-resolution arm'), (2457, 2511, 'execute_candidate_action'), (377, 403, 'Action declaration')],
    'crates/yu-solver/src/lib.rs': [(1054, 1108, 'definition registration'), (1400, 1478, 'pending-use resolution'), (19466, 19474, 'validated_route_use'), (18207, 18236, 'route_internal and route_internal_inner'), (19179, 19187, 'candidate-graph dispatch')],
    'crates/yu-solver/src/candidate_scheme.rs': [(4184, 4191, 'route_candidate_open_use'), (4193, 4220, 'route_candidate_graph'), (4717, 4799, 'instantiate_candidate_graph')],
    'crates/yu-solver/src/shadow_apply.rs': [(2029, 2055, 'CandidateInference::export'), (3038, 3102, 'observer CandidateDefinitionUseRef'), (3233, 3253, 'observer definition_use')],
}
MAX_PAGE_BYTES = 4096
MAX_BODY_BYTES = 100 * 1024
CONTENT_BUDGET = 3600

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def write_page(owner, owner_sha, unit, start_line, end_line, body, page_num, out):
    # The manifest carries the exact source offsets; each page includes a concise authenticated header.
    raw_source = (ROOT / owner).read_bytes()
    offsets = line_offsets(raw_source)
    start_byte = offsets[start_line - 1]
    end_byte = offsets[end_line]
    if raw_source[start_byte:end_byte] != body:
        raise SystemExit(f'offset reconstruction failed for {owner}:{start_line}-{end_line}')
    header = (f"# source={owner} sha256={owner_sha} bytes=[{start_byte},{end_byte}) lines={start_line}-{end_line} unit={unit}\n").encode()
    page = header + body
    if len(page) > MAX_PAGE_BYTES:
        raise SystemExit(f'page cap exceeded: {owner}:{start_line}-{end_line} {len(page)} bytes')
    name = f"page-{len(entries)+1:03d}.txt"
    (out / name).write_bytes(page)
    return {'file': name, 'owner': owner, 'owner_sha256': owner_sha, 'unit': unit, 'page_in_unit': page_num, 'start_byte': start_byte, 'end_byte': end_byte, 'start_line': start_line, 'end_line': end_line, 'body_bytes': len(body), 'emitted_bytes': len(page), 'page_sha256': sha(page), 'continuation': 'next page continues the same unit' if end_line < max(x[1] for x in RANGES[owner] if x[2] == unit) else 'unit complete'}

def line_offsets(raw):
    result = [0]
    for i, b in enumerate(raw):
        if b == 10:
            result.append(i + 1)
    if result[-1] != len(raw):
        result.append(len(raw))
    return result

def parse_page(page):
    _, sep, body = page.partition(b'\n')
    if not sep:
        raise ValueError('page header missing newline')
    return page[:len(page) - len(body)], body


OUT.mkdir(parents=True, exist_ok=True)
# Remove no old artifacts: this destination is required to be new.
if any(OUT.iterdir()):
    raise SystemExit(f'page destination is not empty: {OUT}')
entries = []
body_total = 0
for owner, expected in PINS.items():
    raw = (ROOT / owner).read_bytes()
    actual = sha(raw)
    if actual != expected:
        raise SystemExit(f'owner hash mismatch: {owner} {actual} != {expected}')
    lines = raw.splitlines(keepends=True)
    for start, end, unit in RANGES[owner]:
        if start < 1 or end > len(lines) or start > end:
            raise SystemExit(f'invalid line range {owner}:{start}-{end}')
        segment = b''.join(lines[start - 1:end])
        body_total += len(segment)
        chunk, chunk_line_start, page_num = bytearray(), start, 0
        pending_line = chunk_line_start
        for line_no in range(start, end + 1):
            line = lines[line_no - 1]
            if len(line) > CONTENT_BUDGET:
                raise SystemExit(f'single source line exceeds content budget {owner}:{line_no}')
            if chunk and len(chunk) + len(line) > CONTENT_BUDGET:
                page_num += 1
                entries.append(write_page(owner, expected, unit, chunk_line_start, line_no - 1, bytes(chunk), page_num, OUT))
                chunk = bytearray()
                chunk_line_start = line_no
            chunk.extend(line)
        if chunk:
            page_num += 1
            entries.append(write_page(owner, expected, unit, chunk_line_start, end, bytes(chunk), page_num, OUT))
if body_total > MAX_BODY_BYTES:
    raise SystemExit(f'body cap exceeded: {body_total}')
manifest = {
    'protocol': 'MSNS-r1 authenticated source pages v1',
    'contract': 'tasks/agent-loop/sprints/module-supplier-native-slices-20261028-r1.md',
    'contract_sha256': '6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435',
    'max_emitted_page_bytes_including_header': MAX_PAGE_BYTES,
    'max_unique_body_bytes': MAX_BODY_BYTES,
    'body_bytes_included_once': body_total,
    'owners': {path: {'sha256': digest} for path, digest in PINS.items()},
    'units': [{'owner': owner, 'start_line': start, 'end_line': end, 'name': name} for owner, ranges in RANGES.items() for start, end, name in ranges],
    'pages': entries,
}
manifest_path = OUT / 'manifest.json'
manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
# Independently verify page file hashes, limits, and exact concatenation of each selected unit.
for owner, ranges in RANGES.items():
    for start, end, unit in ranges:
        pages = [e for e in entries if e['owner'] == owner and e['unit'] == unit]
        pages.sort(key=lambda e: e['page_in_unit'])
        assert pages and pages[0]['start_line'] == start and pages[-1]['end_line'] == end
        assert all(pages[i]['end_line'] + 1 == pages[i + 1]['start_line'] for i in range(len(pages) - 1))
        joined = b''.join(parse_page((OUT / e['file']).read_bytes())[1] for e in pages)
        source = (ROOT / owner).read_bytes().splitlines(keepends=True)
        expected_bytes = b''.join(source[start - 1:end])
        assert joined == expected_bytes, (owner, unit, 'reconstruction mismatch')
print(f'PAGES={len(entries)} BODY_BYTES={body_total} MANIFEST={manifest_path} MANIFEST_SHA256={sha(manifest_path.read_bytes())}')
for e in entries:
    print(f"{e['file']} {e['owner']} [{e['start_byte']},{e['end_byte']}) lines {e['start_line']}-{e['end_line']} body={e['body_bytes']} emitted={e['emitted_bytes']} sha256={e['page_sha256']}")
