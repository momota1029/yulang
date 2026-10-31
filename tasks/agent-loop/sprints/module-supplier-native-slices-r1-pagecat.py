import hashlib
import json
import sys
from pathlib import Path

manifest_path = Path('tasks/agent-loop/sprints/module-supplier-native-slices-r1-pages/manifest.json')
manifest = json.loads(manifest_path.read_text())
page_name = Path(sys.argv[1]).name
matches = [page for page in manifest['pages'] if page['file'] == page_name]
if len(matches) != 1:
    raise SystemExit('page absent or ambiguous in frozen manifest')
page = matches[0]
raw = (manifest_path.parent / page_name).read_bytes()
if len(raw) != page['emitted_bytes'] or len(raw) > manifest['max_emitted_page_bytes_including_header']:
    raise SystemExit('page byte limit mismatch')
if hashlib.sha256(raw).hexdigest() != page['page_sha256']:
    raise SystemExit('page hash mismatch')
header, sep, body = raw.partition(b'\n')
expected = f"# source={page['owner']} sha256={page['owner_sha256']} bytes=[{page['start_byte']},{page['end_byte']}) lines={page['start_line']}-{page['end_line']} unit={page['unit']}".encode()
if not sep or header != expected or len(body) != page['body_bytes']:
    raise SystemExit('page header/body mismatch')
sys.stdout.buffer.write(raw)
