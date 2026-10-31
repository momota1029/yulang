import hashlib
import json
import sys
from pathlib import Path

PAGE_DIR=Path('tasks/agent-loop/sprints/module-supplier-native-slices-r2-pages')
MANIFEST=PAGE_DIR/'manifest.json'

def fail(message): raise SystemExit(message)

if len(sys.argv)!=2: fail('usage: pagecat.py page-NNN.txt')
name=Path(sys.argv[1]).name
if name!=sys.argv[1] or '/' in name or '\\' in name: fail('page argument must be a basename')
manifest=json.loads(MANIFEST.read_text())
found=[p for p in manifest['pages'] if p['name']==name]
if len(found)!=1: fail('page absent or ambiguous in manifest')
p=found[0]
path=PAGE_DIR/name
if path.is_symlink() or not path.is_file(): fail('page is not a regular package file')
raw=path.read_bytes()
if len(raw)!=p['emitted_bytes'] or len(raw)>manifest['max_emitted_page_bytes_including_header']: fail('page byte limit mismatch')
if hashlib.sha256(raw).hexdigest()!=p['page_sha256']: fail('page hash mismatch')
header,sep,body=raw.partition(b'\n')
expected=(f"# source={p['owner']} sha256={p['owner_sha256']} bytes=[{p['start_byte']},{p['end_byte']}) lines={p['start_line']}-{p['end_line']} kind={p['kind']} name={p['unit']}").encode()
if not sep or header!=expected or len(body)!=p['body_bytes']: fail('page header/body mismatch')
sys.stdout.buffer.write(raw)
