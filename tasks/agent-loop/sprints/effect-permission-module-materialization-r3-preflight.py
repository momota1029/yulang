import hashlib
import json
import re
import sys
from pathlib import Path

manifest_path = Path(sys.argv[1])
manifest = json.loads(manifest_path.read_text())
if not isinstance(manifest, dict) or len(manifest) != 21:
    print('MANIFEST_INVALID: expected exactly 21 unique paths')
    sys.exit(2)
malformed = [name for name, expected in manifest.items()
             if not isinstance(name, str) or not isinstance(expected, str)
             or not re.fullmatch(r'[0-9a-f]{64}', expected)]
if malformed:
    for name in malformed:
        print(f'{name!r} MALFORMED_DIGEST')
    sys.exit(2)
missing = [name for name in manifest if not Path(name).is_file()]
if missing:
    for name in missing:
        print(f'{name} MISSING')
    sys.exit(2)
matches = True
for name, expected in manifest.items():
    actual = hashlib.sha256(Path(name).read_bytes()).hexdigest()
    ok = actual == expected
    print(f'{name} {actual} {"MATCH" if ok else "MISMATCH"}')
    matches &= ok
print('PREFLIGHT_21_ENTRIES_ALL_MATCH' if matches else 'PREFLIGHT_FAIL')
sys.exit(0 if matches else 1)
