import subprocess
from pathlib import Path
base='00c63b6de8ddbc76eced4b135327013e370fcf14'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',base],text=True).splitlines()
for p in paths:
    if p=='notes/heartbeat/dots-main.md': continue
    old=subprocess.check_output(['git','show',base+':'+p])
    now=Path(p).read_bytes()
    if p in ['lean/Yulang.lean','notes/design/INDEX.md']:
        assert now.startswith(old),p
    else:
        assert now==old,p
print('PRESERVATION-PASS',len(paths),'old paths; root/design index append-only, heartbeat replaced')
