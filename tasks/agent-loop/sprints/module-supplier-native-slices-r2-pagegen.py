import hashlib
import json
import os
from pathlib import Path

ROOT = Path('.')
OUT = Path('tasks/agent-loop/sprints/module-supplier-native-slices-r2-pages')
STAGE = OUT.with_name('.' + OUT.name + '.stage')
MAX_PAGE = 4096
MAX_BODY = 100 * 1024
BODY_BUDGET = 3600
CONTRACT = 'tasks/agent-loop/sprints/module-supplier-native-slices-20261028-r1.md'
CONTRACT_SHA = '6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435'
PINS = {
    'crates/yu-solver/src/candidate_source.rs': '96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a',
    'crates/yu-solver/src/lib.rs': 'ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07',
    'crates/yu-solver/src/candidate_scheme.rs': '31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707',
    'crates/yu-solver/src/shadow_apply.rs': 'c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff',
}
# kind=unit is complete within the admitted owner; context fragments must not be used as whole functions.
RANGES = [
    {'owner':'crates/yu-solver/src/candidate_source.rs','start':1762,'end':1808,'name':'Name-resolution arm plus surrounding context','kind':'complete_arm_with_context','unit_start':1766,'unit_end':1807},
    {'owner':'crates/yu-solver/src/candidate_source.rs','start':2457,'end':2509,'name':'execute_candidate_action','kind':'unit','unit_start':2457,'unit_end':2509},
    {'owner':'crates/yu-solver/src/candidate_source.rs','start':377,'end':403,'name':'Action declaration','kind':'unit','unit_start':377,'unit_end':403},
    {'owner':'crates/yu-solver/src/lib.rs','start':1054,'end':1108,'name':'definition registration context','kind':'context_fragment'},
    {'owner':'crates/yu-solver/src/lib.rs','start':1400,'end':1478,'name':'pending-use resolution context','kind':'context_fragment'},
    {'owner':'crates/yu-solver/src/lib.rs','start':19466,'end':19474,'name':'validated_route_use','kind':'unit','unit_start':19466,'unit_end':19474},
    {'owner':'crates/yu-solver/src/lib.rs','start':18207,'end':18236,'name':'route_internal and route_internal_inner','kind':'unit','unit_start':18207,'unit_end':18236},
    {'owner':'crates/yu-solver/src/lib.rs','start':19179,'end':19187,'name':'candidate-graph dispatch context','kind':'context_fragment'},
    {'owner':'crates/yu-solver/src/candidate_scheme.rs','start':4184,'end':4191,'name':'route_candidate_open_use','kind':'unit','unit_start':4184,'unit_end':4191},
    {'owner':'crates/yu-solver/src/candidate_scheme.rs','start':4193,'end':4220,'name':'route_candidate_graph','kind':'unit','unit_start':4193,'unit_end':4220},
    {'owner':'crates/yu-solver/src/candidate_scheme.rs','start':4717,'end':4800,'name':'instantiate_candidate_graph','kind':'unit','unit_start':4717,'unit_end':4800},
    {'owner':'crates/yu-solver/src/shadow_apply.rs','start':2029,'end':2054,'name':'CandidateInference::export','kind':'unit','unit_start':2029,'unit_end':2054},
    {'owner':'crates/yu-solver/src/shadow_apply.rs','start':3038,'end':3091,'name':'CandidateDefinitionUseRef and implementation','kind':'unit','unit_start':3038,'unit_end':3091},
    {'owner':'crates/yu-solver/src/shadow_apply.rs','start':3230,'end':3253,'name':'definition_use','kind':'unit','unit_start':3230,'unit_end':3253},
]

def sha(b): return hashlib.sha256(b).hexdigest()
def line_offsets(raw):
    starts=[0]
    for i,b in enumerate(raw):
        if b==10: starts.append(i+1)
    if starts[-1] != len(raw): starts.append(len(raw))
    return starts

def main():
    if OUT.exists() or STAGE.exists(): raise SystemExit('destination/staging exists; preserve it and choose a fresh version')
    owners={}
    for path,expected in PINS.items():
        raw=(ROOT/path).read_bytes()
        if sha(raw)!=expected: raise SystemExit(f'owner pin mismatch before staging: {path}')
        owners[path]=(raw,raw.splitlines(keepends=True),line_offsets(raw))
    # Preflight every range, output header, page size and aggregate cap before creating staging.
    prepared=[]; total=0; seq=0; bounds={owner:[] for owner in PINS}
    for spec in RANGES:
        owner=spec['owner']; raw,lines,offsets=owners[owner]
        start,end=spec['start'],spec['end']
        if start<1 or end>len(lines) or start>end: raise SystemExit(f'invalid range: {owner}:{start}-{end}')
        if spec['kind']=='unit':
            if spec.get('unit_start')!=start or spec.get('unit_end')!=end: raise SystemExit(f'unit boundary metadata mismatch: {spec["name"]}')
        elif spec['kind']=='complete_arm_with_context':
            if not start<=spec.get('unit_start',0)<=spec.get('unit_end',0)<=end: raise SystemExit(f'arm boundary metadata mismatch: {spec["name"]}')
        seg=b''.join(lines[start-1:end]); total+=len(seg)
        bounds[owner].append((offsets[start-1],offsets[end],spec['name']))
        chunk=bytearray(); chunk_start=start
        for n in range(start,end+1):
            line=lines[n-1]
            if len(line)>BODY_BUDGET: raise SystemExit(f'line too large: {owner}:{n}')
            if chunk and len(chunk)+len(line)>BODY_BUDGET:
                seq+=1; prepared.append(make_page(seq,spec,chunk_start,n-1,bytes(chunk),offsets)); chunk=bytearray(); chunk_start=n
            chunk.extend(line)
        if chunk:
            seq+=1; prepared.append(make_page(seq,spec,chunk_start,end,bytes(chunk),offsets))
    for owner, intervals in bounds.items():
        intervals.sort()
        for left,right in zip(intervals,intervals[1:]):
            if left[1]>right[0]: raise SystemExit(f'overlapping source ranges before staging: {owner} {left[2]} / {right[2]}')
    if total>MAX_BODY: raise SystemExit(f'body cap exceeded before staging: {total}')
    for item in prepared:
        if len(item['bytes'])>MAX_PAGE: raise SystemExit(f'page cap exceeded before staging: {item["name"]}')
    manifest={
        'protocol':'MSNS-r2 authenticated source pages; atomic publication',
        'contract':CONTRACT,'contract_sha256':CONTRACT_SHA,
        'max_emitted_page_bytes_including_header':MAX_PAGE,'max_unique_body_bytes':MAX_BODY,
        'body_bytes_included_once':total,'owners':{p:{'sha256':h} for p,h in PINS.items()},
        'ranges':RANGES,
        'pages':[{k:v for k,v in x.items() if k!='bytes'} for x in prepared],
    }
    manifest_bytes=(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n').encode()
    # All validation is complete; write a private sibling staging directory, verify it, then atomically publish.
    STAGE.mkdir()
    for item in prepared: (STAGE/item['name']).write_bytes(item['bytes'])
    (STAGE/'manifest.json').write_bytes(manifest_bytes)
    for item in prepared:
        actual=(STAGE/item['name']).read_bytes()
        if len(actual)!=item['emitted_bytes'] or sha(actual)!=item['page_sha256'] or actual!=item['bytes']:
            raise SystemExit(f'staging validation failed; private stage retained: {item["name"]}')
    if sha((STAGE/'manifest.json').read_bytes())!=sha(manifest_bytes): raise SystemExit('staging manifest mismatch; private stage retained')
    if OUT.exists(): raise SystemExit('destination appeared before publish; private stage retained')
    os.rename(STAGE,OUT)
    print(f'PUBLISHED={OUT} PAGES={len(prepared)} BODY_BYTES={total} MANIFEST_SHA256={sha(manifest_bytes)}')
    for item in prepared:
        print(f"{item['name']} {item['owner']} [{item['start_byte']},{item['end_byte']}) lines {item['start_line']}-{item['end_line']} kind={item['kind']} body={item['body_bytes']} emitted={item['emitted_bytes']} sha256={item['page_sha256']}")

def make_page(seq,spec,start_line,end_line,body,offsets):
    owner=spec['owner']; start_byte=offsets[start_line-1]; end_byte=offsets[end_line]
    header=(f"# source={owner} sha256={PINS[owner]} bytes=[{start_byte},{end_byte}) lines={start_line}-{end_line} kind={spec['kind']} name={spec['name']}\n").encode()
    page=header+body
    return {'name':f'page-{seq:03d}.txt','owner':owner,'owner_sha256':PINS[owner],'unit':spec['name'],'kind':spec['kind'],'start_byte':start_byte,'end_byte':end_byte,'start_line':start_line,'end_line':end_line,'body_bytes':len(body),'emitted_bytes':len(page),'page_sha256':sha(page),'complete_unit':spec['kind'] in {'unit','complete_arm_with_context'} and start_line==spec['start'] and end_line==spec['end'],'continuation':'next page continues same declared range' if end_line<spec['end'] else 'declared range complete','bytes':page}

if __name__=='__main__': main()
