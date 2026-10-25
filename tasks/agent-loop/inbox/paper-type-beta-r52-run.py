import sys,os,time,json,hashlib,subprocess,signal
from pathlib import Path
root=Path('/tmp/yulang-r52-type-beta'); out=root/'tasks/agent-loop/inbox'; p=root/'notes/theory/lean'; log=out/'paper-type-beta-r52-worker-log.json'; s=json.loads(log.read_text()); n=len(s['calls'])+1
assert n<=10
used=sum(c['duration_s'] for c in s['calls']); remaining=120-used; assert remaining>0
argv=[s['lake']]+sys.argv[1:]; start=time.monotonic_ns(); proc=subprocess.Popen(argv,cwd=p,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
timed=False
try: stdout,stderr=proc.communicate(timeout=remaining)
except subprocess.TimeoutExpired:
 timed=True;os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate()
end=time.monotonic_ns(); prefix=f'paper-type-beta-r52-call-{n:02}'
(out/(prefix+'.stdout')).write_bytes(stdout);(out/(prefix+'.stderr')).write_bytes(stderr)
entry={'n':n,'argv':argv,'cwd':str(p),'pid':proc.pid,'start_ns':start,'end_ns':end,'duration_s':(end-start)/1e9,'exit':proc.returncode,'timeout':timed,'stdout_sha256':hashlib.sha256(stdout).hexdigest(),'stderr_sha256':hashlib.sha256(stderr).hexdigest(),'process_waited':True}
s['calls'].append(entry);log.write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(entry));print(stdout.decode(),end='');print(stderr.decode(),end='',file=sys.stderr);sys.exit(proc.returncode)
